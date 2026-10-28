#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
PilasTube v3.5 - utils.py (shared foundation)

Everything every other module needs, in the exact original bootstrap order:
  logging (PLog -> LOG/SLOG, excepthook, atexit), XDG env fix, the SDL2
  import machinery with native-library retry, the guarded yt_extras import,
  themes, translations, shared constants (nav/category/wizard/quality),
  the VideoItem data model, format helpers, the WiFi helpers and the
  rasterised icon system.

This module is imported first by every other PilasTube module.
"""

import sys
import os
import time
import atexit
import traceback
import threading
import math

import json
import subprocess
import hashlib
import socket
import queue
import ctypes
import urllib.request
import ssl
from datetime import datetime


import yt_extras as YX

# NOTE: never `import platform` at module level here - `from sdl2 import *`
# re-exports sdl2.platform which would shadow the stdlib module.


def _py_version():
    return sys.version.split()[0] if sys.version.split() else "?"


# re-exports sdl2.platform which would shadow the stdlib module.


def _py_version():
    return sys.version.split()[0] if sys.version.split() else "?"


def _py_machine():
    try:
        import platform as _plat          # local import, no shadowing
        return _plat.machine()
    except Exception:
        return "?"


# ---------------------------------------------------------------------------
# Logging bootstrap - runs BEFORE anything else so that any later failure
# (SDL import, yt_extras import, init crash, ...) is captured on disk in
# logs/detailed.txt (technical) and logs/simple.txt (plain language).
# ---------------------------------------------------------------------------
SCRIPT_DIR = os.path.dirname(os.path.abspath(__file__))


sys.path.insert(0, SCRIPT_DIR)


LOG_DIR = os.path.join(SCRIPT_DIR, "logs")


LOG_DETAILED = os.path.join(LOG_DIR, "detailed.txt")


LOG_SIMPLE = os.path.join(LOG_DIR, "simple.txt")


_CRASHED = [False]


def _first_line(text):
    for part in str(text).splitlines():
        if part.strip():
            return part.strip()[:120]
    return "unknown error"


class PLog(object):
    """Two-file logger: detailed.txt (technical) + simple.txt (human)."""

    MAX_DETAILED = 400 * 1024
    MAX_SIMPLE = 100 * 1024

    def __init__(self, log_dir, detailed, simple):
        self.detailed_path = detailed
        self.simple_path = simple
        self._lock = threading.Lock()
        try:
            if not os.path.isdir(log_dir):
                os.makedirs(log_dir)
        except Exception:
            pass
        self._rotate(self.detailed_path, self.MAX_DETAILED)
        self._rotate(self.simple_path, self.MAX_SIMPLE)
        self.d("session begin - python %s on %s" %
               (_py_version(), _py_machine()))

    def _rotate(self, path, max_bytes):
        try:
            if os.path.exists(path) and os.path.getsize(path) > max_bytes:
                try:
                    os.remove(path + ".old")
                except Exception:
                    pass
                os.rename(path, path + ".old")
        except Exception:
            pass

    def _write(self, path, line):
        try:
            with open(path, "a", encoding="utf-8") as f:
                f.write(line + "\n")
        except Exception:
            pass

    def d(self, msg, comp="APP"):
        """Technical line -> detailed.txt"""
        line = "[%s] [%s] %s" % (time.strftime("%Y-%m-%d %H:%M:%S"), comp, msg)
        with self._lock:
            self._write(self.detailed_path, line)

    def s(self, msg):
        """Human line -> simple.txt (echoed into detailed.txt too)."""
        line = "[%s] %s" % (time.strftime("%Y-%m-%d %H:%M:%S"), msg)
        with self._lock:
            self._write(self.simple_path, line)
            self._write(self.detailed_path, "[%s] [SIMPLE] %s" %
                        (time.strftime("%Y-%m-%d %H:%M:%S"), msg))

    def crash(self, context, exc_info):
        """Exception record: full traceback in detailed, one line in simple."""
        _CRASHED[0] = True
        try:
            tb = "".join(traceback.format_exception(*exc_info)).rstrip()
        except Exception:
            tb = str(exc_info[1])
        stamp = time.strftime("%Y-%m-%d %H:%M:%S")
        with self._lock:
            self._write(self.detailed_path,
                        "[%s] [CRASH] %s\n%s" % (stamp, context, tb))
            self._write(self.simple_path,
                        "[%s] CRASH in %s: %s" %
                        (stamp, context, _first_line(exc_info[1])))


_PLOG = PLog(LOG_DIR, LOG_DETAILED, LOG_SIMPLE)


def LOG(msg, comp="APP"):
    _PLOG.d(msg, comp)


def SLOG(msg):
    _PLOG.s(msg)


def _excepthook(tp, val, tb):
    _PLOG.crash("uncaught exception", (tp, val, tb))
    sys.__excepthook__(tp, val, tb)


def _atexit_note():
    if _CRASHED[0]:
        SLOG("PilasTube closed after an error - see logs/detailed.txt")
    else:
        SLOG("PilasTube closed normally")


atexit.register(_atexit_note)


def run_logged_thread(name, target, args=(), daemon=True):
    """Thread wrapper: any exception inside a worker is logged, never silent."""
    def _worker():
        try:
            target(*args)
        except Exception:
            _PLOG.crash("thread '%s'" % name, sys.exc_info())
    th = threading.Thread(target=_worker, name="pt-" + name)
    th.daemon = daemon
    th.start()
    LOG("thread started: %s" % name, "THREAD")
    return th


try:
    _uid = os.getuid()
except Exception:
    _uid = -1


LOG("env: DISPLAY=%s WAYLAND_DISPLAY=%s" %
    (os.environ.get("DISPLAY", "<unset>"),
     os.environ.get("WAYLAND_DISPLAY", "<unset>")))


LOG("env: SDL_VIDEODRIVER=%s SDL_AUDIODRIVER=%s" %
    (os.environ.get("SDL_VIDEODRIVER", "<unset>"),
     os.environ.get("SDL_AUDIODRIVER", "<unset>")))


LOG("env: XDG_RUNTIME_DIR=%s" % os.environ.get("XDG_RUNTIME_DIR", "<unset>"))


LOG("env: PYSDL2_DLL_PATH=%s uid=%s" %
    (os.environ.get("PYSDL2_DLL_PATH", "<unset>"), _uid))


LOG("script_dir=%s" % SCRIPT_DIR)


SLOG("PilasTube starting (python %s)" % _py_version())


# ---------------------------------------------------------------------------
# SDL2 import with native-library path retry.
# The vendored PySDL2 wrapper loads native SDL2 / SDL2_ttf through ctypes
# at import time. If the first attempt fails we retry against common
# firmware library locations before giving up (logged at every step).
# ---------------------------------------------------------------------------
_SDL_LIB_CANDIDATES = [
    "",  # first attempt: whatever the launcher already configured
    os.path.join(SCRIPT_DIR, "libs"),
    "/opt/system/Tools/PortMaster/libs",
    "/opt/tools/PortMaster/libs",
    "/roms/ports/PortMaster/libs",
    "/usr/lib",
    "/usr/lib/aarch64-linux-gnu",
    "/usr/lib/arm-linux-gnueabihf",
    "/usr/lib/x86_64-linux-gnu",
    "/usr/local/lib",
]


SDL_IMPORT_ERROR = None


SDL_IMAGE_AVAILABLE = False


for _cand in _SDL_LIB_CANDIDATES:
    if _cand and not os.path.isdir(_cand):
        continue
    if _cand:
        os.environ["PYSDL2_DLL_PATH"] = _cand
        LOG("retrying SDL2 import with PYSDL2_DLL_PATH=%s" % _cand, "SDL")
    # purge any partially imported sdl2 modules before retrying
    for _m in [m for m in list(sys.modules)
               if m == "sdl2" or m.startswith("sdl2.")]:
        del sys.modules[_m]
    try:
        import sdl2
        import sdl2.ext
        import sdl2.sdlttf as ttf
        from sdl2 import *
        try:
            import sdl2.sdlimage as sdlimage
            SDL_IMAGE_AVAILABLE = True
        except (ImportError, OSError):
            SDL_IMAGE_AVAILABLE = False
        SDL_IMPORT_ERROR = None
        break
    except (ImportError, OSError) as _e:
        SDL_IMPORT_ERROR = str(_e)
        LOG("SDL2 import attempt failed: %s" % _e, "SDL")
        continue


if SDL_IMPORT_ERROR is not None:
    _CRASHED[0] = True
    LOG("FATAL: SDL2 stack could not be loaded: %s" % SDL_IMPORT_ERROR)
    SLOG("Failed to start: SDL2 libraries not found (%s)" %
         _first_line(SDL_IMPORT_ERROR))
    print("SDL2 Error: %s" % SDL_IMPORT_ERROR)
    sys.exit(1)


LOG("SDL2 python wrapper OK (pysdl2 %s)" %
    getattr(sdl2, "__version__", "?"), "SDL")


LOG("SDL_image available: %s" % SDL_IMAGE_AVAILABLE, "SDL")


# ---------------------------------------------------------------------------
# SDL2/SDL3 button-name compatibility (v2.2 crash fix)
# pysdl2 0.9.x follows SDL2 naming where the small centre button is BACK;
# SDL3 renamed it to SELECT. Older code paths referenced SELECT directly and
# crashed with NameError the moment any unhandled button event arrived
# (exactly what happened on device: "any button closes the app"). Define
# every missing alias here so no button code path can ever raise NameError.
# ---------------------------------------------------------------------------
SDL_CONTROLLER_BUTTON_SELECT = getattr(
    sdl2, "SDL_CONTROLLER_BUTTON_SELECT",
    getattr(sdl2, "SDL_CONTROLLER_BUTTON_BACK", 4))


SDL_CONTROLLER_BUTTON_START = getattr(
    sdl2, "SDL_CONTROLLER_BUTTON_START", 6)


def _sdl_err():
    """Current SDL error string (never raises)."""
    try:
        e = SDL_GetError()
        if e:
            return e.decode("utf-8", "replace")
    except Exception:
        pass
    return "unknown error"


LOG("yt_extras OK (version %s, xml=%s, concurrent=%s)" %
    (YX.APP_VERSION, getattr(YX, "HAS_ET", "?"),
     getattr(YX, "HAS_CONCURRENT", "?")))


# ----------------------------------------------------------------------------
# v0.3.8/0.3.9: device profile (device.txt) + ADAPTATIVE screen geometry.
#
# The app is not locked to 640x480: the window opens at the device's
# REAL native resolution and everything renders through a logical
# coordinate system derived from it (640x480 design grid -> scaled up, so
# 4:3 screens scale 1:1 in aspect, 16:9/1:1 screens get a wider/taller
# logical layout instead of letterbox bars). A human-readable,
# hand-editable device.txt is (re)written every boot:
#   - the AUTO block (detected values) is refreshed by the app
#   - the USER block (commented examples) is preserved verbatim
#
# v0.3.9 CRITICAL RULE (black-screen regression fix): this module must
# NEVER touch the SDL video subsystem at import time. v0.3.8 called
# SDL_Init(SDL_INIT_VIDEO) here to probe the desktop mode and, together
# with the v0.3.8 FULLSCREEN_DESKTOP window, that left several KMSDRM
# builds presenting a dead surface (app fully alive, panel black - the
# 0.3.8 field report on a 640x480 R36S-class device). SDL is now
# initialised exactly ONCE, inside PilasTubeApp.__init__, exactly like
# v0.3.7; the import-time probe reads the framebuffer sysfs instead, and
# the app calls utils.refresh_geometry() after SDL_Init if SDL knows
# better.
# ----------------------------------------------------------------------------
DEVICE_FILE = os.path.join(SCRIPT_DIR, "device.txt")

_USER_BLOCK_MARK = "# ---- user overrides"


def _probe_fb_size():
    """Framebuffer size via sysfs - launcher-era fallback.
    Knulli / Miyoo Flip fix: probe 'mode' before 'virtual_size'.
    On Rockchip fbdev with double/triple buffering, 'virtual_size' returns
    the multi-buffer height (e.g. 640,1440 for 3x 480 buffers), whereas 'mode'
    contains the actual physical panel resolution (e.g. U:640x480p-60)."""
    try:
        raw = open("/sys/class/graphics/fb0/mode").read().strip()
        # "U:640x480p-60" or "a:1024x768r-60" or "640x480" style
        if "x" in raw:
            body = raw.split(":")[-1].split("r")[0].split("p")[0]
            w, h = [int(v) for v in body.split("x")[:2]]
            if 320 <= w <= 4096 and 240 <= h <= 4096:
                return w, h
    except Exception:
        pass
    try:
        # Also check fb0/modes (first available mode)
        for line in open("/sys/class/graphics/fb0/modes"):
            line = line.strip()
            if "x" in line:
                body = line.split(":")[-1].split("r")[0].split("p")[0]
                w, h = [int(v) for v in body.split("x")[:2]]
                if 320 <= w <= 4096 and 240 <= h <= 4096:
                    return w, h
    except Exception:
        pass
    try:
        raw = open("/sys/class/graphics/fb0/virtual_size").read().strip()
        w, h = [int(v) for v in raw.split(",")]
        # On Miyoo Flip / RK3566 with 640x1440 (triple buffered 480p), normalize back to 480
        if w == 640 and h in (960, 1440):
            h = 480
        if 320 <= w <= 4096 and 240 <= h <= 4096:
            return w, h
    except Exception:
        pass
    return None


def _probe_device_name():
    for p in ("/sys/firmware/devicetree/base/model",):
        try:
            s = open(p, "rb").read(128).replace(b"\x00", b" ").decode(
                "utf-8", "replace").strip()
            if s:
                return s[:40]
        except Exception:
            pass
    env = os.environ.get("DEVICE") or os.environ.get("param_device")
    if env:
        return str(env)[:40]
    return "PortMaster handheld"


def _probe_firmware():
    try:
        for line in open("/etc/os-release"):
            if line.startswith("PRETTY_NAME="):
                return line.split("=", 1)[1].strip().strip('"')[:40]
    except Exception:
        pass
    return "unknown"


class DeviceProfile(object):
    """key=value parser/writer for device.txt (auto block + user block)."""

    @staticmethod
    def load(path):
        data = {}
        try:
            for line in open(path):
                line = line.strip()
                if not line or line.startswith("#") or "=" not in line:
                    continue
                k, v = line.split("=", 1)
                data[k.strip()] = v.strip()
        except Exception:
            pass
        return data

    @staticmethod
    def load_user(path):
        """key=value pairs from BELOW the user-override marker only.

        v0.3.9: the auto block's ui_scale line holds the COMPUTED value
        and must never be re-read as a user pin (feedback loop that
        froze the old scale after a resolution change). Only lines the
        user actually wrote in the override block count as overrides.
        """
        data = {}
        try:
            in_user = False
            for line in open(path):
                if line.startswith(_USER_BLOCK_MARK):
                    in_user = True
                    continue
                if not in_user:
                    continue
                line = line.strip()
                if not line or line.startswith("#") or "=" not in line:
                    continue
                k, v = line.split("=", 1)
                data[k.strip()] = v.strip()
        except Exception:
            pass
        return data

    @staticmethod
    def write(path, auto_fields, source="launcher"):
        """(Re)write device.txt: fresh auto block + template user block.

        Any user block from an existing file is preserved verbatim (the
        user may have uncommented/edited override lines by hand).
        """
        user_lines = []
        try:
            in_user = False
            for line in open(path):
                if line.startswith(_USER_BLOCK_MARK):
                    in_user = True
                if in_user:
                    user_lines.append(line.rstrip("\n"))
        except Exception:
            pass
        if not user_lines:
            user_lines = [
                _USER_BLOCK_MARK + " (uncomment a line to change it)",
                "#force_screen_width=640",
                "#force_screen_height=480",
                "#ui_scale=1.5",
                "#scale_mode=fit",
            ]
        lines = [
            "# ==========================================================",
            "#  PilasTube device profile (auto-generated)",
            "#",
            "#  AUTO BLOCK: detected values, refreshed at every boot.",
            "#  USER BLOCK (bottom): uncomment to override - examples:",
            "#    force_screen_width/height : window size (e.g. 640x480)",
            "#    ui_scale  : UI zoom (1.0 = design size; bigger = smaller",
            "#                UI on big screens; auto = fill the screen)",
            "#    scale_mode: fit  = keep proportions (default)",
            "#                fill = stretch the UI edge to edge",
            "# ==========================================================",
            "device_name=%s" % auto_fields.get("device_name", "?"),
            "firmware=%s" % auto_fields.get("firmware", "?"),
            "kernel=%s" % auto_fields.get("kernel", "?"),
            "cpu=%s" % auto_fields.get("cpu", "?"),
            "video_driver=%s" % auto_fields.get("video_driver", "?"),
            "native_width=%s" % auto_fields.get("native_width", 640),
            "native_height=%s" % auto_fields.get("native_height", 480),
            "ui_scale=%s" % auto_fields.get("ui_scale", 1.0),
            "screen_width=%s" % auto_fields.get("screen_width", 640),
            "screen_height=%s" % auto_fields.get("screen_height", 480),
            "scale_mode=%s" % auto_fields.get("scale_mode", "fit"),
            "source=%s" % source,
            "updated=%s" % time.strftime("%Y-%m-%d %H:%M:%S"),
            "",
        ] + user_lines + [""]
        try:
            tmp = path + ".tmp"
            with open(tmp, "w") as f:
                f.write("\n".join(lines) + "\n")
            os.replace(tmp, path)
        except Exception:
            try:
                with open(path, "w") as f:
                    f.write("\n".join(lines) + "\n")
            except Exception:
                pass


def _detect_native_size():
    """(w, h, source) - framebuffer sysfs, then 640x480 default.

    v0.3.9: NO SDL calls here (see the v0.3.9 rule in the header above).
    On PortMaster handhelds /sys/class/graphics/fb0 reports the true
    panel size; the launcher's device.txt writer uses the same probe.
    The test harness can override it with PT_MOCK_DISPLAY=WxH (the same
    variable mock_sdl2 understands, so the import-time probe and the
    mock's SDL_GetDesktopDisplayMode always agree).
    """
    try:
        _m = str(os.environ.get("PT_MOCK_DISPLAY", "")).lower()
        for _sep in ("x", ",", "*", " "):
            if _sep in _m:
                _parts = _m.split(_sep)
                _w, _h = int(_parts[0]), int(_parts[1])
                if 320 <= _w <= 4096 and 240 <= _h <= 4096:
                    return _w, _h, "mock"
    except Exception:
        pass
    fb = _probe_fb_size()
    if fb:
        return fb[0], fb[1], "fb"
    return 640, 480, "default"


# ---- geometry computation (shared by import time + v0.3.9 refresh) -----------
_GEO_ATTRS = ("NATIVE_WIDTH", "NATIVE_HEIGHT", "SCREEN_WIDTH",
              "SCREEN_HEIGHT", "WINDOW_WIDTH", "WINDOW_HEIGHT",
              "UI_SCALE", "SCALE_MODE", "FILL_SCALE_X", "FILL_SCALE_Y")


def _read_profile_overrides(profile, path=None):
    """(scale_mode, force_w, force_h, pinned_ui_scale) - device.txt user
    block values, all optional, all validated.

    v0.3.9: when device.txt carries the USER BLOCK marker (every file
    the app or launcher writes does), the ui_scale pin is honoured ONLY
    from below the marker - the auto block's ui_scale line is the
    computed value and re-reading it as a pin created a feedback loop
    that froze the old scale after refresh_geometry() corrected the
    resolution. Bare hand-made files without the marker still honour
    any line (v0.3.8 compatibility). scale_mode / force_* are safe to
    read flat (their auto-block values always equal the user's choice).
    """
    scale_mode = str(profile.get("scale_mode", "")).strip().lower()
    if scale_mode not in ("fit", "fill"):
        scale_mode = "fit"
    fw, fh = 0, 0
    try:
        fw = int(profile.get("force_screen_width", "0") or 0)
        fh = int(profile.get("force_screen_height", "0") or 0)
    except ValueError:
        fw, fh = 0, 0
    if not (320 <= fw <= 4096 and 240 <= fh <= 4096):
        fw, fh = 0, 0
    pinned = 0.0
    try:
        pinned = float(profile.get("ui_scale", "0") or 0)
    except ValueError:
        pinned = 0.0
    if path:
        try:
            with open(path) as _f:
                _raw = _f.read()
            if _USER_BLOCK_MARK in _raw:
                _ub = DeviceProfile.load_user(path)
                try:
                    pinned = float(_ub.get("ui_scale", "0") or 0)
                except ValueError:
                    pinned = 0.0
        except Exception:
            pass
    return scale_mode, fw, fh, pinned


def _compute_geometry(native_w, native_h, scale_mode, fw, fh, pinned):
    """The v0.3.8 adaptive rules (unchanged in v0.3.9).

    fit  -> logical = native / UI_SCALE, SAME aspect as the panel: 4:3
            screens render the 640x480 design grid exactly; 16:9 screens
            get a WIDER logical layout; 1:1 screens a TALLER one. No
            letterbox bars - the layout itself adapts.
    fill -> 640x480 stretched edge to edge (SDL_RenderSetScale).
    UI_SCALE = min(native/640, native/480) (>= 1.0), user-pinnable.
    """
    if fw and fh:
        # the user forced a window size (device.txt) - honour it
        native_w, native_h = fw, fh
    auto_scale = min(native_w / 640.0, native_h / 480.0)
    if auto_scale < 1.0:
        auto_scale = 1.0
    if not (1.0 <= pinned <= auto_scale):
        pinned = auto_scale
    ui_scale = pinned
    if scale_mode == "fill":
        # stretch the 640x480 design edge to edge (no bars, some
        # distortion)
        screen_w, screen_h = 640, 480
        fill_x = native_w / 640.0
        fill_y = native_h / 480.0
        ui_scale = min(fill_x, fill_y)
    else:
        screen_w = max(640, int(round(native_w / ui_scale)))
        screen_h = max(480, int(round(native_h / ui_scale)))
        fill_x = fill_y = None
    return {
        "native_w": int(native_w), "native_h": int(native_h),
        "screen_w": int(screen_w), "screen_h": int(screen_h),
        "window_w": int(native_w), "window_h": int(native_h),
        "ui_scale": float(ui_scale), "scale_mode": scale_mode,
        "fill_x": fill_x, "fill_y": fill_y,
    }


def _apply_geometry(geo):
    """Write a _compute_geometry() result into this module's globals AND
    the by-value copies already imported into ui/player/auth/PilasTube
    (those modules import the constants before the app exists - v0.3.9
    refreshes them in place so a late geometry correction propagates
    everywhere before the first frame is drawn)."""
    global NATIVE_WIDTH, NATIVE_HEIGHT, SCREEN_WIDTH, SCREEN_HEIGHT
    global WINDOW_WIDTH, WINDOW_HEIGHT, UI_SCALE, SCALE_MODE
    global FILL_SCALE_X, FILL_SCALE_Y
    NATIVE_WIDTH = geo["native_w"]
    NATIVE_HEIGHT = geo["native_h"]
    SCREEN_WIDTH = geo["screen_w"]
    SCREEN_HEIGHT = geo["screen_h"]
    WINDOW_WIDTH = geo["window_w"]
    WINDOW_HEIGHT = geo["window_h"]
    UI_SCALE = geo["ui_scale"]
    SCALE_MODE = geo["scale_mode"]
    FILL_SCALE_X = geo["fill_x"]
    FILL_SCALE_Y = geo["fill_y"]
    # Knulli / Miyoo Flip fix: PilasTube.py executes as '__main__'. Include '__main__'
    # so that module-level geometry constants in PilasTube.py are updated by refresh_geometry().
    for _mod_name in ("ui", "player", "auth", "PilasTube", "__main__"):
        _mod = sys.modules.get(_mod_name)
        if _mod is None:
            continue
        for _attr in _GEO_ATTRS:
            if hasattr(_mod, _attr):
                try:
                    setattr(_mod, _attr, globals()[_attr])
                except Exception:
                    pass


def _current_video_driver():
    """Name of the active SDL video driver ("" before SDL_Init - a pure
    query, never initialises anything)."""
    try:
        _vd = SDL_GetCurrentVideoDriver()
        if _vd:
            return _vd.decode("utf-8", "replace")
    except Exception:
        pass
    return ""


def refresh_geometry(sdl_w, sdl_h):
    """v0.3.9: re-probe the panel size AFTER the app initialised SDL.

    Called by PilasTubeApp.__init__ right after SDL_Init and BEFORE the
    window is created. If the SDL desktop mode disagrees with the
    import-time framebuffer probe (dev machines without fb0, exotic or
    rotated panels), the whole geometry is recomputed and pushed into
    every module + device.txt AUTO block. User overrides
    (force_screen_width/height, pinned ui_scale) are honoured exactly
    like at import time. Returns True when the geometry changed - on
    real handhelds the probes agree and this is a no-op.
    """
    try:
        sdl_w = int(sdl_w or 0)
        sdl_h = int(sdl_h or 0)
    except (TypeError, ValueError):
        return False
    if not (320 <= sdl_w <= 4096 and 240 <= sdl_h <= 4096):
        return False
    if sdl_w == NATIVE_WIDTH and sdl_h == NATIVE_HEIGHT:
        return False
    prof = DeviceProfile.load(DEVICE_FILE)
    scale_mode, fw, fh, pinned = _read_profile_overrides(prof, DEVICE_FILE)
    if fw and fh:
        # the user forced a window size - the SDL mode never wins
        return False
    geo = _compute_geometry(sdl_w, sdl_h, scale_mode, fw, fh, pinned)
    _apply_geometry(geo)
    try:
        DeviceProfile.write(DEVICE_FILE, {
            "device_name": _probe_device_name(),
            "firmware": _probe_firmware(),
            "kernel": os.uname().release if hasattr(os, "uname") else "?",
            "cpu": _py_machine(),
            "video_driver": _current_video_driver() or "sdl",
            "native_width": geo["native_w"],
            "native_height": geo["native_h"],
            "ui_scale": ("%.2f" % geo["ui_scale"]),
            "screen_width": geo["screen_w"],
            "screen_height": geo["screen_h"],
            "scale_mode": geo["scale_mode"],
        }, source="sdl")
    except Exception:
        pass
    LOG("geometry refreshed from SDL desktop mode: native=%dx%d "
        "logical=%dx%d scale=%.2f mode=%s window=%dx%d" %
        (geo["native_w"], geo["native_h"], geo["screen_w"], geo["screen_h"],
         geo["ui_scale"], geo["scale_mode"], geo["window_w"],
         geo["window_h"]), "SDL")
    return True


def apply_logical_mapping(renderer):
    """v0.3.9: map the logical coordinate grid onto the physical window.

    fit  -> SDL_RenderSetLogicalSize (aspect-preserving; logical and
            native share the aspect so there are no bars)
    fill -> SDL_RenderSetScale (stretch edge to edge)

    Applied ONLY when the logical grid actually differs from the window
    (fill mode, or a non-640x480-panel): 640x480 devices take the exact
    v0.3.7 render path (no logical-size call, no scale-quality hint) -
    the identity mapping is implicit. The linear-quality hint must be
    set before the first texture is created, which is why this runs
    right after renderer creation (and again after the player rebuilds
    the renderer around an external player). Returns True when a
    mapping was applied.
    """
    if not renderer:
        return False
    try:
        if (SCREEN_WIDTH == WINDOW_WIDTH and
                SCREEN_HEIGHT == WINDOW_HEIGHT and SCALE_MODE != "fill"):
            return False
        _set_hint = getattr(sdl2, "SDL_SetHint", None)
        if _set_hint:
            try:
                _set_hint(b"SDL_RENDER_SCALE_QUALITY", b"1")
            except Exception:
                pass
        if SCALE_MODE == "fill":
            _rss = getattr(sdl2, "SDL_RenderSetScale", None)
            if _rss and FILL_SCALE_X and FILL_SCALE_Y:
                _rss(renderer, FILL_SCALE_X, FILL_SCALE_Y)
                return True
        else:
            _rsl = getattr(sdl2, "SDL_RenderSetLogicalSize", None)
            if _rsl:
                _rsl(renderer, SCREEN_WIDTH, SCREEN_HEIGHT)
                return True
    except Exception:
        pass
    return False


# ---- compute the actual geometry for this boot (NO SDL - see header) ---------
_prof = DeviceProfile.load(DEVICE_FILE)

_scale_mode, _fw, _fh, _pinned = _read_profile_overrides(_prof, DEVICE_FILE)

NATIVE_WIDTH, NATIVE_HEIGHT, _geo_source = _detect_native_size()

_apply_geometry(_compute_geometry(NATIVE_WIDTH, NATIVE_HEIGHT,
                                  _scale_mode, _fw, _fh, _pinned))

_vid_drv = _current_video_driver()

LOG("geometry: native=%dx%d (%s) logical=%dx%d scale=%.2f mode=%s "
    "window=%dx%d" % (NATIVE_WIDTH, NATIVE_HEIGHT, _geo_source,
                      SCREEN_WIDTH, SCREEN_HEIGHT, UI_SCALE, SCALE_MODE,
                      WINDOW_WIDTH, WINDOW_HEIGHT), "SDL")

# refresh device.txt (auto block) every boot; preserve the user block
# v0.3.9: no SDL at import any more, so the video driver written here is
# the previous boot's value (or the probe source on a fresh install);
# utils.refresh_geometry() overwrites it with the real SDL driver name
# right after the app initialises SDL.
try:
    DeviceProfile.write(DEVICE_FILE, {
        "device_name": _probe_device_name(),
        "firmware": _probe_firmware(),
        "kernel": os.uname().release if hasattr(os, "uname") else "?",
        "cpu": _py_machine(),
        "video_driver": (_vid_drv or
                         str(_prof.get("video_driver", "") or "").strip() or
                         _geo_source),
        "native_width": NATIVE_WIDTH,
        "native_height": NATIVE_HEIGHT,
        "ui_scale": ("%.2f" % UI_SCALE),
        "screen_width": SCREEN_WIDTH,
        "screen_height": SCREEN_HEIGHT,
        "scale_mode": SCALE_MODE,
    }, source=_geo_source)
except Exception:
    pass


APP_TITLE = "PilasTube"


APP_VERSION = YX.APP_VERSION


# ----------------------------------------------------------------------------
# Themes
# ----------------------------------------------------------------------------
class Palette(object):
    def __init__(self, d):
        self.__dict__.update(d)


THEMES = {
    "Dark": Palette({
        "BG_PRIMARY": (15, 15, 15),
        "BG_SECONDARY": (25, 25, 25),
        "BG_TERTIARY": (35, 35, 35),
        "YT_RED": (255, 0, 0),
        "TEXT_PRIMARY": (255, 255, 255),
        "TEXT_SECONDARY": (170, 170, 170),
        "TEXT_TERTIARY": (100, 100, 100),
        "CARD_BG": (30, 30, 30),
        "CARD_SELECTED": (50, 50, 50),
        "NAV_BG": (20, 20, 20),
        "NAV_ACTIVE": (255, 255, 255),
        "NAV_INACTIVE": (100, 100, 100),
        "STATUS_LOADING": (255, 204, 0),
        "STATUS_ERROR": (255, 70, 70),
        "STATUS_SUCCESS": (70, 255, 70),
        "DIVIDER": (50, 50, 50),
        "THUMB_BG": (40, 40, 40),
        "PROGRESS_BG": (60, 60, 60),
        "BADGE_LIVE": (220, 30, 30),
        "BADGE_NEW": (255, 120, 0),
        "OVERLAY": (0, 0, 0, 235),
    }),
    "OLED": Palette({
        "BG_PRIMARY": (0, 0, 0),
        "BG_SECONDARY": (10, 10, 10),
        "BG_TERTIARY": (18, 18, 18),
        "YT_RED": (255, 0, 0),
        "TEXT_PRIMARY": (255, 255, 255),
        "TEXT_SECONDARY": (168, 168, 168),
        "TEXT_TERTIARY": (96, 96, 96),
        "CARD_BG": (12, 12, 12),
        "CARD_SELECTED": (34, 34, 34),
        "NAV_BG": (6, 6, 6),
        "NAV_ACTIVE": (255, 255, 255),
        "NAV_INACTIVE": (96, 96, 96),
        "STATUS_LOADING": (255, 204, 0),
        "STATUS_ERROR": (255, 70, 70),
        "STATUS_SUCCESS": (70, 255, 70),
        "DIVIDER": (26, 26, 26),
        "THUMB_BG": (20, 20, 20),
        "PROGRESS_BG": (50, 50, 50),
        "BADGE_LIVE": (220, 30, 30),
        "BADGE_NEW": (255, 120, 0),
        "OVERLAY": (0, 0, 0, 240),
    }),
}


# ----------------------------------------------------------------------------
# Translations  (English + Portugues fully updated for v2; other languages
# keep v1 strings and fall back to English for new features.)
# ----------------------------------------------------------------------------
TRANSLATIONS = {
    "English": {
        "nav_home": "Trending", "nav_subs": "Subs", "nav_search": "Search",
        "nav_favorites": "Favs", "nav_history": "History", "nav_settings": "Settings",
        "nav_recommended": "For You", "nav_categories": "Categories",
        "cat_trending": "Trending", "cat_music": "Music", "cat_gaming": "Gaming",
        "cat_live": "Live", "cat_movies": "Movies", "cat_news": "News",
        "cat_sports": "Sports", "cat_learning": "Learning",
        "cat_podcasts": "Podcasts", "cat_favorites": "Favorites",
        "msg_select_category": "Choose a category",
        "msg_cat_empty": "No videos in this category yet",
        "settings_title": "Settings",
        "sec_general": "GENERAL", "sec_playback": "PLAYBACK",
        "sec_sponsorblock": "SPONSORBLOCK & EXTRAS", "sec_content": "CONTENT FILTERS",
        "sec_network": "NETWORK / ROUTE", "sec_data": "DATA",
        "settings_language": "Language", "settings_theme": "Theme",
        "settings_search_count": "Results per Page", "settings_auto_load": "Auto Load Home",
        "settings_quality": "Video Quality", "settings_hwdec": "HW Decoding",
        "settings_codec": "Video Codec", "settings_route": "Network Route",
        "settings_seek_interval": "Seek Step (L/R)", "settings_playback_mode": "Playback Mode",
        "settings_speed_memory": "Remember Speed", "settings_subtitles": "Subtitles",
        "settings_sleep_timer": "Sleep Timer", "settings_volume_boost": "Volume Boost",
        "settings_sponsorblock": "SponsorBlock", "settings_dearrow": "DeArrow Titles",
        "settings_ryd": "Dislike Counts", "settings_suggestions": "Search Suggestions",
        "settings_hide_shorts": "Hide Shorts", "settings_hide_live": "Hide Live",
        "settings_hide_watched": "Hide Watched",
        "settings_proxy": "Proxy URL", "settings_prefer_ipv4": "Prefer IPv4",
        "settings_player_client": "YT Client", "settings_socket_timeout": "Socket Timeout",
        "settings_ytdlp_update": "Update yt-dlp Now", "settings_ytdlp_ver": "yt-dlp Version",
        "settings_clear_favorites": "Clear Favorites", "settings_clear_history": "Clear History",
        "settings_clear_cache": "Clear Thumb Cache", "settings_clear_positions": "Clear Positions",
        "settings_clear_searches": "Clear Search History", "settings_clear_blocked": "Clear Blocked Channels",
        "settings_reset": "Reset All Preferences", "settings_execute": "[A] Execute",
        "settings_edit": "[A] Edit", "settings_on": "On", "settings_off": "Off",
        "settings_min": "min",
        "msg_searching": "Searching videos...", "msg_loading": "Loading...",
        "msg_loading_video": "Loading Video...", "msg_loading_videos": "Loading videos...",
        "msg_resuming": "Resuming from", "msg_no_results": "No results",
        "msg_press_search": "Press X to search", "msg_no_ytdlp": "yt-dlp not found!",
        "msg_no_player": "No video player!", "msg_install_ytdlp": "Install: pip install yt-dlp",
        "msg_install_player": "Install: mpv or ffplay", "msg_timeout": "Timeout",
        "msg_added_fav": "Added to favorites", "msg_removed_fav": "Removed from favorites",
        "msg_fav_cleared": "Favorites cleared", "msg_history_cleared": "History cleared",
        "msg_cache_cleared": "Cache cleared", "msg_videos": "videos",
        "msg_positions_cleared": "Positions cleared", "msg_searches_cleared": "Search history cleared",
        "msg_blocked_cleared": "Blocked channels cleared", "msg_prefs_reset": "Preferences reset",
        "msg_subscribed": "Subscribed!", "msg_unsubscribed": "Unsubscribed",
        "msg_blocked": "Channel blocked", "msg_unblocked": "Channel unblocked",
        "msg_queue_added": "Added to queue", "msg_queue_next": "Playing next",
        "msg_play_all": "Playing rest of list", "msg_no_channel": "No channel info",
        "msg_skipped": "Skipped", "msg_next": "Up next",
        "msg_updating": "Updating yt-dlp...", "msg_update_ok": "yt-dlp updated",
        "update_title": "yt-dlp update available",
        "update_current": "Current version",
        "update_latest": "Latest version",
        "update_ask": "Update now?",
        "update_yes": "Yes - update now", "update_no": "No - skip",
        "update_skipped": "Update skipped (Settings > Network anytime)",
        "update_offline": "Update check skipped (offline)",
        "msg_sb_off": "SponsorBlock off", "msg_empty_subs": "No subscriptions yet",
        "msg_subs_hint": "Open a video > START > Subscribe",
        "help_keyboard": "A:Type  B:Close  SUG:Tips  START:Search  Y:Del",
        "help_main": "A:Select  X:Search  Y:Fav  L2/R2:Sections  START+SELECT:Exit",
        "help_ctx": "A:OK  B:Close", "help_queue": "A:Play  Y:Remove  B:Back",
        "kb_space": "SPACE", "kb_go": "GO", "kb_sym": "SYM", "kb_abc": "abc",
        "kb_search_placeholder": "Type to search...", "kb_proxy_placeholder": "Proxy URL (empty=direct)",
        "time_today": "Today", "time_live": "LIVE", "badge_new": "NEW",
        "ctx_title": "Video Menu", "ctx_play": "Play", "ctx_resume": "Resume from",
        "ctx_beginning": "Play from beginning", "ctx_queue_add": "Add to Queue",
        "ctx_queue_next": "Play Next", "ctx_play_all": "Play All From Here",
        "ctx_channel": "Go to Channel", "ctx_subscribe": "Subscribe to Channel",
        "ctx_unsubscribe": "Unsubscribe", "ctx_block": "Block Channel",
        "ctx_unblock": "Unblock Channel", "ctx_info": "Video Info",
        "ctx_remove_history": "Remove from History",
        "queue_title": "Playback Queue", "queue_empty": "Queue is empty",
        "channel_title": "Channel", "sugg_title": "Suggestions",
        "sugg_hist": "Recent Searches",
        "wiz_welcome": "Welcome! First-time setup",
        "wiz_welcome_sub": "A few questions to fit the app to your device",
        "wiz_language": "Language / Idioma", "wiz_device": "Your Device",
        "wiz_quality": "Default Video Quality", "wiz_hwdec": "Hardware Video Decoding",
        "wiz_sb": "SponsorBlock (auto-skip sponsor segments)",
        "wiz_done": "Setup complete!",
        "wiz_done_sub": "You can change everything later in Settings",
        "wiz_hint": "D-pad: choose   A: next   B: back",
        "wiz_finish": "Start using PilasTube",
        "msg_exit_hint": "To exit press START + SELECT",
        "msg_feed_failed": "Couldn't load videos",
        "msg_retry": "[A] Try again",
        "msg_no_internet": "No internet connection",
        "msg_err_ignored": "Error ignored - see logs",
        "msg_cached": "cached",
        # ---- v3.6 network watchdog / pages / audio language ----
        "msg_reconnecting": "Reconnecting to WiFi...",
        "msg_back_online": "Connection restored",
        "msg_net_attempts": "Attempt %s",
        "msg_page": "Page",
        "msg_end_results": "No more results",
        "settings_audio_lang": "Audio language",
        "player_audio_lang": "Audio",
        "player_audio_single": "Single audio track",
        "kb_sug": "SUG",
        # ---- v3.0 built-in player (SmartTube-style HUD) ----
        "player_pause": "Pause", "player_play": "Play",
        "player_prev": "Prev", "player_next": "Next",
        "player_quality": "Quality", "player_speed": "Speed",
        "player_codec": "Codec",
        "player_captions": "Captions", "player_loop": "Loop",
        "player_volume": "Volume", "player_stats": "Stats for nerds",
        "player_chapters": "Chapters", "player_options": "Options",
        "player_no_chapters": "No chapters",
        "player_no_next": "No next video",
        "player_open_channel": "Open channel",
        "player_buffering": "Buffering...",
        "player_seeking": "Seeking...",
        "player_next_in": "Up next in",
        "player_countdown_hint": "A: play now   B: cancel",
        "player_sleep_stop": "Sleep timer - stopping",
        "player_hint": "A:pause  B:exit  </>:seek  v:controls  START:options",
        "player_hint_ui": "</>: move  A: select  B: close  v: hide",
        "player_cc_off": "Off", "player_cc_none": "No captions",
        "player_showtime_menu": "Show time / position",
        "player_stat_res": "Resolution", "player_stat_shown": "Frames shown",
        "player_stat_dropped": "Dropped", "player_stat_buffer": "Buffer",
        "loop_off": "Loop off",
        # ---- v3.3 account login + live playback ----
        "sec_account": "ACCOUNT", "sec_audio": "AUDIO & SUBTITLES",
        "settings_login": "Sign in to YouTube",
        "settings_logout": "Sign out",
        "settings_signed_in_as": "Signed in as",
        "settings_not_signed_in": "Not signed in",
        "settings_pick": "Choose",
        "settings_pick_hint": "A:OK   B:Cancel",
        "login_title": "Sign in to YouTube",
        "login_open": "On your phone or PC, open",
        "login_enter": "and enter this code",
        "login_waiting": "Waiting for sign-in...",
        "login_success": "Signed in as %s",
        "login_failed": "Sign-in failed",
        "login_denied": "Sign-in denied",
        "login_expired": "Code expired - try again",
        "login_cancel_hint": "B: Cancel",
        "msg_live_no_seek": "Live streams can't seek",
        "history_source_yt": "YouTube", "history_source_local": "Device",
        "subs_account": "Account",
        "msg_account_feed_fail": "Account feed unavailable",
    },
    "Portugues": {
        "nav_home": "Em Alta", "nav_subs": "Insc.", "nav_search": "Buscar",
        "nav_favorites": "Favs", "nav_history": "Historico", "nav_settings": "Config",
        "nav_recommended": "Recomendados", "nav_categories": "Categorias",
        "cat_trending": "Em Alta", "cat_music": "Musica", "cat_gaming": "Jogos",
        "cat_live": "Ao Vivo", "cat_movies": "Filmes", "cat_news": "Noticias",
        "cat_sports": "Esportes", "cat_learning": "Aprender",
        "cat_podcasts": "Podcasts", "cat_favorites": "Favoritos",
        "msg_select_category": "Escolha uma categoria",
        "msg_cat_empty": "Nenhum video nesta categoria ainda",
        "settings_title": "Configuracoes",
        "sec_general": "GERAL", "sec_playback": "REPRODUCAO",
        "sec_sponsorblock": "SPONSORBLOCK E EXTRAS", "sec_content": "FILTROS DE CONTEUDO",
        "sec_network": "REDE / ROTA", "sec_data": "DADOS",
        "settings_language": "Idioma", "settings_theme": "Tema",
        "settings_search_count": "Resultados por Pagina", "settings_auto_load": "Carregar Inicio",
        "settings_quality": "Qualidade de Video", "settings_hwdec": "Decod. Hardware",
        "settings_codec": "Codec de Video", "settings_route": "Rota de Rede",
        "settings_seek_interval": "Salto (L/R)", "settings_playback_mode": "Modo de Reproducao",
        "settings_speed_memory": "Lembrar Velocidade", "settings_subtitles": "Legendas",
        "settings_sleep_timer": "Timer de Sono", "settings_volume_boost": "Volume Turbo",
        "settings_sponsorblock": "SponsorBlock", "settings_dearrow": "Titulos DeArrow",
        "settings_ryd": "Contar Dislikes", "settings_suggestions": "Sugestoes de Busca",
        "settings_hide_shorts": "Ocultar Shorts", "settings_hide_live": "Ocultar Ao Vivo",
        "settings_hide_watched": "Ocultar Assistidos",
        "settings_proxy": "URL do Proxy", "settings_prefer_ipv4": "Preferir IPv4",
        "settings_player_client": "Cliente YT", "settings_socket_timeout": "Timeout de Rede",
        "settings_ytdlp_update": "Atualizar yt-dlp Agora", "settings_ytdlp_ver": "Versao do yt-dlp",
        "settings_clear_favorites": "Limpar Favoritos", "settings_clear_history": "Limpar Historico",
        "settings_clear_cache": "Limpar Cache Miniaturas", "settings_clear_positions": "Limpar Posicoes",
        "settings_clear_searches": "Limpar Buscas", "settings_clear_blocked": "Limpar Canais Bloqueados",
        "settings_reset": "Resetar Preferencias", "settings_execute": "[A] Executar",
        "settings_edit": "[A] Editar", "settings_on": "Ligado", "settings_off": "Desligado",
        "settings_min": "min",
        "msg_searching": "Buscando videos...", "msg_loading": "Carregando...",
        "msg_loading_video": "Carregando Video...", "msg_loading_videos": "Carregando videos...",
        "msg_resuming": "Continuando de", "msg_no_results": "Sem resultados",
        "msg_press_search": "Aperte X para buscar", "msg_no_ytdlp": "yt-dlp nao encontrado!",
        "msg_no_player": "Sem player de video!", "msg_install_ytdlp": "Instale: pip install yt-dlp",
        "msg_install_player": "Instale: mpv ou ffplay", "msg_timeout": "Tempo esgotado",
        "msg_added_fav": "Adicionado aos favoritos", "msg_removed_fav": "Removido dos favoritos",
        "msg_fav_cleared": "Favoritos limpos", "msg_history_cleared": "Historico limpo",
        "msg_cache_cleared": "Cache limpo", "msg_videos": "videos",
        "msg_positions_cleared": "Posicoes limpas", "msg_searches_cleared": "Buscas limpas",
        "msg_blocked_cleared": "Canais desbloqueados", "msg_prefs_reset": "Preferencias resetadas",
        "msg_subscribed": "Inscrito!", "msg_unsubscribed": "Inscricao removida",
        "msg_blocked": "Canal bloqueado", "msg_unblocked": "Canal desbloqueado",
        "msg_queue_added": "Adicionado a fila", "msg_queue_next": "Tocando apos atual",
        "msg_play_all": "Tocando resto da lista", "msg_no_channel": "Sem info do canal",
        "msg_skipped": "Pulado", "msg_next": "A seguir",
        "msg_updating": "Atualizando yt-dlp...", "msg_update_ok": "yt-dlp atualizado",
        "update_title": "Atualizacao do yt-dlp disponivel",
        "update_current": "Versao atual",
        "update_latest": "Versao nova",
        "update_ask": "Atualizar agora?",
        "update_yes": "Sim - atualizar agora", "update_no": "Nao - pular",
        "update_skipped": "Atualizacao pulada (Config > Rede a qualquer hora)",
        "update_offline": "Verificacao pulada (sem conexao)",
        "msg_sb_off": "SponsorBlock desligado", "msg_empty_subs": "Sem inscricoes ainda",
        "msg_subs_hint": "Abra um video > START > Inscrever",
        "help_keyboard": "A:Digitar  B:Fechar  SUG:Dicas  START:Buscar  Y:Apagar",
        "help_main": "A:Escolher  X:Buscar  Y:Fav  L2/R2:Secoes  START+SELECT:Sair",
        "help_ctx": "A:OK  B:Fechar", "help_queue": "A:Tocar  Y:Remover  B:Voltar",
        "kb_space": "ESPACO", "kb_go": "IR", "kb_sym": "SIMB", "kb_abc": "abc",
        "kb_search_placeholder": "Digite para buscar...", "kb_proxy_placeholder": "URL do Proxy (vazio=direto)",
        "time_today": "Hoje", "time_live": "AO VIVO", "badge_new": "NOVO",
        "ctx_title": "Menu do Video", "ctx_play": "Assistir", "ctx_resume": "Continuar de",
        "ctx_beginning": "Assistir do comeco", "ctx_queue_add": "Add a Fila",
        "ctx_queue_next": "Tocar Proximo", "ctx_play_all": "Tocar Tudo Daqui",
        "ctx_channel": "Ir ao Canal", "ctx_subscribe": "Inscrever no Canal",
        "ctx_unsubscribe": "Cancelar Inscricao", "ctx_block": "Bloquear Canal",
        "ctx_unblock": "Desbloquear Canal", "ctx_info": "Info do Video",
        "ctx_remove_history": "Remover do Historico",
        "queue_title": "Fila de Reproducao", "queue_empty": "Fila vazia",
        "channel_title": "Canal", "sugg_title": "Sugestoes",
        "sugg_hist": "Buscas Recentes",
        "wiz_welcome": "Bem-vindo! Configuracao inicial",
        "wiz_welcome_sub": "Algumas perguntas para ajustar ao seu aparelho",
        "wiz_language": "Idioma / Language", "wiz_device": "Seu Aparelho",
        "wiz_quality": "Qualidade Padrao", "wiz_hwdec": "Decodificacao por Hardware",
        "wiz_sb": "SponsorBlock (pular patrocinios)",
        "wiz_done": "Configuracao concluida!",
        "wiz_done_sub": "Tudo pode mudar depois nas Configuracoes",
        "wiz_hint": "Direcional: escolher   A: proximo   B: voltar",
        "wiz_finish": "Comecar a usar o PilasTube",
        "msg_exit_hint": "Para sair aperte START + SELECT",
        "msg_feed_failed": "Nao foi possivel carregar videos",
        "msg_retry": "[A] Tentar de novo",
        "msg_no_internet": "Sem conexao com a internet",
        "msg_err_ignored": "Erro ignorado - veja logs",
        "msg_cached": "cache",
        # ---- v3.6 watchdog de rede / paginas / idioma do audio ----
        "msg_reconnecting": "Reconectando ao WiFi...",
        "msg_back_online": "Conexao restabelecida",
        "msg_net_attempts": "Tentativa %s",
        "msg_page": "Pagina",
        "msg_end_results": "Fim dos resultados",
        "settings_audio_lang": "Idioma do audio",
        "player_audio_lang": "Audio",
        "player_audio_single": "Audio unico",
        "kb_sug": "SUG",
        # ---- v3.0 built-in player (SmartTube-style HUD) ----
        "player_pause": "Pausar", "player_play": "Tocar",
        "player_prev": "Anterior", "player_next": "Proximo",
        "player_quality": "Qualidade", "player_speed": "Velocidade",
        "player_codec": "Codec",
        "player_captions": "Legendas", "player_loop": "Repetir",
        "player_volume": "Volume", "player_stats": "Estatisticas",
        "player_chapters": "Capitulos", "player_options": "Opcoes",
        "player_no_chapters": "Sem capitulos",
        "player_no_next": "Sem proximo video",
        "player_open_channel": "Abrir canal",
        "player_buffering": "Carregando...",
        "player_seeking": "Pulando...",
        "player_next_in": "A seguir em",
        "player_countdown_hint": "A: tocar agora   B: cancelar",
        "player_sleep_stop": "Timer de sono - parando",
        "player_hint": "A:pausa  B:sair  </>:salto  v:menu  START:opcoes",
        "player_hint_ui": "</>: mover  A: selecionar  B: fechar  v: esconder",
        "player_cc_off": "Desligado", "player_cc_none": "Sem legendas",
        "player_showtime_menu": "Mostrar tempo / posicao",
        "player_stat_res": "Resolucao", "player_stat_shown": "Quadros exibidos",
        "player_stat_dropped": "Perdidos", "player_stat_buffer": "Buffer",
        "loop_off": "Repetir desligado",
        # ---- v3.3 conta + lives ----
        "sec_account": "CONTA", "sec_audio": "AUDIO E LEGENDAS",
        "settings_login": "Entrar no YouTube",
        "settings_logout": "Sair da conta",
        "settings_signed_in_as": "Conectado como",
        "settings_not_signed_in": "Nao conectado",
        "settings_pick": "Escolher",
        "settings_pick_hint": "A:OK   B:Cancelar",
        "login_title": "Entrar no YouTube",
        "login_open": "No seu celular ou PC, acesse",
        "login_enter": "e digite este codigo",
        "login_waiting": "Aguardando login...",
        "login_success": "Conectado como %s",
        "login_failed": "Falha no login",
        "login_denied": "Login negado",
        "login_expired": "Codigo expirou - tente de novo",
        "login_cancel_hint": "B: Cancelar",
        "msg_live_no_seek": "Lives nao permitem avancar",
        "history_source_yt": "YouTube", "history_source_local": "Aparelho",
        "subs_account": "Conta",
        "msg_account_feed_fail": "Feed da conta indisponivel",
    },
    "Turkce": {
        "nav_home": "Ana", "nav_search": "Ara", "nav_favorites": "Fav",
        "nav_history": "Gecmis", "nav_settings": "Ayarlar",
        "nav_recommended": "Onerilen", "nav_categories": "Kategoriler",
        "settings_title": "Ayarlar", "settings_language": "Dil",
        "settings_quality": "Video Kalitesi", "settings_search_count": "Arama Sayisi",
        "settings_codec": "Video Codec", "settings_route": "Ag Rotasi", "player_codec": "Codec",
        "settings_auto_load": "Otomatik Yukle", "settings_clear_favorites": "Favorileri Temizle",
        "settings_clear_history": "Gecmisi Temizle", "settings_clear_cache": "Onbellek Temizle",
        "settings_execute": "[A] Calistir", "settings_on": "Acik", "settings_off": "Kapali",
        "msg_searching": "Videolar araniyor...", "msg_loading": "Yukleniyor...",
        "msg_loading_video": "Video Yukleniyor...", "msg_loading_videos": "Videolar yukleniyor...",
        "msg_no_results": "Sonuc yok", "msg_press_search": "Aramak icin X'e bas",
        "msg_no_ytdlp": "yt-dlp bulunamadi!", "msg_no_player": "Video oynatici yok!",
        "msg_install_ytdlp": "Kur: pip install yt-dlp", "msg_install_player": "Kur: mpv veya ffplay",
        "msg_timeout": "Zaman asimi", "msg_added_fav": "Favorilere eklendi",
        "msg_removed_fav": "Favorilerden cikarildi", "msg_fav_cleared": "Favoriler temizlendi",
        "msg_history_cleared": "Gecmis temizlendi", "msg_cache_cleared": "Onbellek temizlendi",
        "msg_videos": "video", "help_keyboard": "A:Yaz  B:Kapat  START:Ara",
        "help_main": "A:Sec  B:Geri  X:Ara  Y:Fav  L/R:Sekme",
        "kb_space": "BOSLUK", "kb_go": "GIT",
        "kb_search_placeholder": "Aramak icin yaz...",
        "time_today": "Bugun", "time_live": "CANLI",
    },
    "Espanol": {
        "nav_home": "Inicio", "nav_search": "Buscar", "nav_favorites": "Favs",
        "nav_history": "Historial", "nav_settings": "Ajustes",
        "nav_recommended": "Recomendados", "nav_categories": "Categorias",
        "cat_trending": "Tendencias", "cat_music": "Musica", "cat_gaming": "Juegos",
        "cat_live": "En Vivo", "cat_movies": "Peliculas", "cat_news": "Noticias",
        "cat_sports": "Deportes", "cat_learning": "Aprender",
        "cat_podcasts": "Podcasts", "cat_favorites": "Favoritos",
        "msg_select_category": "Elige una categoria",
        "msg_cat_empty": "Aun no hay videos en esta categoria",
        "settings_title": "Ajustes", "settings_language": "Idioma",
        "settings_quality": "Calidad de Video", "settings_search_count": "Num. Busqueda",
        "settings_codec": "Codec de Video", "settings_route": "Ruta de Red", "player_codec": "Codec",
        "settings_auto_load": "Carga Auto", "settings_clear_favorites": "Borrar Favoritos",
        "settings_clear_history": "Borrar Historial", "settings_clear_cache": "Borrar Cache",
        "settings_execute": "[A] Ejecutar", "settings_on": "Si", "settings_off": "No",
        "msg_searching": "Buscando videos...", "msg_loading": "Cargando...",
        "msg_loading_video": "Cargando Video...", "msg_loading_videos": "Cargando videos...",
        "msg_no_results": "Sin resultados", "msg_press_search": "Pulsa X para buscar",
        "msg_no_ytdlp": "yt-dlp no encontrado!", "msg_no_player": "Sin reproductor!",
        "msg_install_ytdlp": "Instalar: pip install yt-dlp", "msg_install_player": "Instalar: mpv o ffplay",
        "msg_timeout": "Tiempo agotado", "msg_added_fav": "Anadido a favoritos",
        "msg_removed_fav": "Quitado de favoritos", "msg_fav_cleared": "Favoritos borrados",
        "msg_history_cleared": "Historial borrado", "msg_cache_cleared": "Cache borrado",
        "msg_videos": "videos", "help_keyboard": "A:Escribir  B:Cerrar  START:Buscar",
        "help_main": "A:Elegir  B:Atras  X:Buscar  Y:Fav  L/R:Pestana",
        "kb_space": "ESPACIO", "kb_go": "IR",
        "kb_search_placeholder": "Escribe para buscar...",
        "time_today": "Hoy", "time_live": "EN VIVO",
    },
    "Deutsch": {
        "nav_home": "Start", "nav_search": "Suche", "nav_favorites": "Favs",
        "nav_history": "Verlauf", "nav_settings": "Einst.",
        "nav_recommended": "Fur Dich", "nav_categories": "Kategorien",
        "settings_title": "Einstellungen", "settings_language": "Sprache",
        "settings_quality": "Videoqualitat", "settings_search_count": "Suchanzahl",
        "settings_codec": "Video-Codec", "settings_route": "Netzwerk-Route", "player_codec": "Codec",
        "settings_auto_load": "Auto Laden", "settings_clear_favorites": "Favoriten loschen",
        "settings_clear_history": "Verlauf loschen", "settings_clear_cache": "Cache loschen",
        "settings_execute": "[A] Ausfuhren", "settings_on": "An", "settings_off": "Aus",
        "msg_searching": "Videos suchen...", "msg_loading": "Laden...",
        "msg_loading_video": "Video laden...", "msg_loading_videos": "Videos laden...",
        "msg_no_results": "Keine Ergebnisse", "msg_press_search": "X fur Suche drucken",
        "msg_no_ytdlp": "yt-dlp nicht gefunden!", "msg_no_player": "Kein Videoplayer!",
        "msg_install_ytdlp": "Installieren: pip install yt-dlp", "msg_install_player": "Installieren: mpv oder ffplay",
        "msg_timeout": "Zeituberschreitung", "msg_added_fav": "Zu Favoriten hinzugefugt",
        "msg_removed_fav": "Aus Favoriten entfernt", "msg_fav_cleared": "Favoriten geloscht",
        "msg_history_cleared": "Verlauf geloscht", "msg_cache_cleared": "Cache geloscht",
        "msg_videos": "Videos", "help_keyboard": "A:Tippen  B:Schliessen  START:Suchen",
        "help_main": "A:Wahlen  B:Zuruck  X:Suchen  Y:Fav  L/R:Tab",
        "kb_space": "LEER", "kb_go": "LOS",
        "kb_search_placeholder": "Zum Suchen tippen...",
        "time_today": "Heute", "time_live": "LIVE",
    },
    "Francais": {
        "nav_home": "Accueil", "nav_search": "Chercher", "nav_favorites": "Favs",
        "nav_history": "Historique", "nav_settings": "Params",
        "nav_recommended": "Pour Vous", "nav_categories": "Categories",
        "settings_title": "Parametres", "settings_language": "Langue",
        "settings_quality": "Qualite Video", "settings_search_count": "Nb. Recherche",
        "settings_codec": "Codec Video", "settings_route": "Route Reseau", "player_codec": "Codec",
        "settings_auto_load": "Charg. Auto", "settings_clear_favorites": "Effacer Favoris",
        "settings_clear_history": "Effacer Historique", "settings_clear_cache": "Effacer Cache",
        "settings_execute": "[A] Executer", "settings_on": "Oui", "settings_off": "Non",
        "msg_searching": "Recherche videos...", "msg_loading": "Chargement...",
        "msg_loading_video": "Chargement Video...", "msg_loading_videos": "Chargement videos...",
        "msg_no_results": "Aucun resultat", "msg_press_search": "Appuyez X pour chercher",
        "msg_no_ytdlp": "yt-dlp non trouve!", "msg_no_player": "Pas de lecteur!",
        "msg_install_ytdlp": "Installer: pip install yt-dlp", "msg_install_player": "Installer: mpv ou ffplay",
        "msg_timeout": "Delai depasse", "msg_added_fav": "Ajoute aux favoris",
        "msg_removed_fav": "Retire des favoris", "msg_fav_cleared": "Favoris effaces",
        "msg_history_cleared": "Historique efface", "msg_cache_cleared": "Cache efface",
        "msg_videos": "videos", "help_keyboard": "A:Taper  B:Fermer  START:Chercher",
        "help_main": "A:Choisir  B:Retour  X:Chercher  Y:Fav  L/R:Onglet",
        "kb_space": "ESPACE", "kb_go": "ALLER",
        "kb_search_placeholder": "Tapez pour chercher...",
        "time_today": "Aujourd'hui", "time_live": "DIRECT",
    },
}


LANGUAGES = ["English", "Portugues", "Turkce", "Espanol", "Deutsch", "Francais"]


NAV_HOME = 0


NAV_SUBS = 1


NAV_SEARCH = 2


NAV_CATEGORIES = 3


NAV_HISTORY = 4


NAV_SETTINGS = 5


NAV_COUNT = 6


# v3.4 legacy alias for old tests (value unchanged: the 4th tab)
NAV_FAVORITES = NAV_CATEGORIES


SPEED_STEPS = [0.5, 0.75, 1.0, 1.25, 1.5, 1.75, 2.0]


QUALITY_OPTIONS = ["Auto", "240p", "360p", "480p", "720p"]


# v3.4 Categories tab (SmartTube "Explore"-style). Each entry:
#   (key, icon-name, feed-source-kind)
# Sources: "trending" = Piped/Invidious region trending; "charts" = the
# official Top-100 music playlist; "search" = yt-dlp search with a
# server-side filter token (most-viewed or live - see YX.category_search_url);
# "favorites" = the local favorites list.
CATEGORY_DEFS = [
    ("trending", "cat_flame", "trending"),
    ("music", "cat_note", "charts"),
    ("gaming", "cat_pad", "search"),
    ("live", "cat_live", "search"),
    ("movies", "cat_film", "search"),
    ("news", "cat_news", "search"),
    ("sports", "cat_ball", "search"),
    ("learning", "cat_book", "search"),
    ("podcasts", "cat_mic", "search"),
    ("favorites", "cat_heart", "favorites"),
]


# subtitle language codes -> display names
LANG_NAMES = {
    "en": "English", "pt": "Portugues", "pt-BR": "Portugues (BR)",
    "es": "Espanol", "fr": "Francais", "de": "Deutsch", "it": "Italiano",
    "ja": "Japones", "ko": "Coreano", "ru": "Russo", "zh-Hans": "Chinese",
    "zh-Hant": "Chinese (Trad.)", "ar": "Arabe", "hi": "Hindi",
    "id": "Indonesio", "tr": "Turco",
}


WIZARD_STEPS = ["language", "device", "quality", "hwdec", "sponsorblock", "done"]


WIZARD_DEVICES = ["R36S / R35S", "RG35XX Plus / H", "RGB30", "Other"]


# trigger buttons (chapter navigation) - may be absent on some pads.
# NOTE: SDL2 has no trigger BUTTON constants - triggers are axes - so these
# getattr fallbacks historically aliased the stick-click buttons (7/8).
# Chapter seek therefore fires on stick clicks; volume uses the real
# trigger axes (see the CONTROLLERAXISMOTION handler).
BTN_LTRIG = getattr(sdl2, "SDL_CONTROLLER_BUTTON_LEFTTRIGGER", 7)


BTN_RTRIG = getattr(sdl2, "SDL_CONTROLLER_BUTTON_RIGHTTRIGGER", 8)


BTN_GUIDE = getattr(sdl2, "SDL_CONTROLLER_BUTTON_GUIDE", 11)


BTN_LSTICK = getattr(sdl2, "SDL_CONTROLLER_BUTTON_LEFTSTICK", 7)


BTN_RSTICK = getattr(sdl2, "SDL_CONTROLLER_BUTTON_RIGHTSTICK", 8)


# ----------------------------------------------------------------------------
# WiFi signal state (v2.2) - read from the kernel, no external tools.
#   /proc/net/wireless  -> link quality / signal dBm per wlan interface
#   /sys/class/net/*/operstate -> interface up or down
# Returns (level 0-4, connected bool); level 0 + connected True means
# "associated but strength unknown". Never raises.
# ----------------------------------------------------------------------------
def _dbm_to_bars(sig):
    if sig >= -55:
        return 4
    if sig >= -67:
        return 3
    if sig >= -75:
        return 2
    if sig >= -85:
        return 1
    return 1


def _link_to_bars(link):
    """Link quality like '45/70' or a plain 0-70 wext number -> 0-4 bars."""
    ratio = None
    text = str(link).rstrip(".")
    if "/" in text:
        try:
            lo, hi = text.split("/", 1)
            ratio = float(lo) / float(hi)
        except (TypeError, ValueError, ZeroDivisionError):
            ratio = None
    else:
        try:
            val = float(text)
        except (TypeError, ValueError):
            return 0
        ratio = val / 70.0 if val > 1 else val
    if ratio is None:
        return 0
    if ratio >= 0.75:
        return 4
    if ratio >= 0.5:
        return 3
    if ratio >= 0.25:
        return 2
    if ratio > 0.02:
        return 1
    return 0


def _read_wifi_state(sys_net="/sys/class/net",
                     proc_wireless="/proc/net/wireless"):
    """(level 0-4, connected) for the best wifi interface. Never raises."""
    best = 0
    connected = False
    try:
        names = []
        try:
            for entry in sorted(os.listdir(sys_net)):
                if entry.startswith("wlan") or entry.startswith("mlan") \
                        or entry.startswith("wlp"):
                    names.append(entry)
        except Exception:
            pass
        if not names:
            return 0, False
        quality = {}
        try:
            with open(proc_wireless, "r") as f:
                lines = f.readlines()
            for line in lines[2:]:
                parts = line.split()
                if parts and parts[0].endswith(":") and len(parts) >= 4:
                    quality[parts[0][:-1]] = parts
        except Exception:
            quality = {}
        for name in names:
            try:
                with open(os.path.join(sys_net, name, "operstate"), "r") as f:
                    state = f.read().strip()
            except Exception:
                state = ""
            if state != "up":
                continue
            connected = True
            parts = quality.get(name)
            lvl = 0
            if parts:
                try:
                    sig = float(parts[3].rstrip("."))
                except (ValueError, IndexError):
                    sig = 0.0
                if sig < 0:
                    lvl = _dbm_to_bars(sig)
                else:
                    lvl = _link_to_bars(parts[2])
            if lvl == 0:
                lvl = 4      # up but no strength info - show full fan
            best = max(best, lvl)
    except Exception:
        return 0, False
    return best, connected


# ----------------------------------------------------------------------------
# Video item
# ----------------------------------------------------------------------------
class VideoItem(object):
    def __init__(self, data=None):
        data = data or {}
        self.id = data.get("id", "")
        self.title = data.get("title", "") or "Unknown"
        self.channel = data.get("channel", data.get("uploader", "")) or "Unknown"
        self.channel_id = data.get("channel_id", "") or ""
        self.duration = data.get("duration", None)
        self.views = data.get("view_count", 0) or 0
        self.likes = data.get("like_count", 0) or 0
        self.upload_date = data.get("upload_date", "") or ""
        self.url = data.get("webpage_url", data.get("url", "")) or (
            "https://www.youtube.com/watch?v=%s" % self.id if self.id else "")
        self.is_live = bool(data.get("is_live")) or data.get("live_status") == "is_live"
        self.live_status = data.get("live_status", "") or ""
        self.source = data.get("source", "ytdlp")

        # Thumbnail URL - prefer a mid-size variant for fast loads
        self.thumbnail = ""
        if data.get("thumbnail"):
            self.thumbnail = data.get("thumbnail")
        elif data.get("thumbnails"):
            thumbs = data.get("thumbnails", [])
            if thumbs:
                for t in thumbs:
                    if t.get("url"):
                        self.thumbnail = t.get("url")
                        break
        if not self.thumbnail and self.id:
            self.thumbnail = "https://i.ytimg.com/vi/%s/mqdefault.jpg" % self.id
        # normalise giant thumbnails down to mqdefault for 640x480 screens
        if self.thumbnail and "ytimg.com/vi/" in self.thumbnail:
            m = re_match_yt(self.thumbnail)
            if m:
                self.thumbnail = "https://i.ytimg.com/vi/%s/mqdefault.jpg" % m

    def format_duration(self):
        if self.is_live:
            return self._t_live()
        d = self.duration
        if d is None:
            return ""
        try:
            d = int(float(d))
        except (TypeError, ValueError):
            return ""
        if d <= 0:
            return self._t_live() if self.source == "ytdlp" else ""
        mins, secs = divmod(d, 60)
        hours, mins = divmod(mins, 60)
        if hours:
            return "%d:%02d:%02d" % (hours, mins, secs)
        return "%d:%02d" % (mins, secs)

    _live_text = None

    def _t_live(self):
        if VideoItem._live_text is None:
            VideoItem._live_text = "LIVE"
        return VideoItem._live_text

    def format_views(self):
        if not self.views:
            return ""
        if self.views >= 1000000:
            return "%.1fM" % (self.views / 1000000.0)
        if self.views >= 1000:
            return "%.1fK" % (self.views / 1000.0)
        return str(self.views)

    def format_date(self):
        if not self.upload_date:
            return ""
        try:
            date = datetime.strptime(self.upload_date, "%Y%m%d")
            delta = datetime.now() - date
            if delta.days < 1:
                return "Today"
            if delta.days < 7:
                return "%dd" % delta.days
            if delta.days < 30:
                return "%dw" % (delta.days // 7)
            if delta.days < 365:
                return "%dmo" % (delta.days // 30)
            return "%dy" % (delta.days // 365)
        except Exception:
            return ""

    def to_dict(self):
        return {
            "id": self.id, "title": self.title, "channel": self.channel,
            "channel_id": self.channel_id, "duration": self.duration,
            "view_count": self.views, "like_count": self.likes,
            "thumbnail": self.thumbnail, "upload_date": self.upload_date,
            "url": self.url, "is_live": self.is_live,
            "live_status": self.live_status, "source": self.source,
        }


def re_match_yt(url):
    import re as _re
    m = _re.search(r"ytimg\.com/vi/([\w-]+)/", url or "")
    return m.group(1) if m else None


def fmt_clock(seconds):
    try:
        seconds = int(seconds)
    except (TypeError, ValueError):
        return "0:00"
    if seconds < 0:
        seconds = 0
    m, s = divmod(seconds, 60)
    h, m = divmod(m, 60)
    if h:
        return "%d:%02d:%02d" % (h, m, s)
    return "%d:%02d" % (m, s)


# ----------------------------------------------------------------------------
# v3.2 HUD icon rasterizer
#
# The v3.1 icons were assembled from a handful of 1-2 px rectangles and
# read as "weird shapes that are not what they say they are". These are
# real vector shapes (filled triangles, thick segments, rings, arcs,
# rounded rects) painted on a 64x64 grid, box-downsampled to 32x32 for
# smooth edges, then uploaded ONCE per (icon, color) into an SDL texture
# and blitted every frame - one RenderCopy per button, zero CPU cost.
# ----------------------------------------------------------------------------
ICON_TEX_SIZE = 32


def _rr_pred(px, py, x, y, w, h, rad):
    """Rounded-rectangle containment predicate."""
    rx0, ry0 = x + rad, y + rad
    rx1, ry1 = x + w - rad, y + h - rad
    nx = min(max(px, rx0), rx1)
    ny = min(max(py, ry0), ry1)
    dx = px - nx
    dy = py - ny
    return dx * dx + dy * dy <= rad * rad


def _icon_pixels(name, rgb):
    """Rasterize `name` into 32x32 BGRA bytes (2x supersampled)."""
    S = 64
    hit = bytearray(S * S)

    def fill_pred(x0, y0, x1, y1, pred):
        x0 = max(0, int(x0) - 1)
        y0 = max(0, int(y0) - 1)
        x1 = min(S, int(x1) + 2)
        y1 = min(S, int(y1) + 2)
        for y in range(y0, y1):
            base = y * S
            for x in range(x0, x1):
                if pred(x + 0.5, y + 0.5):
                    hit[base + x] = 1

    def clear_pred(x0, y0, x1, y1, pred):
        x0 = max(0, int(x0) - 1)
        y0 = max(0, int(y0) - 1)
        x1 = min(S, int(x1) + 2)
        y1 = min(S, int(y1) + 2)
        for y in range(y0, y1):
            base = y * S
            for x in range(x0, x1):
                if pred(x + 0.5, y + 0.5):
                    hit[base + x] = 0

    def circle(cx, cy, r):
        fill_pred(cx - r, cy - r, cx + r, cy + r,
                  lambda px, py: (px - cx) ** 2 + (py - cy) ** 2 <= r * r)

    def circle_clear(cx, cy, r):
        clear_pred(cx - r, cy - r, cx + r, cy + r,
                   lambda px, py: (px - cx) ** 2 + (py - cy) ** 2 <= r * r)

    def ring(cx, cy, r_out, r_in):
        fill_pred(cx - r_out, cy - r_out, cx + r_out, cy + r_out,
                  lambda px, py: r_in * r_in <=
                  (px - cx) ** 2 + (py - cy) ** 2 <= r_out * r_out)

    def rrect(x, y, w, h, rad=0):
        fill_pred(x, y, x + w, y + h,
                  lambda px, py: _rr_pred(px, py, x, y, w, h, rad))

    def rrect_hole(x, y, w, h, rad, hx, hy, hw, hh, hrad):
        fill_pred(x, y, x + w, y + h,
                  lambda px, py: _rr_pred(px, py, x, y, w, h, rad) and
                  not _rr_pred(px, py, hx, hy, hw, hh, hrad))

    def tri(p1, p2, p3):
        (x1, y1), (x2, y2), (x3, y3) = p1, p2, p3

        def sgn(ax, ay, bx, by, px, py):
            return (px - bx) * (ay - by) - (ax - bx) * (py - by)

        def pred(px, py):
            d1 = sgn(x1, y1, x2, y2, px, py)
            d2 = sgn(x2, y2, x3, y3, px, py)
            d3 = sgn(x3, y3, x1, y1, px, py)
            neg = (d1 < 0) or (d2 < 0) or (d3 < 0)
            pos = (d1 > 0) or (d2 > 0) or (d3 > 0)
            return not (neg and pos)
        fill_pred(min(x1, x2, x3), min(y1, y2, y3),
                  max(x1, x2, x3), max(y1, y2, y3), pred)

    def seg(x1, y1, x2, y2, t):
        dx, dy = x2 - x1, y2 - y1
        L2 = dx * dx + dy * dy
        half = (t / 2.0) ** 2

        def pred(px, py):
            if L2 == 0:
                d2 = (px - x1) ** 2 + (py - y1) ** 2
            else:
                u = ((px - x1) * dx + (py - y1) * dy) / float(L2)
                u = min(1.0, max(0.0, u))
                qx = x1 + u * dx
                qy = y1 + u * dy
                d2 = (px - qx) ** 2 + (py - qy) ** 2
            return d2 <= half
        fill_pred(min(x1, x2) - t, min(y1, y2) - t,
                  max(x1, x2) + t, max(y1, y2) + t, pred)

    def arc(cx, cy, r, a0, a1, t):
        """Angles in degrees (screen coords, y down: 0=right 90=bottom).
        Covers a0 -> a1 moving through INCREASING angle (screen-CW)."""
        a0n = a0 % 360.0
        a1n = a1 % 360.0
        half = t / 2.0

        def pred(px, py):
            d = math.sqrt((px - cx) ** 2 + (py - cy) ** 2)
            if abs(d - r) > half:
                return False
            a = math.degrees(math.atan2(py - cy, px - cx)) % 360.0
            if a0n <= a1n:
                return a0n <= a <= a1n
            return a >= a0n or a <= a1n
        fill_pred(cx - r - t, cy - r - t, cx + r + t, cy + r + t, pred)

    def arrow_head(ex, ey, tx, ty, ln=11.0, wd=9.0):
        """Filled triangle: tip ahead of (ex, ey) along (tx, ty)."""
        nx, ny = -ty, tx
        tri((ex + tx * ln, ey + ty * ln),
            (ex + nx * wd * 0.5, ey + ny * wd * 0.5),
            (ex - nx * wd * 0.5, ey - ny * wd * 0.5))

    def mirror_x():
        nonlocal hit
        flipped = bytearray(S * S)
        for y in range(S):
            base = y * S
            for x in range(S):
                flipped[base + x] = hit[base + (S - 1 - x)]
        hit = flipped

    if name == "play":
        tri((22, 12), (22, 52), (56, 32))
    elif name == "pause":
        rrect(19, 14, 10, 36, 4)
        rrect(35, 14, 10, 36, 4)
    elif name == "next":
        # right-pointing triangle, gap, bar on the right
        tri((14, 12), (14, 52), (44, 32))
        rrect(49, 14, 7, 36, 3)
    elif name == "prev":
        # bar on the left, gap, left-pointing triangle
        rrect(8, 14, 7, 36, 3)
        tri((20, 32), (50, 12), (50, 52))
    elif name == "fwd10":
        # clockwise skip arrow with the gap at the upper right
        arc(32, 32, 24, 335, 635, 6)
        a = math.radians(635.0 % 360.0)
        ex = 32 + 24 * math.cos(a)
        ey = 32 + 24 * math.sin(a)
        arrow_head(ex, ey, -math.sin(a), math.cos(a))
    elif name == "back10":
        arc(32, 32, 24, 335, 635, 6)
        a = math.radians(635.0 % 360.0)
        ex = 32 + 24 * math.cos(a)
        ey = 32 + 24 * math.sin(a)
        arrow_head(ex, ey, -math.sin(a), math.cos(a))
        mirror_x()
    elif name == "cc":
        rrect_hole(4, 14, 56, 36, 8, 10, 20, 44, 24, 5)
    elif name == "speed":
        # speedometer: upper half ring + needle + hub
        arc(32, 38, 22, 180, 360, 6)
        seg(32, 38, 45, 21, 5)
        circle(32, 38, 5)
    elif name == "quality":
        # monitor + stand
        rrect_hole(4, 6, 56, 42, 7, 10, 12, 44, 30, 4)
        rrect(27, 48, 10, 5, 1)
        rrect(18, 54, 28, 5, 2)
    elif name == "chapters":
        # bookmark
        rrect(18, 6, 28, 32, 3)
        tri((18, 38), (46, 38), (32, 56))
    elif name == "loop":
        # two opposing arcs with arrowheads (the standard loop glyph):
        # top arc ends upper-right pointing down, bottom arc ends
        # lower-left pointing up - clear 40-degree gaps make it read as
        # a loop, not a circle
        arc(32, 32, 20, 200, 340, 6)
        a = math.radians(340.0)
        ex = 32 + 20 * math.cos(a)
        ey = 32 + 20 * math.sin(a)
        arrow_head(ex, ey, -math.sin(a), math.cos(a), 12.0, 9.0)
        arc(32, 32, 20, 20, 160, 6)
        a = math.radians(160.0)
        ex = 32 + 20 * math.cos(a)
        ey = 32 + 20 * math.sin(a)
        arrow_head(ex, ey, -math.sin(a), math.cos(a), 12.0, 9.0)
    elif name == "gear":
        ring(32, 32, 17, 8)
        for k in range(8):
            a = math.radians(k * 45.0)
            seg(32 + 12 * math.cos(a), 32 + 12 * math.sin(a),
                32 + 25 * math.cos(a), 32 + 25 * math.sin(a), 8)
        circle_clear(32, 32, 8)
    else:
        circle(32, 32, 12)

    # downsample 2x2 -> alpha, emit BGRA (little-endian ARGB8888)
    out = bytearray(ICON_TEX_SIZE * ICON_TEX_SIZE * 4)
    r, g, b = rgb[0], rgb[1], rgb[2]
    for y in range(ICON_TEX_SIZE):
        srow = 2 * y * S
        drow = y * ICON_TEX_SIZE * 4
        for x in range(ICON_TEX_SIZE):
            c = hit[srow + 2 * x] + hit[srow + 2 * x + 1] + \
                hit[srow + S + 2 * x] + hit[srow + S + 2 * x + 1]
            i = drow + x * 4
            out[i] = b
            out[i + 1] = g
            out[i + 2] = r
            out[i + 3] = (c * 255) // 4
    return bytes(out)


_ICON_TEX_CACHE = {}


def _get_icon_texture(renderer, name, rgb):
    """Cached 32x32 texture for (icon, color) - created on first use."""
    key = (name, rgb)
    tex = _ICON_TEX_CACHE.get(key)
    if tex is None:
        try:
            buf = _icon_pixels(name, rgb)
            tex = SDL_CreateTexture(
                renderer, sdl2.SDL_PIXELFORMAT_ARGB8888,
                sdl2.SDL_TEXTUREACCESS_STATIC,
                ICON_TEX_SIZE, ICON_TEX_SIZE)
            if tex:
                SDL_UpdateTexture(tex, None, buf, ICON_TEX_SIZE * 4)
                SDL_SetTextureBlendMode(tex, SDL_BLENDMODE_BLEND)
        except Exception as e:
            LOG("icon rasterize failed (%s): %s" % (name, e), "APP")
            tex = None
        _ICON_TEX_CACHE[key] = tex
    return tex


def _destroy_icon_cache():
    for tex in list(_ICON_TEX_CACHE.values()):
        if tex:
            try:
                SDL_DestroyTexture(tex)
            except Exception:
                pass
    _ICON_TEX_CACHE.clear()
