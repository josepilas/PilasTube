#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
PilasTube v3.5 - player.py (playback domain)

The built-in SmartTube-style player: FFPlayer (one SDL process, ffmpeg
pipes video frames into a streaming texture and PCM audio into
SDL_QueueAudio, live HLS master-manifest audio pairing, muxed fallback),
binary discovery (yt-dlp / ffmpeg / external player), playback control
(seek / speed / quality / codec / chapters), the player HUD + options row,
the player menus and the playback queue (PlayerMixin).
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


from utils import (
    ICON_TEX_SIZE,
    LANG_NAMES,
    LOG,
    QUALITY_OPTIONS,
    SCREEN_HEIGHT,
    SCREEN_WIDTH,
    UI_SCALE,
    SCRIPT_DIR,
    WINDOW_HEIGHT,
    WINDOW_WIDTH,
    apply_logical_mapping,
    SDL_BLENDMODE_BLEND,
    SDL_BLENDMODE_NONE,
    SDL_ClearQueuedAudio,
    SDL_CreateRenderer,
    SDL_CreateTexture,
    SDL_CreateWindow,
    SDL_DestroyRenderer,
    SDL_DestroyTexture,
    SDL_DestroyWindow,
    SDL_GetTicks,
    SDL_PauseAudioDevice,
    SDL_QueueAudio,
    SDL_RENDERER_ACCELERATED,
    SDL_RENDERER_PRESENTVSYNC,
    SDL_RENDERER_SOFTWARE,
    SDL_RaiseWindow,
    SDL_Rect,
    SDL_RenderCopy,
    SDL_RenderPresent,
    SDL_SetRenderDrawBlendMode,
    SDL_SetTextureBlendMode,
    SDL_ShowWindow,
    SDL_UpdateTexture,
    SDL_WINDOWPOS_CENTERED,
    SLOG,
    SPEED_STEPS,
    _PLOG,
    _get_icon_texture,
    _sdl_err,
    fmt_clock,
    run_logged_thread,
    sdl2,
)
import yt_extras as YX

# SponsorBlock category colors on the player progress bar (SmartTube-style)
SB_COLORS = {
    "sponsor": (255, 204, 0),        # yellow - sponsor
    "selfpromo": (255, 120, 0),      # orange - self promotion
    "interaction": (170, 120, 255),  # purple - subscribe reminders
    "intro": (100, 200, 255),        # blue - intro
    "outro": (100, 200, 255),        # blue - outro
    "preview": (120, 255, 170),      # green - preview/recap
    "filler": (200, 200, 200),       # grey - filler
    "music_offtopic": (255, 120, 200),
}


# ----------------------------------------------------------------------------
# Helpers: locate yt-dlp / video player
# ----------------------------------------------------------------------------
def find_ytdlp():
    paths = [
        os.path.join(SCRIPT_DIR, "yt-dlp"),
        os.path.expanduser("~/.local/bin/yt-dlp"),
        "/home/ark/.local/bin/yt-dlp",
        "/usr/local/bin/yt-dlp",
        "/usr/bin/yt-dlp",
    ]
    for p in paths:
        if os.path.exists(p):
            try:
                os.chmod(p, 0o755)
            except Exception:
                pass
            return p
    try:
        result = subprocess.run(["which", "yt-dlp"],
                                stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE,
                                universal_newlines=True, timeout=5)
        if result.returncode == 0 and result.stdout.strip():
            return result.stdout.strip()
    except Exception:
        pass
    return None


def find_video_player():
    players = ["mpv", "ffplay", "vlc", "mplayer"]
    for player in players:
        try:
            result = subprocess.run(["which", player],
                                    stdout=subprocess.PIPE,
                                    stderr=subprocess.PIPE,
                                    universal_newlines=True, timeout=5)
            if result.returncode == 0 and result.stdout.strip():
                return result.stdout.strip()
        except Exception:
            continue
    pm_ffplay = "/opt/system/Tools/PortMaster/libs/ffplay"
    if os.path.exists(pm_ffplay):
        return pm_ffplay
    return None


def find_ffmpeg():
    """v3.0: the in-app player decodes with the ffmpeg CLI and pipes raw
    video frames + PCM audio straight into our SDL window / audio queue.
    This keeps the whole app in ONE process - on KMSDRM devices only one
    process may own the display, which is why the old "spawn ffplay"
    approach deadlocked the screen after pressing B (pageflip -16)."""
    candidates = ["ffmpeg", "/usr/bin/ffmpeg", "/usr/local/bin/ffmpeg",
                  "/opt/system/Tools/PortMaster/libs/ffmpeg"]
    for cand in candidates:
        try:
            if os.sep not in cand:
                result = subprocess.run(["which", cand],
                                        stdout=subprocess.PIPE,
                                        stderr=subprocess.PIPE,
                                        universal_newlines=True, timeout=5)
                if result.returncode == 0 and result.stdout.strip():
                    return result.stdout.strip()
            elif os.path.isfile(cand) and os.access(cand, os.X_OK):
                return cand
        except Exception:
            continue
    return None


YTDLP_PATH = find_ytdlp()


VIDEO_PLAYER = find_video_player()


FFMPEG_PATH = find_ffmpeg()


PLAYER_IS_MPV = VIDEO_PLAYER and os.path.basename(VIDEO_PLAYER) == "mpv"


# v3.0: when an ffmpeg binary exists we ALWAYS use the built-in player
# (video+audio together, on-screen HUD, safe B-exit). External players are
# only a last-resort fallback now.
USE_BUILTIN_PLAYER = bool(FFMPEG_PATH)


LOG("ffmpeg for built-in player: %s" % (FFMPEG_PATH or "NOT FOUND"),
    "PLAYER")


# ----------------------------------------------------------------------------
# FFPlayer - the v3.0 built-in video player (SmartTube-style, in-process).
#
# Why: on KMSDRM handhelds only ONE process may own the display. v2.2 spawned
# a second SDL process (ffplay) which fought our app for the DRM master -
# after pressing B the app's own pageflips failed forever ("Could not queue
# pageflip: -16") leaving a dead black screen. It also played a video-ONLY
# HLS variant (no sound) and, running as root, could not reach the user's
# PulseAudio at all.
#
# How: a single ffmpeg subprocess pipes raw bgr0 frames (fd 3) and s16le
# 48kHz stereo PCM (fd 4) into this process. Frames go to a streaming SDL
# texture, PCM goes to SDL_QueueAudio (master clock). Backpressure is free:
# when we stop reading, the 64 KB pipes fill and ffmpeg stalls by itself.
# Pause = stop the clock + let the pipes fill. Seek/speed/quality = relaunch
# ffmpeg with -ss / atempo / new URLs. No DRM handoff ever happens.
# ----------------------------------------------------------------------------
AUDIO_RATE = 48000


AUDIO_CHANNELS = 2


AUDIO_BYTES_PER_SEC = AUDIO_RATE * AUDIO_CHANNELS * 2   # s16le stereo


# v3.2: audio submission may lead the playback clock by this much; the
# device queue is capped by the clock itself (see FFPlayer.pump)
AUDIO_LEAD_SECONDS = 1.2


SEEK_COOLDOWN_MS = 700            # v3.2: min gap between ffmpeg relaunches


MAX_VIDEO_QUEUE = 4                                     # decoded frames held


def _short_cmd_part(arg, limit=90):
    """Log-friendly ffmpeg argument: URLs keep scheme + first 80 chars."""
    s = str(arg)
    if s.startswith(("http://", "https://")) and len(s) > limit:
        return s[:limit] + "..."
    return s


class FFPlayer(object):
    """Raw-pipe player driven by the main UI loop (pull model).

    The app calls pump() every UI frame; pump() queues audio to SDL and
    returns the newest video frame that should be on screen right now.
    """

    def __init__(self, ffmpeg_path, renderer,
                 video_url, audio_url, width, height, fps,
                 start_pos=0.0, speed=1.0, sub_file=None,
                 hw_accel_hint=True, route="Default", is_live=False,
                 audio_in_video=False):
        self.ffmpeg = ffmpeg_path
        self.renderer = renderer
        self.video_url = video_url
        self.audio_url = audio_url
        self.has_audio = bool(audio_url)
        # v3.3: live streams are never seekable (rolling HLS window) - no
        # -ss on spawn, seeks rejected, positions not saved/resumed
        self.is_live = bool(is_live)
        # v3.4: single-input streams that carry BOTH video and audio (muxed
        # live variants) - the audio pipe maps 0:a:0 instead of 1:a:0
        self.audio_in_video = bool(audio_in_video)
        # native stream size (stats / quality display) - the pipe carries
        # the screen-fit size instead (see _scaled_size)
        self.src_width = max(2, int(width or 640))
        self.src_height = max(2, int(height or 360))
        self.fps = float(fps or 30.0) or 30.0
        self.speed = float(speed or 1.0)
        self.sub_file = sub_file
        self.hw_accel_hint = hw_accel_hint

        # playback state
        self.position = float(start_pos or 0.0)
        self.duration = 0.0
        self.paused = False
        self.ended = False
        self.failed = False
        self.error_msg = ""
        self.seek_pending = False
        self.frames_shown = 0
        self.frames_dropped = 0
        self.decode_fps = 0.0

        # clock v3.2: ACCUMULATED wall time. The old audio-master design
        # trusted SDL_GetQueuedAudioSize() for the playhead - on some audio
        # drivers (PipeWire/dmix) that call misreports, which made the
        # progress bar race ahead at "10x speed" (position = submitted
        # bytes). The new clock only ever adds small measured dt values
        # while the audio pipeline is healthy, so the position can never
        # exceed real elapsed time. The audio submission counter can only
        # FREEZE the clock (network stall), never accelerate it.
        self._clock_base = float(start_pos or 0.0)
        self._clock_started = None      # tick when first data arrived
        self._clock_accum = 0.0         # seconds of healthy playback
        self._last_pump_ms = None       # tick of previous pump() call
        self._last_data_ms = None       # tick of last decoded data
        self.starving = False           # audio pipeline dry (buffering)

        # audio
        self.audio_dev = None
        self.audio_failed = False
        self._audio_submitted = 0       # bytes handed to SDL since (re)start
        self._pending_audio = []        # decoded but not yet queued
        self._pending_audio_bytes = 0
        self.volume = 100               # 0..100 -> SDL MixAudio 0..128

        # process + pipes + queues
        self.proc = None
        self._seek_deferred = None       # v3.2: coalesced seek target
        self._last_spawn_ms = None       # v3.2: last ffmpeg (re)launch tick
        self._gen = 0                    # v3.2: spawn generation tag
        self.route = "Default"           # v3.2: network route flavor
        self._pipe_v = None             # (r, w) os.pipe for video
        self._pipe_a = None             # (r, w) os.pipe for audio
        self._video_q = None            # queue.Queue of bytes frames
        self._audio_q = None            # queue.Queue of byte chunks
        self._threads = []
        self._lock = threading.Lock()
        self._frame_decode_times = []
        self._frame_idx = 0             # sequential index of decoded frames
        self._held = None               # (idx, frame) shown later when due
        self._late_pending = False      # a due frame was superseded (late)

        self.texture = None
        self.last_frame = None
        self._apply_size()

    # ------------------------------------------------------------ lifecycle
    def _scaled_size(self):
        """Even WxH that fits the screen, preserving the stream aspect.

        ffmpeg scales to exactly this size, so SDL blits 1:1 (no per-frame
        scaling / colorspace conversion in the renderer) and the pipe
        carries fewer bytes - both matter a lot on a slow ARM core.

        v0.3.8: the size is computed in LOGICAL coordinates (the 640x480
        design grid) and then multiplied by UI_SCALE so the decode happens
        at the device's PHYSICAL resolution - on a 1024x768 panel video
        renders at 1024x768 instead of 640x480 (sharper, same pipe layout).
        Capped at ~720p worth of pixels so small ARM cores are safe.
        """
        sw = max(2, int(self.src_width or 640))
        sh = max(2, int(self.src_height or 360))
        scale = min(SCREEN_WIDTH / float(sw), SCREEN_HEIGHT / float(sh), 1.0)
        w = max(2, int(round(sw * scale))) & ~1
        h = max(2, int(round(sh * scale))) & ~1
        sc = UI_SCALE if UI_SCALE and UI_SCALE > 1.0 else 1.0
        if sc != 1.0:
            w = max(2, int(round(w * sc))) & ~1
            h = max(2, int(round(h * sc))) & ~1
            # never upscale beyond the SOURCE resolution (a 640x480 video
            # gains nothing from decoding at 1024x768 - the GPU upscales
            # it for free), and keep the decode within a ~720p pixel
            # budget so small ARM cores are always safe.
            cap_w, cap_h = sw & ~1, sh & ~1
            if w * h > 1000000 or w > cap_w or h > cap_h:
                shrink = 1.0
                if w * h > 1000000:
                    shrink = min(shrink,
                                 math.sqrt(1000000.0 / (w * h)))
                if w > cap_w or h > cap_h:
                    # scale down to the source size, aspect preserved
                    shrink = min(shrink, cap_w / float(w), cap_h / float(h))
                w = max(2, int(round(w * shrink))) & ~1
                h = max(2, int(round(h * shrink))) & ~1
        return w, h

    def _apply_size(self):
        self.width, self.height = self._scaled_size()
        self.frame_bytes = self.width * self.height * 4

    def start(self, audio_dev=None):
        self.audio_dev = audio_dev
        self._spawn(self.position)

    def _spawn(self, start_pos):
        self.ended = False
        self.failed = False
        self.seek_pending = True
        self._gen += 1
        if self.is_live:
            # v3.3: live has no seekable timeline - the clock counts from
            # the live edge (position 0) no matter what start_pos says
            start_pos = 0.0
        gen = self._gen
        vq = queue.Queue(maxsize=MAX_VIDEO_QUEUE)
        aq = queue.Queue(maxsize=32)
        self._video_q = vq
        self._audio_q = aq
        self._frame_idx = 0
        self._held = None
        self._late_pending = False
        with self._lock:
            self._pending_audio = []
            self._pending_audio_bytes = 0
            self._audio_submitted = 0

        cmd = [self.ffmpeg, "-hide_banner", "-nostdin",
               "-loglevel", "info", "-stats",
               # v3.2: -re paces decoding at native rate. Without it ffmpeg
               # burst-decodes as fast as the network allows, overflowing
               # the queues and making every early frame "late" (dropped).
               "-re"]
        # reconnect flags are HTTP-protocol options - ffmpeg ABORTS with
        # "Option reconnect not found" when they meet a local file input,
        # so they are only added for network URLs
        if str(self.video_url).startswith(("http://", "https://")):
            # Knulli / Miyoo Flip fix: YouTube googlevideo.com streams reject ffmpeg's default Lavf user-agent with HTTP 403.
            # Passing a browser User-Agent matching yt-dlp allows the raw streams to decode without 403 Forbidden errors.
            ua = getattr(YX, "USER_AGENT", "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36")
            cmd += ["-user_agent", ua,
                    "-reconnect", "1", "-reconnect_streamed", "1",
                    "-reconnect_delay_max", "4"]
            # v3.2 route flavors (SmartTube-style): OkHttp = connection
            # reuse; Cronet = reuse + resilience (Chromium-style stack)
            if self.route in ("Cronet", "OkHttp"):
                cmd += ["-multiple_requests", "1"]
        if start_pos and start_pos > 0.5 and not self.is_live:
            # v3.3: live HLS inputs cannot seek ("could not seek to position
            # 6876" in the device log) - a live relaunch always starts at
            # the live edge
            cmd += ["-ss", "%.3f" % float(start_pos)]
        cmd += ["-i", self.video_url]
        if self.has_audio:
            if start_pos and start_pos > 0.5 and not self.is_live:
                cmd += ["-ss", "%.3f" % float(start_pos)]
            cmd += ["-i", self.audio_url]

        # video output -> first pipe (bgra raw frames).
        # bgra memory is B,G,R,A - byte-for-byte what SDL's ARGB8888
        # texture expects on little-endian, so SDL_UpdateTexture does a
        # plain copy with NO channel swizzle (v3.0 used bgr0 + BGRX8888:
        # the padding byte landed in the blue channel -> "bluish tint").
        vf = []
        if abs(self.speed - 1.0) > 0.001:
            vf.append("setpts=PTS/%.4f" % self.speed)
        # scale once, in ffmpeg, to the exact blit size
        vf.append("scale=%d:%d:flags=bilinear" % (self.width, self.height))
        if self.sub_file:
            esc = self.sub_file.replace("\\", "/").replace(":", "\\:")
            vf.append("subtitles=filename='%s'" % esc)
        cmd += ["-map", "0:v:0", "-pix_fmt", "bgra"]
        if vf:
            cmd += ["-vf", ",".join(vf)]
        # v3.2: HLS inputs sometimes carry no framerate metadata, which made
        # ffmpeg fall back to a 25 fps rawvideo output while we schedule
        # frames at the (correct) 30 fps - judder + excessive frame drops.
        # Forcing the output rate keeps the pipe's frame cadence honest.
        if self.fps and 1.0 <= self.fps <= 120.0:
            cmd += ["-r", "%d" % int(round(self.fps))]

        pipe_v = os.pipe()
        # v3.4: a muxed single input still gets an audio pipe (0:a:0)
        pipe_a = os.pipe() if (self.has_audio or self.audio_in_video) \
            else None
        w_v = pipe_v[1]
        w_a = pipe_a[1] if pipe_a else -1
        # subprocess(close_fds=True) closes everything >2 in the child AFTER
        # preexec_fn, so a preexec dup2 onto fd 3 gets clobbered. Instead we
        # keep the pipe write-ends open at their natural fd numbers with
        # pass_fds and simply tell ffmpeg to write to "pipe:<that number>".
        pass_fds = (w_v,) if pipe_a is None else (w_v, w_a)
        cmd += ["-f", "rawvideo", "pipe:%d" % w_v]

        # audio output -> second pipe (s16le 48k stereo). v3.4: the map is
        # OPTIONAL ("1:a:0?" / "0:a:0?") so a stream that turns out to have
        # no audio track degrades to silent video instead of killing the
        # whole playback with "matches no streams".
        if self.has_audio or self.audio_in_video:
            src = "1:a:0" if self.has_audio else "0:a:0"
            cmd += ["-map", src + "?"]
            if abs(self.speed - 1.0) > 0.001:
                cmd += ["-af", "atempo=%.4f" % self.speed]
            cmd += ["-f", "s16le", "-ar", str(AUDIO_RATE),
                    "-ac", str(AUDIO_CHANNELS), "pipe:%d" % w_a]

        try:
            self.proc = subprocess.Popen(
                cmd, stdin=subprocess.DEVNULL, stdout=subprocess.DEVNULL,
                stderr=subprocess.PIPE, universal_newlines=False,
                pass_fds=pass_fds)
        except Exception as e:
            LOG("ffmpeg spawn failed: %s" % e, "PLAYER")
            self.failed = True
            self.error_msg = str(e)
            for pipe in (pipe_v, pipe_a):
                if pipe:
                    for fd in pipe:
                        try:
                            os.close(fd)
                        except OSError:
                            pass
            return
        LOG("ffmpeg launched (pid %s) %.0fp%s%s%s start=%.1fs route=%s" %
            (self.proc.pid, self.height, "@%.0f" % self.fps,
             " +audio" if (self.has_audio or self.audio_in_video) else "",
             " LIVE" if self.is_live else "", start_pos, self.route),
            "PLAYER")
        LOG("cmd: %s" % " ".join(_short_cmd_part(a) for a in cmd), "PLAYER")

        # parent closes the write ends; the child owns them now
        try:
            os.close(pipe_v[1])
        except OSError:
            pass
        if pipe_a is not None:
            try:
                os.close(pipe_a[1])
            except OSError:
                pass
        self._pipe_v = pipe_v
        self._pipe_a = pipe_a

        # reader threads (v3.2: each generation gets its OWN queues - a
        # lingering reader from a previous spawn can never corrupt the new
        # stream with stale frames/chunks of a different frame size; that
        # was the "colors break when the video is opened again" bug)
        need = self.frame_bytes
        self._threads = [
            run_logged_thread("ff-video", self._video_reader,
                              args=(gen, vq, need), daemon=True),
            run_logged_thread("ff-stderr", self._stderr_reader,
                              daemon=True),
        ]
        if pipe_a is not None:
            self._threads.append(
                run_logged_thread("ff-audio", self._audio_reader,
                                  args=(gen, aq), daemon=True))

        # reset the clock so the new stream starts pacing from start_pos.
        # the clock stays FROZEN until the first frame/audio actually
        # arrives - ffmpeg needs seconds to open a network input, and a
        # running clock during that window made the progress bar race
        # ahead of what has actually been decoded.
        self._clock_base = float(start_pos or 0.0)
        self._clock_started = None
        self._clock_accum = 0.0
        self._last_pump_ms = None
        self._last_data_ms = None
        self.starving = False
        self.position = float(start_pos or 0.0)
        self._last_spawn_ms = SDL_GetTicks()

    # --------------------------------------------------------------- threads
    def _video_reader(self, gen, vq, need):
        """Reads `need`-byte BGRA frames from the video pipe into `vq`.

        v3.2: fd, frame size AND queue are all captured per generation, so
        a thread that outlives its spawn cycle writes only into its own
        dead queue (never read again) instead of mixing old-size frames
        into the new stream. Also verifies the frame length defensively."""
        pipe_v = self._pipe_v if self._gen == gen else None
        fd = pipe_v[0] if pipe_v else -1
        while fd >= 0 and not self.failed:
            buf = bytearray()
            while len(buf) < need:
                try:
                    chunk = os.read(fd, need - len(buf))
                except (OSError, ValueError):
                    chunk = b""
                if not chunk:
                    # EOF: ffmpeg exited
                    if buf:
                        # final partial frame - ignore, incomplete
                        pass
                    if self._gen == gen:
                        self.ended = self._proc_dead()
                    return
                buf += chunk
            if len(buf) != need:
                continue
            try:
                vq.put(bytes(buf), timeout=0.25)
            except queue.Full:
                continue    # retry - main loop will drain it
            except Exception:
                return

    def _audio_reader(self, gen, aq):
        pipe_a = self._pipe_a if self._gen == gen else None
        fd = pipe_a[0] if pipe_a else -1
        while fd >= 0 and not self.failed:
            try:
                chunk = os.read(fd, 16384)
            except (OSError, ValueError):
                return
            if not chunk:
                return
            try:
                aq.put(chunk, timeout=0.25)
            except queue.Full:
                continue
            except Exception:
                return

    def _stderr_reader(self):
        try:
            stream = self.proc.stderr
            if not stream:
                return
            import io as _io
            buf = b""
            while True:
                chunk = stream.read(4096)
                if not chunk:
                    break
                buf += chunk
                while b"\n" in buf:
                    line, buf = buf.split(b"\n", 1)
                    try:
                        text = line.decode("utf-8", "replace").strip()
                    except Exception:
                        continue
                    if text:
                        LOG("ffmpeg: %s" % text[:240], "PLAYER")
        except Exception:
            pass

    def _proc_dead(self):
        try:
            return self.proc is not None and self.proc.poll() is not None
        except Exception:
            return True

    # ----------------------------------------------------------------- clock
    def _elapsed(self):
        """Seconds of healthy (accumulated) playback since (re)start."""
        return self._clock_accum

    def _wall_position(self):
        return self._clock_base + self._clock_accum * self.speed

    # ------------------------------------------------------------------ pump
    def pump(self):
        """Called once per UI frame: queue audio, pick the frame to show.

        v3.2 clock (ACCUMULATED WALL TIME, audio-starve guarded):
          self._clock_accum grows by the real dt between pumps, but ONLY
          while unpaused AND the audio pipeline is not starved. position =
          base + accum * speed. Because accum is fed by measured pump
          intervals and can only ever ADD small positive dt values, the
          position is structurally incapable of racing ahead of real time
          (the old audio-master clock trusted SDL_GetQueuedAudioSize(),
          which misreports on some drivers -> "10x speed" progress bar).
        """
        now_ms = SDL_GetTicks()

        # 0. deferred (coalesced) seek ready?
        if self._seek_deferred is not None and \
                (self._last_spawn_ms is None or
                 now_ms - self._last_spawn_ms >= SEEK_COOLDOWN_MS):
            target = self._seek_deferred
            self._seek_deferred = None
            self._do_seek(target)
            return self.last_frame

        # 1. advance the clock by the measured dt (clamped: a UI hiccup
        #    must not make the clock jump; audio in the device keeps the
        #    reference honest anyway)
        if self._last_pump_ms is not None:
            dt = (now_ms - self._last_pump_ms) / 1000.0
            if dt < 0.0:
                dt = 0.0
            elif dt > 0.1:
                dt = 0.1
        else:
            dt = 0.0
        self._last_pump_ms = now_ms

        # 2. drain decoded audio into SDL. The ONLY throttle is the clock
        #    itself - submit at most AUDIO_LEAD_SECONDS ahead of it.
        #    SDL_GetQueuedAudioSize is deliberately NOT used for pacing.
        if self.audio_dev is not None and not self.paused:
            submitted_s = self._audio_submitted / float(AUDIO_BYTES_PER_SEC)
            moved = 0
            while submitted_s < self._clock_accum + AUDIO_LEAD_SECONDS and \
                    moved < 12:
                try:
                    chunk = self._audio_q.get_nowait()
                except queue.Empty:
                    break
                except Exception:
                    break
                with self._lock:
                    self._pending_audio.append(chunk)
                    self._pending_audio_bytes += len(chunk)
                submitted_s += len(chunk) / float(AUDIO_BYTES_PER_SEC)
                moved += 1
                self._last_data_ms = now_ms
            self._flush_pending_audio()

        # 3. position: accumulate while healthy; freeze while the audio
        #    pipeline is starved (network stall) or paused. The clock can
        #    never run ahead of the audio it has actually handed out, and
        #    can never exceed real elapsed time.
        self.starving = False
        if self._clock_started is None:
            if self._audio_submitted > 0 or self.frames_shown > 0:
                self._clock_started = now_ms
                self._last_data_ms = now_ms
        else:
            healthy = True
            if self.has_audio and self.audio_dev is not None and \
                    (self._audio_submitted > 0 or self._clock_accum < 12.0):
                # (the 12 s grace window: if the audio track never produces
                # anything at all, fall back to pure wall-clock playback
                # instead of freezing the video forever)
                submitted_s = self._audio_submitted / \
                    float(AUDIO_BYTES_PER_SEC)
                # audio pipeline dry and ffmpeg still working -> freeze
                # (if the process died, let the clock finish the tail)
                if submitted_s < self._clock_accum - 0.25 and \
                        not self._proc_dead():
                    healthy = False
                    self.starving = True
            if healthy and not self.paused and self._seek_deferred is None:
                self._clock_accum += dt
        # 0b. while a seek is pending, position IS the pending target
        # (set optimistically by seek()) - do not overwrite it with the
        # frozen clock value
        if self._seek_deferred is None:
            self.position = self._clock_base + self._clock_accum * self.speed

        # 4. pick video frames that are due
        if not self.paused and self._video_q is not None:
            # 4a. a frame held back from an earlier pump may be due now
            if self._held is not None:
                idx, frame = self._held
                if self._clock_base + idx / self.fps <= self.position + 0.03:
                    self.last_frame = frame
                    self._held = None
                    self.frames_shown += 1
                    self.seek_pending = False
                    self._note_decode(now_ms)
                    self._last_data_ms = now_ms
            # 4b. pop everything the decoder produced since last pump
            while self._held is None:
                try:
                    frame = self._video_q.get_nowait()
                except queue.Empty:
                    break
                except Exception:
                    break
                idx = self._frame_idx
                self._frame_idx += 1
                if self._clock_base + idx / self.fps <= \
                        self.position + 0.03:
                    # due: show it (older due frames were late -> dropped)
                    self.last_frame = frame
                    self.frames_shown += 1
                    self.frames_dropped += 1 if self._late_pending else 0
                    self._late_pending = False
                    self.seek_pending = False
                    self._note_decode(now_ms)
                    self._last_data_ms = now_ms
                else:
                    # future frame: hold it, do not lose it
                    self._held = (idx, frame)
                    self._late_pending = False

        # 5. end of stream? (wait for the audio tail to be handed out too)
        if not self.ended and self._video_q is not None and \
                self._video_q.qsize() == 0 and self._held is None and \
                self._proc_dead():
            audio_tail = True
            if self.has_audio and self._audio_submitted > 0:
                submitted_s = self._audio_submitted / \
                    float(AUDIO_BYTES_PER_SEC)
                audio_tail = self._clock_accum >= submitted_s - 0.05
            if audio_tail:
                self.ended = True

        return self.last_frame

    def _note_decode(self, now_ms):
        self._frame_decode_times.append(now_ms)
        while self._frame_decode_times and \
                now_ms - self._frame_decode_times[0] > 2000:
            self._frame_decode_times.pop(0)
        self.decode_fps = len(self._frame_decode_times) / 2.0

    def _flush_pending_audio(self):
        if not self._pending_audio:
            return
        vol = int(max(0, min(100, self.volume)) * 1.28)
        try:
            with self._lock:
                chunks = self._pending_audio
                self._pending_audio = []
                self._pending_audio_bytes = 0
            for chunk in chunks:
                if vol >= 128:
                    data = chunk
                elif vol <= 0:
                    data = b"\x00" * len(chunk)
                else:
                    data = self._mix_volume(chunk, vol)
                SDL_QueueAudio(self.audio_dev, data, len(data))
                self._audio_submitted += len(data)
        except Exception as e:
            LOG("audio queue error: %s" % e, "PLAYER")

    @staticmethod
    def _mix_volume(chunk, vol):
        """Scale s16le samples by vol/128 using SDL_MixAudioFormat (C speed).
        Mixing onto silence == volume-scaled copy."""
        try:
            dst = ctypes.create_string_buffer(len(chunk))
            sdl2.SDL_MixAudioFormat(
                dst, ctypes.create_string_buffer(chunk, len(chunk)),
                sdl2.AUDIO_S16LSB, len(chunk), int(vol))
            return dst.raw
        except Exception:
            return chunk

    # -------------------------------------------------------------- controls
    def toggle_pause(self):
        if self.ended:
            return
        if not self.paused:
            self.paused = True
            # v3.2 clock: the accumulated clock simply stops growing while
            # paused (pump skips the dt add) - no pause-marker math left.
            if self.audio_dev is not None:
                try:
                    SDL_PauseAudioDevice(self.audio_dev, 1)
                except Exception:
                    pass
        else:
            self.paused = False
            self._last_pump_ms = None    # do not count the pause window
            if self.audio_dev is not None:
                try:
                    SDL_PauseAudioDevice(self.audio_dev, 0)
                except Exception:
                    pass

    def seek(self, target):
        """Absolute seek (seconds) - relaunches ffmpeg at the new position.

        v3.2: COALESCED. A seek costs a full ffmpeg relaunch (seconds on a
        network input); rapid seek events used to relaunch it several
        times per second (the log showed two launches inside one second
        and five inside three). Events arriving inside the cooldown kill
        the current decode immediately but only UPDATE the pending target;
        pump() performs a single relaunch once the cooldown expires.

        v3.3: live streams reject all seeks - the rolling HLS window is
        not seekable and a -ss relaunch just errors out."""
        if not self.video_url:
            return
        if self.is_live:
            return
        target = max(0.0, float(target))
        if self.duration and target >= self.duration - 1.0:
            target = max(0.0, self.duration - 1.5)
        now = SDL_GetTicks()
        if self._last_spawn_ms is not None and \
                now - self._last_spawn_ms < SEEK_COOLDOWN_MS:
            # too soon after the last (re)launch: just remember the newest
            # target. The current decode keeps running (killing + rejoining
            # the reader threads on every tap froze the UI for up to a
            # second); pump() performs ONE relaunch when the cooldown
            # expires. self.position jumps optimistically to the pending
            # target so the progress bar moves instantly and repeated
            # relative seeks (tap +10 five times) accumulate exactly.
            self._seek_deferred = target
            self.position = target
            self.seek_pending = True
            return
        self._do_seek(target)

    def _do_seek(self, target):
        """Perform the actual relaunch (rate limiting already handled)."""
        if not self.video_url:
            return
        target = max(0.0, float(target))
        if self.duration and target >= self.duration - 1.0:
            target = max(0.0, self.duration - 1.5)
        was_paused = self.paused
        self._kill_proc()
        self.frames_shown = 0
        self.frames_dropped = 0
        self._frame_decode_times = []
        self._frame_idx = 0
        self._held = None
        self._late_pending = False
        self._last_data_ms = None
        if self.audio_dev is not None:
            try:
                SDL_ClearQueuedAudio(self.audio_dev)
            except Exception:
                pass
        self._spawn(target)
        self.paused = was_paused
        if was_paused and self.audio_dev is not None:
            try:
                SDL_PauseAudioDevice(self.audio_dev, 1)
            except Exception:
                pass

    def set_speed(self, speed):
        if self.is_live:
            return          # live: no timestamps to rebase, keep 1.0x
        speed = float(speed)
        if speed < 0.25:
            speed = 0.25
        self.speed = speed
        self.seek(self.position)

    def set_volume(self, volume):
        self.volume = int(max(0, min(100, volume)))

    def set_inputs(self, video_url, audio_url, width, height, fps,
                   audio_in_video=False):
        """Switch to a different quality (new URLs) keeping the position.

        v3.2: relaunches IMMEDIATELY (no seek-coalescing deferral). The old
        stream's frames have a different byte size than the new texture -
        showing one through the other overreads the frame buffer - and a
        quality switch is a single deliberate action, not rapid tapping."""
        self.video_url = video_url
        self.audio_url = audio_url
        self.has_audio = bool(audio_url)
        # v3.4: quality/codec switches can flip between a paired video+audio
        # selection and a muxed single-input one (live streams)
        self.audio_in_video = bool(audio_in_video)
        if width and height:
            self.src_width = max(2, int(width))
            self.src_height = max(2, int(height))
            self._apply_size()
        if fps:
            self.fps = float(fps)
        self.texture = None       # caller recreates it at the new size
        self.last_frame = None    # old-size frames must never hit the new texture
        self._seek_deferred = None
        # v3.3: a live quality/codec switch relaunches at the LIVE EDGE
        # (the previous position is not an HLS-seekable spot)
        self._do_seek(0.0 if self.is_live else max(0.0, self.position))

    def stop(self):
        self.ended = True
        self._kill_proc()

    def _kill_proc(self):
        proc = self.proc
        self.proc = None
        threads = self._threads
        self._threads = []
        if proc is not None:
            try:
                proc.terminate()
            except Exception:
                pass
            try:
                proc.wait(timeout=0.6)
            except Exception:
                try:
                    proc.kill()
                except Exception:
                    pass
        # v3.2: WAIT for the old reader threads to see EOF and exit BEFORE
        # the fds are closed and (potentially) reused by the next spawn. A
        # reader still parked on a recycled fd number could otherwise steal
        # bytes from the NEW pipe - permanently misaligned frames, i.e. the
        # "colors garble when the video is opened again" bug. After ffmpeg
        # dies the readers hit EOF within their 0.25 s put-timeout, so this
        # join is normally instant.
        for t in threads:
            try:
                if t is not None and t.is_alive():
                    t.join(timeout=0.5)
            except Exception:
                pass
        # closing pipes + stderr unblocks anything that still lingers
        for pipe in (self._pipe_v, self._pipe_a):
            if pipe:
                try:
                    os.close(pipe[0])
                except OSError:
                    pass
        self._pipe_v = self._pipe_a = None
        try:
            if proc is not None and proc.stderr:
                proc.stderr.close()
        except Exception:
            pass

    def buffered_ahead(self):
        """Rough estimate of decoded-ahead seconds (for the progress bar)."""
        ahead = 0.0
        if self._video_q is not None:
            ahead += self._video_q.qsize() / max(1.0, self.fps)
        with self._lock:
            ahead += self._pending_audio_bytes / float(AUDIO_BYTES_PER_SEC)
        # audio already handed to the device but not yet consumed by the
        # clock (submission is allowed to lead the clock by up to
        # AUDIO_LEAD_SECONDS)
        ahead += max(0.0, self._audio_submitted /
                     float(AUDIO_BYTES_PER_SEC) - self._clock_accum)
        return ahead

    def is_buffering(self):
        if self.failed:
            return False
        if self.paused or self.ended:
            return False
        if self.seek_pending:
            return True
        if self.last_frame is None:
            return True
        if self.starving:
            return True
        # stalled: no decoded data for a while while the decoder lives
        # (v3.2: with -re the queues are legitimately near-empty at all
        # times, so emptiness alone must NOT read as buffering)
        if self._last_data_ms is not None and not self._proc_dead():
            if SDL_GetTicks() - self._last_data_ms > 2500:
                return True
        return False



class PlayerMixin(object):
    """Playback engine control, player screen, HUD, queue.
    Hosted by PilasTubeApp; all state lives on self."""
    # =====================================================================
    # PLAYBACK ENGINE
    # =====================================================================
    def play_video(self, video, start_pos=None):
        if not self.ytdlp_path:
            self.set_status(self.t("msg_no_ytdlp"), "error")
            return
        # Knulli / Miyoo Flip fix: if built-in ffmpeg player is available, external player is not required
        if not self.video_player and not USE_BUILTIN_PLAYER:
            self.set_status(self.t("msg_no_player"), "error")
            return

        self.add_to_history(video)
        self.current_video = video
        self.is_loading_video = True
        self.user_stopped = False
        self._skip_to_next = False
        self._restart_requested = False
        self.sb_skipped_ids = set()
        self.current_segments = []
        self.current_chapters = []
        self.last_time_pos = 0.0
        self.last_duration = 0.0
        self.loading_ryd = None
        self.next_info = None
        self.set_status(self.t("msg_loading_video"), "loading")
        self.render_loading_screen(self.t("msg_loading_video"),
                                   self.display_title(video))

        # remember speed preference
        if self.prefs.get("speed_memory", "On") == "On":
            try:
                self.current_speed = float(self.prefs.get("last_speed", "1.0"))
            except ValueError:
                self.current_speed = 1.0
        else:
            self.current_speed = 1.0

        # sleep timer
        st = self.prefs.get("sleep_timer", "Off")
        self.sleep_deadline = None
        if st not in ("Off", ""):
            try:
                self.sleep_deadline = time.time() + int(st) * 60
            except ValueError:
                self.sleep_deadline = None

        quality = self.session_quality or self.prefs.get("quality", "Auto")
        codec = self.session_codec or self.prefs.get("video_codec", "Auto")

        def worker():
            video_url = None
            audio_url = None
            info = {}
            sub_path = None
            chapters_path = None
            try:
                # v3.6: while offline, queue the playback instead of timing
                # out - the watchdog restarts it when the network returns
                if self.net_offline:
                    self.is_loading_video = False
                    self._net_pending = lambda: self.play_video(
                        video, start_pos)
                    self.set_status(self.t("msg_reconnecting"), "error")
                    return
                # --- 1. full metadata (formats + chapters + subtitles) ---
                args = self._ytdlp_args(for_video=True) + [
                    "--no-playlist", "--dump-single-json", video.url]
                result = self._run_ytdlp(args, timeout=60)
                if result.returncode != 0 or not (result.stdout or "").strip():
                    raise RuntimeError("metadata failed")
                info = json.loads(result.stdout.strip().split("\n")[0])

                video_url, audio_url, height, note = YX.select_formats(
                    info, quality, codec, ffmpeg_path=FFMPEG_PATH,
                    audio_lang=self._current_audio_lang())
                self.next_info = (self.display_title(video), height, note)

                # --- fallback to classic -g if nothing usable ---
                if not video_url:
                    cap = YX.quality_cap(quality)
                    args = self._ytdlp_args(for_video=True) + [
                        "-f", "best[height<=%d]/best" % cap,
                        "-g", "--no-playlist", video.url]
                    result2 = self._run_ytdlp(args, timeout=45)
                    lines = [l for l in (result2.stdout or "").strip().split("\n") if l.strip()]
                    if lines:
                        video_url = lines[0]
                        audio_url = lines[1] if len(lines) > 1 else None

                if not video_url:
                    self.is_loading_video = False
                    self.set_status("Failed to get URL", "error")
                    return

                # --- resume position ---
                # v3.2: clamp hard against a stale/corrupt entry - positions
                # saved by the old racing clock sit near the end of the
                # video and made a re-opened video start "broken" at the
                # credits with seconds left on the clock.
                # v3.3: live streams never resume - the HLS window rolls.
                resume_at = 0.0
                live_now = bool(video.is_live) or bool(info.get("is_live")) or \
                    info.get("live_status") == "is_live"
                if live_now:
                    resume_at = 0.0
                    self.positions.pop(video.id, None)
                elif start_pos is None:
                    pos = self.get_position(video.id)
                    if pos and pos[0] > 30:
                        dur = info.get("duration") or pos[1] or 0
                        if dur and pos[0] > dur - 25.0:
                            # saved position is in the final 25 s - treat
                            # the video as finished, start clean
                            self.positions.pop(video.id, None)
                            self._save_positions()
                        elif not dur or pos[0] < dur * 0.95:
                            resume_at = pos[0]
                else:
                    resume_at = float(start_pos)
                    if info.get("duration"):
                        dur = float(info.get("duration"))
                        if dur and resume_at > dur - 25.0:
                            resume_at = max(0.0, dur - 25.0)
                if info.get("duration"):
                    self.last_duration = float(info.get("duration"))

                # --- chapters ---
                self.current_chapters = info.get("chapters") or []
                if self.current_chapters and PLAYER_IS_MPV:
                    chapters_path = "/tmp/yt_chapters_%d.xml" % os.getpid()
                    YX.build_chapters_xml(self.current_chapters, chapters_path)

                # --- subtitles ---
                want_subs = PLAYER_IS_MPV or USE_BUILTIN_PLAYER
                if want_subs:
                    sub_pref = self.prefs.get("subtitles", "Auto")
                    if sub_pref == "Auto":
                        sub_pref = YX.SUB_LANG_MAP.get(
                            self.prefs.get("language", "English")) or "Auto"
                    if sub_pref and sub_pref != "Off":
                        sub_path = "/tmp/yt_sub_%d.vtt" % os.getpid()
                        if not YX.pick_subtitle(info, sub_pref, sub_path,
                                                self.prefs):
                            sub_path = None
                        elif USE_BUILTIN_PLAYER:
                            # ffmpeg's subtitles filter needs srt/ass -
                            # convert the vtt in place
                            srt_path = sub_path.rsplit(".", 1)[0] + ".srt"
                            if self._vtt_to_srt(sub_path, srt_path):
                                try:
                                    os.remove(sub_path)
                                except OSError:
                                    pass
                                sub_path = srt_path
                            else:
                                sub_path = None

                self.is_loading_video = False
                self._launch_player(video, video_url, audio_url, resume_at,
                                    sub_path, chapters_path, info)
                if not live_now and audio_url is None:
                    LOG("WARN: no audio format selected - video may be "
                        "silent (check [PLAYER] format lines)", "PLAYER")

            except subprocess.TimeoutExpired as e:
                self.is_loading_video = False
                if self._net_fail(e, lambda: self.play_video(
                        video, start_pos)):
                    return
                self.set_status(self.t("msg_timeout"), "error")
            except Exception as e:
                print("Play error: %s" % e)
                self.is_loading_video = False
                if self._net_fail(e, lambda: self.play_video(
                        video, start_pos)):
                    return
                self.set_status("Error: %s" % str(e)[:24], "error")

        run_logged_thread("video-load", worker)

    def _launch_player(self, video, video_url, audio_url, resume_at,
                       sub_path, chapters_path, info):
        if USE_BUILTIN_PLAYER:
            self._start_builtin_player(video, video_url, audio_url,
                                       resume_at, sub_path, info)
            return
        self._launch_player_external(video, video_url, audio_url, resume_at,
                                     sub_path, chapters_path, info)

    # ------------------------------------------------------------ audio dev
    def _open_audio_device(self):
        """Open the SDL audio device once for the whole session.

        Running as the regular console user this reaches PulseAudio /
        PipeWire through $XDG_RUNTIME_DIR - which is exactly what v2.2 could
        NOT do as root ("XDG_RUNTIME_DIR is not owned by us (uid 0)").
        """
        if self.audio_dev is not None or self.audio_dev == 0:
            return self.audio_dev
        try:
            # SDL_OpenAudioDevice needs the audio subsystem initialised
            try:
                if sdl2.SDL_WasInit(sdl2.SDL_INIT_AUDIO) == 0:
                    rc = sdl2.SDL_InitSubSystem(sdl2.SDL_INIT_AUDIO)
                    if rc != 0:
                        LOG("SDL_InitSubSystem(audio) failed: %s" % _sdl_err(),
                            "AUDIO")
            except Exception as _e:
                LOG("SDL_InitSubSystem(audio) exception: %s" % _e, "AUDIO")
            want = sdl2.SDL_AudioSpec(AUDIO_RATE, sdl2.AUDIO_S16LSB,
                                       AUDIO_CHANNELS, 1024)
            # note: do NOT assign want.callback = None (pysdl2 raises
            # TypeError - the field wants a CFunctionType). A zeroed
            # SDL_AudioSpec already has callback == NULL, which is exactly
            # what SDL_QueueAudio needs.
            obtained = sdl2.SDL_AudioSpec(0, 0, 0, 0)
            dev = sdl2.SDL_OpenAudioDevice(None, 0, want, obtained, 0)
            if dev == 0:
                LOG("audio device open failed: %s" % _sdl_err(), "AUDIO")
                # retry: 44.1 kHz in case 48 kHz is unsupported
                want = sdl2.SDL_AudioSpec(44100, sdl2.AUDIO_S16LSB,
                                           AUDIO_CHANNELS, 1024)
                obtained = sdl2.SDL_AudioSpec(0, 0, 0, 0)
                dev = sdl2.SDL_OpenAudioDevice(None, 0, want, obtained, 0)
            if dev == 0:
                LOG("audio unavailable - video will be silent: %s" %
                    _sdl_err(), "AUDIO")
                self.audio_driver_ok = False
                self.audio_dev = None
                return None
            self.audio_dev = dev
            try:
                drv = sdl2.SDL_GetCurrentAudioDriver()
                drv_s = drv.decode() if drv else "?"
            except Exception:
                drv_s = "?"
            LOG("audio device open (id %s, driver %s)" % (dev, drv_s),
                "AUDIO")
            SDL_PauseAudioDevice(dev, 0)
            return dev
        except Exception as e:
            LOG("audio device exception: %s" % e, "AUDIO")
            self.audio_driver_ok = False
            self.audio_dev = None
            return None

    def _close_audio_device(self):
        if self.audio_dev is not None:
            try:
                sdl2.SDL_CloseAudioDevice(self.audio_dev)
            except Exception:
                pass
        self.audio_dev = None

    # ------------------------------------------------------- builtin player
    def _start_builtin_player(self, video, video_url, audio_url,
                              resume_at, sub_path, info):
        """v3.0: everything stays inside this one SDL process."""
        # remember formats so quality can switch without re-fetching
        self.play_info = info or {}
        fmt = None
        for f in (self.play_info.get("formats") or []):
            if f.get("url") == video_url:
                fmt = f
                break
        self.player_hw = (int((fmt or {}).get("width") or 0) or 640,
                          int((fmt or {}).get("height") or 0) or 360)
        self.player_fps = float((fmt or {}).get("fps") or 0) or \
            float(self.play_info.get("fps") or 0) or 30.0
        if self.play_info.get("duration"):
            self.last_duration = float(self.play_info.get("duration"))

        if sub_path and not self._ffmpeg_has_subtitles():
            LOG("device ffmpeg lacks the subtitles filter - "
                "captions disabled for this playback", "PLAYER")
            sub_path = None

        audio_dev = self._open_audio_device()
        if audio_dev is None and not self._player_audio_warned:
            self._player_audio_warned = True
            LOG("WARN: no audio device - check that the app runs as the "
                "console user (not root) and that PulseAudio/PipeWire is "
                "up. See [AUDIO] lines above.", "AUDIO")

        try:
            self.player = FFPlayer(
                FFMPEG_PATH, self.renderer, video_url, audio_url,
                self.player_hw[0], self.player_hw[1], self.player_fps,
                start_pos=resume_at, speed=self.current_speed,
                sub_file=sub_path,
                route=self.prefs.get("route", "Default"),
                is_live=bool(getattr(video, "is_live", False)) or
                bool(self.play_info.get("is_live")) or
                self.play_info.get("live_status") == "is_live",
                audio_in_video=bool(
                    self.play_info.get("_pilastube_muxed_video")))
            self.player.duration = self.last_duration
            self.player.volume = self.player_volume_pct
        except Exception as e:
            LOG("FFPlayer init error: %s" % e, "PLAYER")
            self.set_status("Player error: %s" % str(e)[:24], "error")
            self.is_loading_video = False
            return

        self.player.start(audio_dev)
        self.is_playing = True
        self.player_paused = False
        self.player_start_pos = float(resume_at or 0.0)
        self._player_started_at = SDL_GetTicks()
        self.hud_visible = True
        self.hud_last_activity = SDL_GetTicks()
        self.player_menu = None
        self.player_stats = False
        self.player_loop = (self.prefs.get("playback_mode", "Normal")
                            == "Repeat One")
        self.autoplay_countdown = None
        self.player_toast = None
        self._sb_last_shown = 0.0
        if self.player_start_pos > 5:
            self._player_toast("%s %s" % (self.t("msg_resuming"),
                                          fmt_clock(self.player_start_pos)))
        LOG("built-in player started: %s | %dx%d@%.0f | audio=%s%s" %
            (self.display_title(video)[:48], self.player_hw[0],
             self.player_hw[1], self.player_fps,
             "yes" if audio_url else "NO AUDIO TRACK",
             " | LIVE" if self.player.is_live else ""), "PLAYER")
        SLOG("Playing: %s" % self.display_title(video)[:80])

        # SponsorBlock + RYD fetch while playback starts
        run_logged_thread("play-extras", self._fetch_play_extras,
                          args=(video,))

    _ffmpeg_subtitles_probe = None

    def _ffmpeg_has_subtitles(self):
        if PilasTubeApp._ffmpeg_subtitles_probe is None:
            ok = False
            try:
                result = subprocess.run(
                    [FFMPEG_PATH, "-hide_banner", "-filters"],
                    stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                    universal_newlines=True, timeout=10)
                ok = "subtitles" in (result.stdout or "")
            except Exception:
                ok = False
            PilasTubeApp._ffmpeg_subtitles_probe = ok
            LOG("ffmpeg subtitles filter: %s" % ("yes" if ok else "no"),
                "PLAYER")
        return PilasTubeApp._ffmpeg_subtitles_probe

    # ------------------------------------------------- legacy external path
    def _launch_player_external(self, video, video_url, audio_url,
                                resume_at, sub_path, chapters_path, info):
        """Fallback for firmwares without an ffmpeg binary.

        v3.0 fix: a KMSDRM display has exactly ONE master. The old code
        only hid our window while ffplay owned the display, and after it
        exited our pageflips failed forever (pageflip -16, black screen).
        Now the whole SDL *video subsystem* is torn down first and rebuilt
        afterwards, so the external player truly owns the display while it
        runs and we truly own it again afterwards.
        """
        player = self.video_player
        player_name = os.path.basename(player) if player else ""
        self.mpv_socket = "/tmp/mpv_%d" % os.getpid()

        if player_name == "mpv":
            cmd = [
                player, "--fs", "--no-terminal", "--really-quiet",
                "--input-ipc-server=%s" % self.mpv_socket,
                "--osd-level=1", "--osd-duration=1500",
                "--osd-font-size=32",
                "--cache=yes", "--demuxer-max-bytes=50M",
                "--keep-open=no",
            ]
            if self.prefs.get("hwdec", "On") == "On":
                cmd += ["--hwdec=auto"]
            if self.prefs.get("volume_boost", "Off") == "On":
                cmd += ["--softvol-max=130", "--volume=100"]
            if resume_at > 0:
                cmd += ["--start=+%f" % resume_at]
            if self.current_speed and self.current_speed != 1.0:
                cmd += ["--speed=%s" % self.current_speed]
            if sub_path:
                cmd += ["--sub-file=%s" % sub_path, "--sub-font-size=30"]
            if chapters_path:
                cmd += ["--chapters-file=%s" % chapters_path]
            if audio_url:
                cmd += ["--audio-file=%s" % audio_url]
            cmd.append(video_url)
        elif player_name == "ffplay":
            # v3.0: hand ffplay BOTH streams - v2.2 passed only the
            # video-only URL which is one of the two "no sound" causes.
            cmd = [player, "-fs", "-autoexit", "-loglevel", "quiet"]
            if resume_at > 0:
                cmd += ["-ss", "%f" % resume_at]
            if audio_url:
                cmd += ["-i", video_url, "-i", audio_url,
                        "-map", "0:v:0", "-map", "1:a:0"]
            else:
                cmd.append(video_url)
        elif player_name == "vlc":
            cmd = [player, "--fullscreen", "--play-and-exit", "-q"]
            if resume_at > 0:
                cmd += ["--start-time=%d" % int(resume_at)]
            cmd.append(video_url)
        else:
            cmd = [player, video_url]

        self._sdl_video_suspend()

        try:
            self.player_process = subprocess.Popen(
                cmd, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE,
                universal_newlines=True)
        except Exception as e:
            LOG("player launch error: %s" % e, "PLAYER")
            print("player launch error: %s" % e)
            self._sdl_video_resume()
            self._finish_playback(video, sub_path, chapters_path)
            return

        self.is_playing = True
        self.player_paused = False

        # keep the player's stderr flowing into the detailed log so that
        # playback problems on the device are diagnosable
        if self.player_process.stderr:
            run_logged_thread("player-stderr", self._drain_player_stderr,
                              args=(self.player_process.stderr,),
                              daemon=True)
        LOG("player launched: %s (pid %s)" %
            (" ".join(str(c) for c in cmd[:6]) + "...",
             getattr(self.player_process, "pid", "?")), "PLAYER")
        SLOG("Playing: %s" % self.display_title(video)[:80])

        # SponsorBlock + RYD fetch while playback starts
        if PLAYER_IS_MPV:
            run_logged_thread("play-extras", self._fetch_play_extras,
                              args=(video,))

        # monitor thread: position tracking, SponsorBlock skipping, sleep timer
        self.monitor_thread = run_logged_thread(
            "player-monitor", self._player_monitor,
            args=(video, sub_path, chapters_path))

        self.player_process.wait()
        self._sdl_video_resume()
        self._finish_playback(video, sub_path, chapters_path)

    # ------------------------------------------- SDL video suspend / resume
    def _sdl_video_suspend(self):
        """Release the display so an external player can own it (KMSDRM)."""
        try:
            for cache in (self.text_cache, self.image_cache):
                for tex, _, _ in cache.values():
                    if tex:
                        SDL_DestroyTexture(tex)
                cache.clear()
            if getattr(self, "player", None) and self.player.texture:
                SDL_DestroyTexture(self.player.texture)
                self.player.texture = None
            self.renderer = self.renderer      # keep reference for typing
            if self.renderer:
                SDL_DestroyRenderer(self.renderer)
                self.renderer = None
            if self.window:
                SDL_DestroyWindow(self.window)
                self.window = None
            sdl2.SDL_QuitSubSystem(sdl2.SDL_INIT_VIDEO)
            LOG("SDL video suspended (display released)", "SDL")
        except Exception as e:
            LOG("SDL video suspend error: %s" % e, "SDL")

    def _sdl_video_resume(self):
        """Re-acquire the display after an external player exited."""
        try:
            rc = sdl2.SDL_InitSubSystem(sdl2.SDL_INIT_VIDEO)
            if rc != 0:
                LOG("SDL_InitSubSystem(video) failed: %s" % _sdl_err(),
                    "SDL")
            # v0.3.9: rebuild the window at the NATIVE size (v0.3.7's
            # proven flags=0 + CENTERED call, just at WINDOW_WIDTH/HEIGHT
            # so big panels keep the full-screen canvas).
            self.window = SDL_CreateWindow(
                b"PilasTube", SDL_WINDOWPOS_CENTERED, SDL_WINDOWPOS_CENTERED,
                WINDOW_WIDTH, WINDOW_HEIGHT, 0)
            self.renderer = SDL_CreateRenderer(
                self.window, -1,
                SDL_RENDERER_ACCELERATED | SDL_RENDERER_PRESENTVSYNC)
            if not self.renderer:
                self.renderer = SDL_CreateRenderer(
                    self.window, -1, SDL_RENDERER_ACCELERATED)
            if not self.renderer:
                self.renderer = SDL_CreateRenderer(
                    self.window, -1, SDL_RENDERER_SOFTWARE)
            if self.renderer:
                SDL_SetRenderDrawBlendMode(self.renderer, SDL_BLENDMODE_BLEND)
                # v0.3.9: v0.3.8 lost the logical-size mapping here -
                # after an external player exited, big-panel UIs rendered
                # 1:1 (wrong scale) until restart. Re-apply it exactly
                # like at startup (no-op on identity/640x480 devices).
                apply_logical_mapping(self.renderer)
            # caches were cleared on suspend - force a full redraw
            self.text_cache = {}
            self.image_cache = {}
            self.need_redraw = True
            LOG("SDL video resumed (window + renderer rebuilt)", "SDL")
        except Exception as e:
            LOG("SDL video resume error: %s" % e, "SDL")

    def _fetch_play_extras(self, video):
        if self.sponsorblock.get_categories():
            segs = self.sponsorblock.fetch_segments(video.id)
            self.current_segments = segs
        if self.prefs.get("ryd", "On") == "On":
            votes = self.ryd.fetch_votes(video.id)
            if votes:
                likes = votes.get("likes", 0)
                dislikes = votes.get("dislikes", 0)
                self.loading_ryd = "+%s / -%s" % (
                    self._short_num(likes), self._short_num(dislikes))

    @staticmethod
    def _short_num(n):
        try:
            n = int(n)
        except (TypeError, ValueError):
            return "0"
        if n >= 1000000:
            return "%.1fM" % (n / 1000000.0)
        if n >= 1000:
            return "%.1fK" % (n / 1000.0)
        return str(n)

    def _player_monitor(self, video, sub_path, chapters_path):
        """Runs while mpv is alive: track position, skip sponsor segments."""
        last_save = 0.0
        while self.is_playing and self.player_process and \
                self.player_process.poll() is None:
            pos = self.mpv_query("time-pos") if PLAYER_IS_MPV else None
            dur = self.mpv_query("duration") if PLAYER_IS_MPV else None
            if pos is not None and pos >= 0:
                self.last_time_pos = float(pos)
            if dur is not None and dur > 0:
                self.last_duration = float(dur)

            # SponsorBlock auto-skip
            if pos is not None and self.current_segments:
                for i, seg in enumerate(self.current_segments):
                    if i in self.sb_skipped_ids:
                        continue
                    if seg["start"] <= pos < seg["end"] - 0.4:
                        self.send_mpv_command(["seek", "%f" % seg["end"], "absolute"])
                        self.send_mpv_command([
                            "show-text",
                            "%s %s" % (self.t("msg_skipped"), seg["label"]), 2000])
                        self.sb_skipped_ids.add(i)
                        self.last_time_pos = seg["end"]
                        break

            # periodic position save
            now = time.time()
            if now - last_save > 10:
                last_save = now
                if self.last_time_pos > 5:
                    self.save_position(video.id, self.last_time_pos,
                                       self.last_duration)
                # sleep timer
                if self.sleep_deadline and now > self.sleep_deadline:
                    self.send_mpv_command(["show-text", "Sleep timer", 1500])
                    time.sleep(1.5)
                    self.user_stopped = True
                    try:
                        self.player_process.terminate()
                    except Exception:
                        pass
                    return
            time.sleep(1.0)

    def _drain_player_stderr(self, stream):
        """Read the video player's stderr into the detailed log until EOF."""
        try:
            for line in stream:
                line = (line or "").rstrip()
                if line:
                    LOG("player: %s" % line[:300], "PLAYER")
        except Exception:
            pass

    def _finish_playback(self, video, sub_path, chapters_path):
        """External-player path: player process already exited."""
        LOG("playback finished: %s (pos %.0fs)" %
            (self.display_title(video)[:60], self.last_time_pos), "PLAYER")
        # save final position
        if self.last_time_pos > 5:
            self.save_position(video.id, self.last_time_pos, self.last_duration)
        self.subs.mark_seen([video.id])
        for p in (sub_path, chapters_path):
            try:
                if p and os.path.exists(p):
                    os.remove(p)
            except Exception:
                pass
        try:
            if self.mpv_socket and os.path.exists(self.mpv_socket):
                os.remove(self.mpv_socket)
        except Exception:
            pass

        was_restart = self._restart_requested
        skip_next = self._skip_to_next
        self.is_playing = False
        self.player_process = None
        self.player_paused = False

        if was_restart:
            # quality changed mid-playback: relaunch with new quality
            self._restart_requested = False
            start = self.last_time_pos
            self.play_video(video, start_pos=start)
            return

        # app shutting down: no UI / no auto-advance
        if not self.running:
            return

        if self.window:
            SDL_ShowWindow(self.window)
            SDL_RaiseWindow(self.window)

        # user pressed stop (or sleep timer fired): never auto-advance
        if self.user_stopped:
            self.current_video = None
            self.set_status("Stopped")
            return

        if skip_next:
            self._skip_to_next = False
            self._advance_playback()
            return

        mode = self.prefs.get("playback_mode", "Normal")
        if mode != "Normal":
            self._advance_playback()
        else:
            self.current_video = None
            self.set_status("Ready")

    # -------------------------------------------------- builtin player glue
    def _vtt_to_srt(self, vtt_path, srt_path):
        """Convert a WebVTT subtitle file to SubRip for ffmpeg burn-in."""
        try:
            import re as _re
            with open(vtt_path, "r", encoding="utf-8", errors="replace") \
                    as fh:
                text = fh.read()
            text = text.replace("\r\n", "\n")
            blocks = []
            time_rx = _re.compile(
                r"(\d+):(\d+):(\d+)\.(\d+)\s+-->\s+(\d+):(\d+):(\d+)\.(\d+)")
            for chunk in text.split("\n\n"):
                m = time_rx.search(chunk)
                if not m:
                    continue
                g = [int(x) for x in m.groups()]
                start = "%02d:%02d:%02d,%03d" % (g[0], g[1], g[2], g[3])
                end = "%02d:%02d:%02d,%03d" % (g[4], g[5], g[6], g[7])
                lines = [l for l in chunk.split("\n")
                         if l.strip() and not time_rx.search(l)
                         and not l.strip().isdigit()
                         and not l.startswith("WEBVTT")
                         and "-->" not in l]
                if lines:
                    blocks.append("%d\n%s --> %s\n%s\n" %
                                  (len(blocks) + 1, start, end,
                                   "\n".join(lines)))
            if not blocks:
                return False
            with open(srt_path, "w", encoding="utf-8") as fh:
                fh.write("\n".join(blocks))
            return True
        except Exception as e:
            LOG("vtt->srt error: %s" % e, "PLAYER")
            return False

    def _player_toast(self, text, color=None, ms=1800):
        self.player_toast = (str(text), SDL_GetTicks() + ms,
                             color or self.C.TEXT_PRIMARY)

    def _player_hud_toggle(self):
        """DOWN in the player: show / hide the SmartTube-style HUD.

        When showing, the focus lands on the play/pause button of the
        options row (SmartTube's default)."""
        self.hud_visible = not self.hud_visible
        self.hud_last_activity = SDL_GetTicks()
        if self.hud_visible:
            self.hud_focus = self._hud_default_focus()
        self.player_menu = None

    def _hud_default_focus(self):
        player = self.player
        buttons = self._player_buttons(player) if player else []
        for i, b in enumerate(buttons):
            if b[0] in ("play", "pause"):
                return i
        return 0

    def _builtin_teardown(self):
        """Stop the FFPlayer and clean per-video player state."""
        player = self.player
        self.player = None
        self.is_playing = False
        self.player_paused = False
        self.player_menu = None
        self.autoplay_countdown = None
        self.hud_visible = True
        if player is not None:
            try:
                if self.last_time_pos <= 0 and player.position > 0:
                    self.last_time_pos = player.position
                player.stop()
            except Exception:
                pass
            for p in (getattr(player, "sub_file", None),):
                try:
                    if p and os.path.exists(p):
                        os.remove(p)
                except Exception:
                    pass
            if player.texture:
                try:
                    SDL_DestroyTexture(player.texture)
                except Exception:
                    pass
                player.texture = None

    def _next_video_candidate(self):
        """The video that auto-advance would pick (for the countdown)."""
        mode = self.prefs.get("playback_mode", "Normal")
        video = self.current_video
        if self.queue:
            return self.queue[0]
        if mode in ("Autoplay", "Shuffle"):
            videos = self._get_filtered_list()
            if not videos:
                return None
            if mode == "Shuffle":
                import random
                candidates = [v for v in videos if (not video or v.id != video.id)]
                return candidates[0] if candidates else None
            idx = -1
            if video:
                for i, v in enumerate(videos):
                    if v.id == video.id:
                        idx = i
                        break
            if 0 <= idx + 1 < len(videos):
                return videos[idx + 1]
        return None

    def _builtin_playback_done(self):
        """The FFPlayer hit end-of-stream (or failed)."""
        player = self.player
        video = self.current_video
        failed = bool(player and player.failed)
        if player:
            self.last_time_pos = max(self.last_time_pos, player.position)
        LOG("playback finished (built-in): %s (pos %.0fs%s)" %
            (self.display_title(video)[:60] if video else "?",
             self.last_time_pos, " FAILED" if failed else ""), "PLAYER")

        # save final position + mark seen
        if video:
            if self.last_time_pos > 5 and self.last_duration and \
                    self.last_time_pos < self.last_duration * 0.95:
                self.save_position(video.id, self.last_time_pos,
                                   self.last_duration)
            else:
                self.save_position(video.id, 0, self.last_duration)
            self.subs.mark_seen([video.id])

        self._builtin_teardown()

        if not self.running:
            return

        if failed:
            self.current_video = None
            self.set_status("Playback error - see logs", "error")
            return

        # loop the same video (Repeat One / loop toggle)
        if (self.player_loop or
                self.prefs.get("playback_mode", "Normal") == "Repeat One") \
                and video:
            self.play_video(video, start_pos=0)
            return

        # SmartTube-style autoplay countdown when something is queued next
        nxt = self._next_video_candidate()
        if nxt is not None and not self.user_stopped:
            self.autoplay_countdown = (nxt, SDL_GetTicks() + 5000)
            self.hud_visible = True
            self.need_redraw = True
            return

        if self._skip_to_next:
            self._skip_to_next = False
            self._advance_playback()
            return

        self.current_video = None
        self.set_status("Ready")
        self.need_redraw = True

    # ----------------------------------------------------------------- next
    def _advance_playback(self):
        video = self.current_video
        mode = self.prefs.get("playback_mode", "Normal")

        if mode == "Repeat One" and video:
            self.set_status("%s: %s" % (self.t("msg_next"), video.title[:30]))
            self.play_video(video)
            return
        if self.queue:
            nxt = self.queue.pop(0)
            self.set_status("%s: %s" % (self.t("msg_next"), nxt.title[:30]))
            self.play_video(nxt)
            return
        if mode in ("Autoplay", "Shuffle"):
            videos = self._get_filtered_list()
            if not videos:
                self.current_video = None
                self.set_status("Ready")
                return
            if mode == "Shuffle":
                import random
                candidates = [v for v in videos if (not video or v.id != video.id)]
                if candidates:
                    nxt = random.choice(candidates)
                else:
                    self.current_video = None
                    self.set_status("Ready")
                    return
            else:
                idx = -1
                if video:
                    for i, v in enumerate(videos):
                        if v.id == video.id:
                            idx = i
                            break
                if idx + 1 >= len(videos):
                    self.current_video = None
                    self.set_status("Ready")
                    return
                nxt = videos[idx + 1]
            self.set_status("%s: %s" % (self.t("msg_next"), nxt.title[:30]))
            self.play_video(nxt)
            return
        self.current_video = None
        self.set_status("Ready")

    # ---------------------------------------------------------- mpv control
    def send_mpv_command(self, command):
        if not self.is_playing or not self.mpv_socket:
            return False
        try:
            sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
            sock.settimeout(0.5)
            sock.connect(self.mpv_socket)
            sock.send((json.dumps({"command": command}) + "\n").encode())
            sock.close()
            return True
        except Exception:
            return False

    def mpv_query(self, prop):
        """Query an mpv property via IPC. Returns value or None."""
        if not self.is_playing or not self.mpv_socket:
            return None
        self.mpv_query_id += 1
        rid = self.mpv_query_id
        try:
            sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
            sock.settimeout(0.5)
            sock.connect(self.mpv_socket)
            sock.send((json.dumps({
                "command": ["get_property", prop], "request_id": rid}) + "\n").encode())
            data = b""
            while b"\n" not in data:
                chunk = sock.recv(1024)
                if not chunk:
                    break
                data += chunk
            sock.close()
            for line in data.decode("utf-8", "replace").split("\n"):
                line = line.strip()
                if not line:
                    continue
                try:
                    msg = json.loads(line)
                except ValueError:
                    continue
                if msg.get("request_id") == rid:
                    if msg.get("error") == "success":
                        return msg.get("data")
                    return None
            return None
        except Exception:
            return None

    # -------------------------------------------------------- player input
    def player_seek(self, seconds):
        """Relative seek in seconds."""
        if self.player is not None:
            if getattr(self.player, "is_live", False):
                # v3.3: live streams roll - seeking is meaningless
                self._player_toast(self.t("msg_live_no_seek"),
                                   self.C.TEXT_SECONDARY, 1200)
                return
            try:
                self.player.seek(self.player.position + seconds)
                self._player_toast(
                    "%+ds" % seconds, self.C.TEXT_PRIMARY, 1000)
            except Exception:
                pass
            return
        if self.is_playing:
            self.send_mpv_command(["seek", str(seconds), "relative"])

    def player_seek_absolute(self, target):
        if self.player is not None:
            if getattr(self.player, "is_live", False):
                self._player_toast(self.t("msg_live_no_seek"),
                                   self.C.TEXT_SECONDARY, 1200)
                return
            try:
                self.player.seek(target)
            except Exception:
                pass
            return
        if self.is_playing:
            self.send_mpv_command(["seek", "%f" % target, "absolute"])

    def player_toggle_pause(self):
        if self.player is not None:
            self.player.toggle_pause()
            self.player_paused = self.player.paused
            return
        if self.is_playing:
            self.player_paused = not self.player_paused
            self.send_mpv_command(["cycle", "pause"])

    def player_set_speed(self, speed):
        self.current_speed = speed
        if self.player is not None:
            if getattr(self.player, "is_live", False):
                # live: speed stays 1.0x (no rebaseable timestamps)
                self._player_toast(self.t("msg_live_no_seek"),
                                   self.C.TEXT_SECONDARY, 1200)
                self.current_speed = 1.0
                return
            self.player.set_speed(speed)
            self._player_toast("%sx" % speed, self.C.TEXT_PRIMARY, 1200)
        elif self.is_playing:
            self.send_mpv_command(["set_property", "speed", str(speed)])
            self.send_mpv_command(["show-text", "Speed: %sx" % speed, 1500])
        if self.prefs.get("speed_memory", "On") == "On":
            self.prefs.set("last_speed", str(speed), save=False)

    def player_speed_cycle(self):
        if not self.is_playing:
            return
        cur = self.current_speed
        steps = SPEED_STEPS
        idx = 0
        for i, s in enumerate(steps):
            if abs(s - cur) < 0.01:
                idx = i
                break
        self.player_set_speed(steps[(idx + 1) % len(steps)])

    def player_volume(self, delta):
        if self.player is not None:
            self.player_volume_pct = int(max(0, min(100,
                self.player_volume_pct + delta)))
            try:
                self.player.set_volume(self.player_volume_pct)
            except Exception:
                pass
            self._player_toast("%s %d%%" % (self.t("player_volume"),
                                           self.player_volume_pct),
                               self.C.TEXT_PRIMARY, 1000)
            return
        if not self.is_playing:
            return
        self.send_mpv_command(["add", "volume", str(delta)])
        vol = self.mpv_query("volume")
        if vol is not None:
            self.send_mpv_command(["show-text", "Volume: %d%%" % int(vol), 1200])

    def player_show_time(self):
        pos = self.last_time_pos
        dur = self.last_duration
        if dur and dur > 0:
            remain = max(0, int(dur - pos))
            txt = "%s / %s (-%s)" % (fmt_clock(pos), fmt_clock(dur),
                                     fmt_clock(remain))
        else:
            txt = fmt_clock(pos)
        if self.player is not None:
            self._player_toast(txt, self.C.TEXT_PRIMARY, 2000)
            return
        if self.is_playing:
            self.send_mpv_command(["show-text", txt, 2000])

    def player_chapter_seek(self, direction):
        if not self.is_playing or not self.current_chapters:
            return
        pos = self.last_time_pos
        marks = [float(c.get("start_time", 0) or 0) for c in self.current_chapters]
        target = None
        if direction > 0:
            for m in marks:
                if m > pos + 1:
                    target = m
                    break
        else:
            for m in reversed(marks):
                if m < pos - 3:
                    target = m
                    break
        if target is not None:
            self.player_seek_absolute(target)
            for c in self.current_chapters:
                if abs(float(c.get("start_time", 0) or 0) - target) < 0.5:
                    self._player_toast(c.get("title", "Chapter"),
                                       self.C.TEXT_PRIMARY, 1800)
                    break

    def _current_audio_lang(self):
        """The active audio track preference ('Original' or an ISO code).

        Accepts BOTH shapes: the preference stores the UI label
        ('Portugues'), the session override stores the code ('pt')."""
        lang = self.session_audio_lang or self.prefs.get("audio_lang",
                                                         "Original")
        if not lang or lang == "Original":
            return "Original"
        code = YX.AUDIO_LANG_MAP.get(lang)
        if code and code != "Original":
            return code
        # already a raw code ('pt', 'en-US') from a session override
        if 2 <= len(lang) <= 8 and "-" not in lang[:1]:
            return str(lang).lower()
        return "Original"

    def _available_audio_langs(self):
        """(code, label) audio languages offered by the CURRENT video.

        Live: the EXT-X-MEDIA renditions parsed from the master manifest.
        VOD: the language-tagged audio formats. Codes are normalised to
        their BASE language ('en-US' -> 'en' - matching is prefix-based
        anyway, and 'English' beats 'en-us' in the menu). Falls back to
        [('Original', 'Original')] when the video has a single track."""
        info = self.play_info or {}
        langs = info.get("_pilastube_audio_langs")
        if not langs:
            langs = YX.available_audio_languages(info)
        out = []
        seen = set()
        for code, label in (langs or []):
            c = str(code).lower().split("-")[0].split(".")[0]
            if c not in seen:
                seen.add(c)
                if c in ("original", ""):
                    # show WHICH language the original track speaks when
                    # known ("Original (Portugues)" beats a bare Original)
                    orig_name = LANG_NAMES.get(
                        str(label).lower().split("-")[0], "")
                    if orig_name and str(label).lower() not in ("", "original"):
                        out.append(("Original", "Original (%s)" % orig_name))
                    else:
                        out.append(("Original", "Original"))
                else:
                    out.append((c, LANG_NAMES.get(c, c)))
        if not out:
            out = [("Original", "Original")]
        return out

    def _audio_lang_label(self):
        cur = self._current_audio_lang()
        if cur == "Original":
            return "Original"
        return LANG_NAMES.get(cur, cur)

    def player_audio_lang_set(self, code):
        """v3.6: switch the audio track language live (SmartTube's audio
        picker). Multi-audio videos (auto-dubs) get their tracks re-picked
        and playback restarts on the new audio input."""
        if code not in ("Original",) and not code:
            return
        self.session_audio_lang = code
        if self.player is not None and self.play_info:
            quality = self.session_quality or self.prefs.get("quality",
                                                             "Auto")
            codec = self.session_codec or self.prefs.get("video_codec",
                                                         "Auto")
            video_url, audio_url, height, note = YX.select_formats(
                self.play_info, quality, codec, ffmpeg_path=FFMPEG_PATH,
                audio_lang=code)
            if not video_url:
                self._player_toast("%s ?" % code, self.C.STATUS_ERROR, 1200)
                return
            fmt = None
            for f in (self.play_info.get("formats") or []):
                if f.get("url") == video_url:
                    fmt = f
                    break
            w = int((fmt or {}).get("width") or 0) or self.player_hw[0]
            h = int((fmt or {}).get("height") or 0) or self.player_hw[1]
            fps = float((fmt or {}).get("fps") or 0) or self.player_fps
            self.player_hw = (w, h)
            self.player_fps = fps
            self.player.texture = None
            self.player.set_inputs(video_url, audio_url, w, h, fps,
                                   audio_in_video=bool(
                                       self.play_info.get(
                                           "_pilastube_muxed_video")))
            self._player_toast("%s: %s" % (self.t("player_audio_lang"),
                                           self._audio_lang_label()),
                               self.C.TEXT_PRIMARY, 1400)
            LOG("audio language switched to %s" % code, "PLAYER")
            return
        if self.is_playing:
            self._restart_requested = True
            try:
                self.player_process.terminate()
            except Exception:
                pass

    def player_quality_set(self, quality):
        """Switch stream quality live (builtin) or via restart (external)."""
        self.session_quality = quality
        if self.player is not None and self.play_info:
            codec = self.session_codec or self.prefs.get("video_codec",
                                                         "Auto")
            video_url, audio_url, height, note = YX.select_formats(
                self.play_info, quality, codec, ffmpeg_path=FFMPEG_PATH,
                audio_lang=self._current_audio_lang())
            if not video_url:
                self._player_toast(quality + " ?", self.C.STATUS_ERROR, 1200)
                return
            fmt = None
            for f in (self.play_info.get("formats") or []):
                if f.get("url") == video_url:
                    fmt = f
                    break
            w = int((fmt or {}).get("width") or 0) or self.player_hw[0]
            h = int((fmt or {}).get("height") or 0) or self.player_hw[1]
            fps = float((fmt or {}).get("fps") or 0) or self.player_fps
            self.player_hw = (w, h)
            self.player_fps = fps
            self.player.texture = None
            self.player.set_inputs(video_url, audio_url, w, h, fps,
                                   audio_in_video=bool(
                                       self.play_info.get(
                                           "_pilastube_muxed_video")))
            self._player_toast("%s %s" % (self.t("player_quality"), quality),
                               self.C.TEXT_PRIMARY, 1400)
            LOG("quality switched to %s (%dx%d)" % (quality, w, h), "PLAYER")
            return
        if self.is_playing:
            self._restart_requested = True
            try:
                self.player_process.terminate()
            except Exception:
                pass

    def player_codec_set(self, codec):
        """v3.2: switch video codec live (SmartTube's video codec picker).

        VP9/AV1 come as DASH video-only streams, so the audio pairing is
        re-selected too. Falls back to the previous stream when the codec
        is not available for this video."""
        if codec not in YX.CODEC_OPTIONS:
            return
        self.session_codec = codec
        if self.player is not None and self.play_info:
            quality = self.session_quality or self.prefs.get("quality",
                                                             "Auto")
            video_url, audio_url, height, note = YX.select_formats(
                self.play_info, quality, codec, ffmpeg_path=FFMPEG_PATH,
                audio_lang=self._current_audio_lang())
            if not video_url:
                self._player_toast(codec + " ?", self.C.STATUS_ERROR, 1200)
                return
            fmt = None
            for f in (self.play_info.get("formats") or []):
                if f.get("url") == video_url:
                    fmt = f
                    break
            w = int((fmt or {}).get("width") or 0) or self.player_hw[0]
            h = int((fmt or {}).get("height") or 0) or self.player_hw[1]
            fps = float((fmt or {}).get("fps") or 0) or self.player_fps
            self.player_hw = (w, h)
            self.player_fps = fps
            self.player.texture = None
            self.player.set_inputs(video_url, audio_url, w, h, fps,
                                   audio_in_video=bool(
                                       self.play_info.get(
                                           "_pilastube_muxed_video")))
            self._player_toast("Codec: %s" % codec,
                               self.C.TEXT_PRIMARY, 1400)
            LOG("codec switched to %s (%dx%d)" % (codec, w, h), "PLAYER")

    def player_quality_cycle(self):
        if not self.is_playing:
            return
        cur = self.session_quality or self.prefs.get("quality", "Auto")
        opts = QUALITY_OPTIONS
        idx = 0
        for i, q in enumerate(opts):
            if q == cur:
                idx = i
                break
        self.player_quality_set(opts[(idx + 1) % len(opts)])

    def player_skip_next(self):
        """START during playback: jump to next queued/next video."""
        if not self.is_playing:
            return
        self._skip_to_next = True
        self.user_stopped = False
        if self.player is not None:
            self._builtin_playback_done()
            return
        try:
            self.player_process.terminate()
        except Exception:
            pass

    def player_prev_video(self):
        """L1 during playback: go back to the previous list video."""
        if not self.is_playing:
            return
        videos = self._get_filtered_list()
        cur = self.current_video
        if not videos or not cur:
            return
        idx = -1
        for i, v in enumerate(videos):
            if v.id == cur.id:
                idx = i
                break
        if idx > 0:
            self.user_stopped = False
            self._skip_to_next = False
            self.queue_add(cur, front=True)
            prev = videos[idx - 1]
            if self.player is not None:
                self.current_video = prev
                self._builtin_teardown()
                self.play_video(prev, start_pos=0)
            else:
                try:
                    self.player_process.terminate()
                except Exception:
                    pass
                self.current_video = prev

    def player_next_video(self):
        """R1 during playback: jump to the next queued/next video."""
        if not self.is_playing:
            return
        nxt = self._next_video_candidate()
        if nxt is None:
            self._player_toast(self.t("player_no_next"),
                               self.C.TEXT_SECONDARY, 1200)
            return
        self.user_stopped = False
        self._skip_to_next = False
        if self.player is not None:
            if self.queue and self.queue[0].id == nxt.id:
                self.queue.pop(0)
            self.current_video = nxt
            self._builtin_teardown()
            self.play_video(nxt, start_pos=0)
        else:
            try:
                self.player_process.terminate()
            except Exception:
                pass
            self.current_video = nxt

    def stop_playback(self, user=True):
        if user:
            self.user_stopped = True
            self._skip_to_next = False
            self._restart_requested = False
        if self.player is not None:
            # built-in player: our window was never given away, so going
            # back to the menu is instant and completely safe (v2.2's
            # black-screen deadlock is structurally impossible now)
            if user and self.current_video:
                try:
                    self.save_position(self.current_video.id,
                                       self.player.position,
                                       self.last_duration)
                except Exception:
                    pass
            self._builtin_teardown()
            if user:
                self.current_video = None
                self.set_status("Stopped")
                self.need_redraw = True
            return
        if self.player_process:
            try:
                self.player_process.terminate()
                self.player_process.wait(timeout=2)
            except Exception:
                try:
                    self.player_process.kill()
                except Exception:
                    pass
        self.is_playing = False
        self.player_process = None
        if user:
            self.current_video = None
            if self.window:
                SDL_ShowWindow(self.window)
                SDL_RaiseWindow(self.window)
            self.set_status("Stopped")

    # ------------------------------------------------------------- queue
    def queue_add(self, video, front=False):
        if not video:
            return
        self.queue = [v for v in self.queue if v.id != video.id]
        if front:
            self.queue.insert(0, video)
        else:
            self.queue.append(video)
        self.set_status(self.t("msg_queue_next") if front
                        else self.t("msg_queue_added"))

    def queue_play_all(self, videos, start_idx):
        if not videos or start_idx >= len(videos):
            return
        self.queue = list(videos[start_idx + 1:])
        self.set_status(self.t("msg_play_all"))
        self.ctx_close()
        self.play_video(videos[start_idx])

    # =====================================================================
    # BUILT-IN PLAYER (v3.0) - SmartTube-style HUD
    # =====================================================================
    def _player_tick(self):
        """One main-loop iteration while the built-in player is active."""
        player = self.player
        if player is None:
            # between videos: the autoplay countdown may still be running
            if self.autoplay_countdown is not None:
                nxt, deadline = self.autoplay_countdown
                now = SDL_GetTicks()
                if now >= deadline:
                    self.autoplay_countdown = None
                    self._advance_playback()
                    return
                self.draw_rect(0, 0, SCREEN_WIDTH, SCREEN_HEIGHT,
                               self.C.BG_PRIMARY)
                self.draw_logo(SCREEN_WIDTH // 2 - 20, 120, 40, 28)
                self.draw_text_centered(self.t("player_next_in"),
                                        SCREEN_WIDTH // 2, 190,
                                        self.C.TEXT_SECONDARY,
                                        self.font_small)
                title = self.display_title(nxt)
                if len(title) > 46:
                    title = title[:44] + "..."
                self.draw_text_centered(title, SCREEN_WIDTH // 2, 214,
                                        self.C.TEXT_PRIMARY, self.font)
                remain = max(0, (deadline - now) / 1000)
                self.draw_text_centered("%d" % int(remain + 0.999),
                                        SCREEN_WIDTH // 2, 246,
                                        self.C.YT_RED, self.font_large)
                self.draw_text_centered(self.t("player_countdown_hint"),
                                        SCREEN_WIDTH // 2, 300,
                                        self.C.TEXT_TERTIARY, self.font_tiny)
                SDL_RenderPresent(self.renderer)
                self.frame_count += 1
                return
            self.is_playing = False
            return
        try:
            player.pump()
        except Exception:
            _PLOG.crash("player pump (ignored)", sys.exc_info())
        self.last_time_pos = max(0.0, player.position)
        self.player_paused = player.paused

        # ---- SponsorBlock auto-skip (SmartTube behavior) ----
        if self.current_segments and not player.paused and \
                not player.seek_pending:
            pos = player.position
            for i, seg in enumerate(self.current_segments):
                if i in self.sb_skipped_ids:
                    continue
                if seg["start"] <= pos < seg["end"] - 0.5:
                    self.sb_skipped_ids.add(i)
                    player.seek(seg["end"])
                    self._player_toast(
                        "%s %s" % (self.t("msg_skipped"), seg["label"]),
                        (120, 255, 140), 2000)
                    break

        # ---- periodic position save + sleep timer ----
        now = time.time()
        if now - self._sb_last_shown > 10:
            self._sb_last_shown = now
            if self.last_time_pos > 5 and self.current_video and \
                    not getattr(player, "is_live", False):
                self.save_position(self.current_video.id,
                                   self.last_time_pos, self.last_duration)
            if self.sleep_deadline and now > self.sleep_deadline:
                self._player_toast(self.t("player_sleep_stop"),
                                   self.C.STATUS_LOADING, 2000)
                self.user_stopped = True
                self.stop_playback(user=True)
                return

        # ---- autoplay countdown (SmartTube-style) ----
        if self.autoplay_countdown is not None:
            nxt, deadline = self.autoplay_countdown
            if SDL_GetTicks() >= deadline:
                self.autoplay_countdown = None
                self._advance_playback()
                return

        # ---- end / failure ----
        if player.ended or player.failed:
            self._builtin_playback_done()
            return

        # ---- battery (player HUD only, like SmartTube) ----
        if time.time() >= self._battery_next_check:
            self._battery_next_check = time.time() + 30.0
            self._read_battery()

        # ---- draw ----
        try:
            self.render_player_screen()
        except Exception:
            _PLOG.crash("player render (ignored)", sys.exc_info())

    def _read_battery(self):
        try:
            import glob as _glob
            for base in _glob.glob("/sys/class/power_supply/*"):
                try:
                    with open(os.path.join(base, "capacity")) as fh:
                        self.battery_pct = int(fh.read().strip())
                    with open(os.path.join(base, "status")) as fh:
                        self.battery_charging = \
                            fh.read().strip().lower() in ("charging",
                                                          "full")
                    return
                except Exception:
                    continue
        except Exception:
            pass

    def _player_draw_frame(self, player):
        """Blit the latest decoded frame, letterboxed. Returns dest rect."""
        # black background
        self.draw_rect(0, 0, SCREEN_WIDTH, SCREEN_HEIGHT, (0, 0, 0))
        vw, vh = player.width, player.height
        if player.last_frame is None:
            return None
        if player.texture is None:
            # ffmpeg pipes bgra (memory B,G,R,A); SDL_PIXELFORMAT_ARGB8888
            # reads exactly that byte order on little-endian - a plain copy,
            # no channel swizzle (v3.0's BGRX8888 read the padding byte as
            # BLUE -> the "bluish tint" bug). ARGB8888 is also the native
            # streaming format of the GLES/KMSDRM renderers, so the upload
            # itself stays a memcpy.
            player.texture = SDL_CreateTexture(
                self.renderer, sdl2.SDL_PIXELFORMAT_ARGB8888,
                sdl2.SDL_TEXTUREACCESS_STREAMING, vw, vh)
            if player.texture:
                SDL_SetTextureBlendMode(player.texture, SDL_BLENDMODE_NONE)
        if player.texture:
            try:
                SDL_UpdateTexture(player.texture, None, player.last_frame,
                                  vw * 4)
            except Exception:
                pass
            # v0.3.8: the texture is PHYSICAL pixels (design x UI_SCALE) -
            # map it back to LOGICAL coordinates for the blit. fit-mode
            # logical size shares the panel aspect, so this lands 1:1 on
            # the physical screen (no double scaling).
            sc = UI_SCALE if UI_SCALE and UI_SCALE > 1.0 else 1.0
            dw, dh = int(round(vw / sc)), int(round(vh / sc))
            if dw > SCREEN_WIDTH or dh > SCREEN_HEIGHT or dw < 2 or dh < 2:
                # defensive: refit if the logical size fell out of range
                scale = min(SCREEN_WIDTH / float(vw),
                            SCREEN_HEIGHT / float(vh))
                dw, dh = int(vw * scale), int(vh * scale)
            dx, dy = (SCREEN_WIDTH - dw) // 2, (SCREEN_HEIGHT - dh) // 2
            SDL_RenderCopy(self.renderer, player.texture, None,
                           SDL_Rect(dx, dy, dw, dh))
            return (dx, dy, dw, dh)
        return None

    def _player_gradient(self, y, h, down=True):
        """Fake vertical gradient (few solid strips, alpha blended)."""
        steps = 6
        for i in range(steps):
            alpha = 190 - int(150 * i / float(steps - 1)) if down \
                else 40 + int(150 * i / float(steps - 1))
            sy = y + int(h * i / float(steps))
            sh = int(h * (i + 1) / float(steps)) - int(h * i / float(steps))
            self.draw_rect(0, sy, SCREEN_WIDTH, sh, (0, 0, 0), alpha)

    def render_player_screen(self):
        player = self.player
        if player is None:
            return
        now = SDL_GetTicks()

        # auto-hide the HUD after 4s of inactivity (SmartTube behavior)
        if self.hud_visible and not self.player_menu and \
                not self.autoplay_countdown and \
                now - self.hud_last_activity > 4000 and \
                not player.paused:
            self.hud_visible = False

        self._player_draw_frame(player)

        # ---- buffering spinner ----
        if player.is_buffering():
            self.draw_rect(0, 0, SCREEN_WIDTH, SCREEN_HEIGHT, (0, 0, 0), 120)
            self.draw_spinner(SCREEN_WIDTH // 2, SCREEN_HEIGHT // 2 - 10, 14, 4)
            self.draw_text_centered(self.t("player_buffering"),
                                    SCREEN_WIDTH // 2,
                                    SCREEN_HEIGHT // 2 + 20,
                                    self.C.TEXT_SECONDARY, self.font_small)
            if player.seek_pending:
                self.draw_text_centered(self.t("player_seeking"),
                                        SCREEN_WIDTH // 2,
                                        SCREEN_HEIGHT // 2 + 42,
                                        self.C.TEXT_TERTIARY, self.font_tiny)

        # ---- big center pause badge ----
        if player.paused:
            self.draw_rect(SCREEN_WIDTH // 2 - 34, SCREEN_HEIGHT // 2 - 34,
                           68, 68, (0, 0, 0), 150)
            bar = self.C.TEXT_PRIMARY
            self.draw_rect(SCREEN_WIDTH // 2 - 16, SCREEN_HEIGHT // 2 - 22,
                           11, 44, bar)
            self.draw_rect(SCREEN_WIDTH // 2 + 5, SCREEN_HEIGHT // 2 - 22,
                           11, 44, bar)

        if self.hud_visible:
            self._render_player_topbar(player)
            self._render_player_bottom(player)

        # ---- transient toast ----
        if self.player_toast is not None:
            text, until, color = self.player_toast
            if now > until:
                self.player_toast = None
            else:
                w = len(text) * (self.text_factor(self.font) + 1)
                x = (SCREEN_WIDTH - w) // 2
                self.draw_rect(x - 14, 96, w + 28, 30, (0, 0, 0), 190)
                self.draw_text(text, x, 103, color, self.font)

        # ---- stats for nerds ----
        if self.player_stats:
            self._render_player_stats(player)

        # ---- modal menus ----
        if self.player_menu:
            self._render_player_menu(player)

        # ---- autoplay countdown ----
        if self.autoplay_countdown is not None:
            nxt, deadline = self.autoplay_countdown
            remain = max(0, (deadline - now) / 1000)
            self._player_gradient(SCREEN_HEIGHT - 150, 150)
            self.draw_text_centered(self.t("player_next_in"),
                                    SCREEN_WIDTH // 2, SCREEN_HEIGHT - 138,
                                    self.C.TEXT_SECONDARY, self.font_small)
            title = self.display_title(nxt)
            if len(title) > 46:
                title = title[:44] + "..."
            self.draw_text_centered(title, SCREEN_WIDTH // 2,
                                    SCREEN_HEIGHT - 116,
                                    self.C.TEXT_PRIMARY, self.font)
            self.draw_text_centered("%d" % int(remain + 0.999),
                                    SCREEN_WIDTH // 2, SCREEN_HEIGHT - 84,
                                    self.C.YT_RED, self.font_large)
            self.draw_text_centered(self.t("player_countdown_hint"),
                                    SCREEN_WIDTH // 2, SCREEN_HEIGHT - 40,
                                    self.C.TEXT_TERTIARY, self.font_tiny)

        SDL_RenderPresent(self.renderer)
        self.frame_count += 1

    # ------------------------------------------------------------- top bar
    def _render_player_topbar(self, player):
        h = 78
        self._player_gradient(0, h)
        video = self.current_video
        # wifi indicator (top-left, as everywhere else in the app)
        self.draw_wifi_icon(10, 10)
        # battery (top-right, like SmartTube's player)
        if self.battery_pct is not None:
            self._draw_battery(SCREEN_WIDTH - 52, 12, self.battery_pct,
                               self.battery_charging)
        # title
        title = self.display_title(video) if video else ""
        if len(title) > 52:
            title = title[:50] + "..."
        self.draw_text(title, 46, 8, self.C.TEXT_PRIMARY, self.font)
        # channel + meta line
        meta = []
        if video is not None:
            meta.append(video.channel or "")
            if video.views:
                meta.append(video.format_views())
        qual = self.session_quality or self.prefs.get("quality", "Auto")
        height = player.src_height or player.height or 0
        meta.append("%s (%dp)" % (qual, height) if height else qual)
        if abs(self.current_speed - 1.0) > 0.01:
            meta.append("%sx" % self.current_speed)
        if player.sub_file:
            meta.append("CC")
        meta_txt = "  |  ".join([m for m in meta if m])
        if len(meta_txt) > 74:
            meta_txt = meta_txt[:72] + "..."
        self.draw_text(meta_txt, 46, 32, self.C.TEXT_SECONDARY,
                       self.font_small)
        # chapter title under the meta line
        if self.current_chapters:
            pos = self.last_time_pos
            cur_ch = None
            for c in self.current_chapters:
                if float(c.get("start_time", 0) or 0) <= pos + 0.5:
                    cur_ch = c
            if cur_ch:
                ctitle = cur_ch.get("title", "")
                if len(ctitle) > 60:
                    ctitle = ctitle[:58] + "..."
                self.draw_text(ctitle, 46, 50, (255, 204, 0),
                               self.font_tiny)

    def _draw_battery(self, x, y, pct, charging):
        color = self.C.STATUS_SUCCESS if pct > 25 else self.C.STATUS_ERROR
        if charging:
            color = (255, 204, 0)
        self.draw_rect(x, y + 2, 2, 8, self.C.TEXT_SECONDARY)
        self.draw_rect(x + 2, y, 30, 12, (0, 0, 0), 160)
        fill = int(26 * max(0, min(100, pct)) / 100.0)
        self.draw_rect(x + 4, y + 2, fill, 8, color)
        self.draw_text("%d%%" % pct, x - 2, y + 15,
                       self.C.TEXT_SECONDARY, self.font_tiny)
        if charging:
            # little lightning bolt
            self.draw_rect(x + 15, y + 3, 4, 2, (255, 255, 255))
            self.draw_rect(x + 16, y + 5, 3, 2, (255, 255, 255))
            self.draw_rect(x + 17, y + 7, 2, 2, (255, 255, 255))

    # ---------------------------------------------------------- bottom bar
    # v3.1 layout, mirroring SmartTube's player:
    #   00:42  ====================|=========  -12:03      <- progress row
    #   [<<] [-10] [>] [+10] [>>]   [CC] [1x] [480p] [...] [x] <- options row
    # The options row sits BELOW the progress bar and is navigated with
    # LEFT/RIGHT (dpad or stick); A activates the focused button.
    HUD_CELL = 48                 # width of one options-row cell

    def _render_player_bottom(self, player):
        y0 = SCREEN_HEIGHT - 128
        self._player_gradient(y0, 128, down=False)

        dur = self.last_duration or player.duration or 0
        pos = self.last_time_pos
        live = dur <= 0

        # ---- progress row: elapsed  [bar]  remaining (inline, SmartTube) --
        time_y = y0 + 34
        bar_x, bar_w, bar_y, bar_h = 78, SCREEN_WIDTH - 156, time_y - 1, 12
        self.draw_text(fmt_clock(pos), 24, time_y,
                       self.C.TEXT_PRIMARY, self.font_small)
        if not live:
            remain = "-" + fmt_clock(max(0, dur - pos))
            w = len(remain) * (self.text_factor(self.font_small) + 1)
            self.draw_text(remain, SCREEN_WIDTH - 24 - w, time_y,
                           self.C.TEXT_PRIMARY, self.font_small)
        else:
            self.draw_text("LIVE", SCREEN_WIDTH - 58, time_y,
                           self.C.BADGE_LIVE, self.font_small)

        self.draw_rect(bar_x, bar_y, bar_w, bar_h, (90, 90, 90))
        if not live and dur > 0:
            # buffered-ahead (light)
            ahead = player.buffered_ahead()
            buf_w = int(bar_w * max(0.0, min(1.0,
                                             (pos + ahead) / dur)))
            self.draw_rect(bar_x, bar_y, buf_w, bar_h, (150, 150, 150))
            # sponsorblock segments (category colors)
            for seg in self.current_segments:
                sx = bar_x + int(bar_w * max(0.0,
                                             seg["start"] / dur))
                sw = int(bar_w * max(0.0,
                                     (seg["end"] - seg["start"]) / dur))
                sw = max(2, min(sw, bar_x + bar_w - sx))
                self.draw_rect(sx, bar_y, sw, bar_h,
                               SB_COLORS.get(seg.get("category"),
                                             (120, 200, 255)))
            # chapter tick marks
            for c in self.current_chapters:
                cx = bar_x + int(bar_w * max(0.0, min(1.0,
                        float(c.get("start_time", 0) or 0) / dur)))
                self.draw_rect(cx, bar_y - 2, 2, bar_h + 4,
                               (30, 30, 30))
            # progress
            prog_w = int(bar_w * max(0.0, min(1.0, pos / dur)))
            self.draw_rect(bar_x, bar_y, prog_w, bar_h, self.C.YT_RED)
            # thumb
            self.draw_rect(bar_x + prog_w - 6, bar_y - 4, 12, bar_h + 8,
                           self.C.YT_RED)
        else:
            # live: pulsing bar
            pulse = (SDL_GetTicks() // 400) % 2 == 0
            self.draw_rect(bar_x, bar_y, bar_w, bar_h,
                           self.C.BADGE_LIVE if pulse else (120, 30, 30))

        # ---- options row BELOW the progress bar ----
        buttons = self._player_buttons(player)
        n = len(buttons)
        if n:
            row_cy = y0 + 78
            total_w = n * self.HUD_CELL
            x = (SCREEN_WIDTH - total_w) // 2
            # caption of the focused button (announces what A will do)
            fidx = self.hud_focus if self.hud_focus < n else 0
            if buttons[fidx][0] != "spacer":
                caption = buttons[fidx][1]
                cw = len(caption) * (self.text_factor(self.font_tiny))
                self.draw_text(caption,
                               SCREEN_WIDTH // 2 - cw // 2, y0 + 54,
                               self.C.TEXT_SECONDARY, self.font_tiny)
            for i, (icon, label, hot) in enumerate(buttons):
                if icon != "spacer":
                    self._draw_player_button(x, row_cy, icon, label, hot,
                                             focused=(i == fidx))
                x += self.HUD_CELL

        # ---- hint line ----
        hint = self.t("player_hint_ui" if self.hud_visible
                     else "player_hint")
        self.draw_text(hint, SCREEN_WIDTH // 2 -
                       len(hint) * (self.text_factor(self.font_tiny)),
                       SCREEN_HEIGHT - 14, self.C.TEXT_TERTIARY,
                       self.font_tiny)

    def _player_buttons(self, player):
        """SmartTube-style options row: (icon, label, hot)."""
        has_ch = bool(self.current_chapters)
        return [
            ("prev", self.t("player_prev"), True),
            ("back10", "-%ds" % self._seek_step(), True),
            ("play" if not player.paused else "pause",
             self.t("player_pause") if not player.paused
             else self.t("player_play"), True),
            ("fwd10", "+%ds" % self._seek_step(), True),
            ("next", self.t("player_next"), True),
            ("spacer", "", False),
            ("cc", self.t("player_captions"), bool(player.sub_file)),
            ("speed", "%sx" % self.current_speed, True),
            ("quality", (self.session_quality or
                         self.prefs.get("quality", "Auto")), True),
            ("chapters" if has_ch else "loop",
             self.t("player_chapters") if has_ch else
             (self.t("player_loop") if self.player_loop else
              self.t("loop_off")), True),
            ("gear", self.t("player_options"), True),
        ]

    def _draw_player_button(self, x, cy, icon, label, hot, focused=False):
        """One options-row cell (v3.2): anti-aliased vector icon blitted
        from the texture cache, small caption for the value-bearing
        buttons, red underline marking focus (SmartTube focus style)."""
        cell = self.HUD_CELL
        cx = x + cell // 2
        if focused:
            self.draw_rect(x + 4, cy - 24, cell - 8, 48, (0, 0, 0), 130)
            self.draw_rect(x + 8, cy + 21, cell - 16, 3, self.C.YT_RED)
        color = (255, 255, 255) if (focused or hot) \
            else (156, 156, 156)
        icy = cy - 5
        tex = _get_icon_texture(self.renderer, icon, color)
        if tex:
            SDL_RenderCopy(self.renderer, tex, None,
                           SDL_Rect(cx - ICON_TEX_SIZE // 2,
                                    icy - ICON_TEX_SIZE // 2,
                                    ICON_TEX_SIZE, ICON_TEX_SIZE))
        # value captions: skip seconds inside the arrow, CC inside the box,
        # speed/quality below the icon
        if icon in ("back10", "fwd10"):
            self.draw_text_centered(label, cx, icy - 5, color,
                                    self.font_tiny)
        elif icon == "cc":
            self.draw_text_centered("CC", cx, icy - 5, color,
                                    self.font_tiny)
        elif icon == "speed":
            self.draw_text_centered(label, cx, cy + 11, color,
                                    self.font_tiny)
        elif icon == "quality":
            self.draw_text_centered(label[:5], cx, cy + 11, color,
                                    self.font_tiny)

    # -------------------------------------------------------- stats overlay
    def _render_player_stats(self, player):
        lines = [
            "%s: %dx%d@%.0f -> %dx%d bgra" % (
                self.t("player_stat_res"),
                player.src_width, player.src_height, player.fps,
                player.width, player.height),
            "%s / %s" % (self.t("player_stat_shown"), player.frames_shown),
            "%s: %d" % (self.t("player_stat_dropped"), player.frames_dropped),
            "decode: %.1f fps" % player.decode_fps,
            "%s: %.1fs" % (self.t("player_stat_buffer"),
                           player.buffered_ahead()),
            "vol: %d%%  speed: %sx" % (player.volume, self.current_speed),
            "audio: %s" % ("48k s16" if player.has_audio else "none"),
        ]
        if player.video_url:
            lines.append("url: ...%s" % player.video_url[-46:])
        w = 300
        self.draw_rect(14, 88, w, 20 + len(lines) * 18, (0, 0, 0), 200)
        yy = 96
        for line in lines:
            self.draw_text(line[:52], 22, yy, (120, 255, 120),
                           self.font_tiny)
            yy += 18

    # ---------------------------------------------------------- menu panel
    def _player_menu_items(self, player):
        """(label, kind, payload) rows for the open player menu."""
        items = []
        if self.player_menu == "quality":
            cur = self.session_quality or self.prefs.get("quality", "Auto")
            for q in QUALITY_OPTIONS:
                items.append(("%s%s" % (q, "  <" if q == cur else ""),
                              "quality", q))
        elif self.player_menu == "speed":
            for s in SPEED_STEPS:
                s_txt = ("%gx" % s)
                items.append((s_txt + ("  <" if abs(s - self.current_speed)
                                       < 0.01 else ""), "speed", s))
        elif self.player_menu == "chapters":
            pos = self.last_time_pos
            for c in self.current_chapters:
                st = float(c.get("start_time", 0) or 0)
                mark = "  <" if st <= pos + 1 else ""
                items.append(("%s  %s%s" % (fmt_clock(st),
                                            (c.get("title") or "")[:34],
                                            mark), "chapter", st))
            if not items:
                items.append((self.t("player_no_chapters"), "noop", None))
        elif self.player_menu == "captions":
            items.append((self.t("player_cc_off"), "cc", None))
            langs = []
            for tr in (self.play_info or {}).get("subtitles") or {}:
                if tr != "live_chat":
                    langs.append(tr)
            for lang in langs[:8]:
                name = LANG_NAMES.get(lang, lang)
                items.append((name, "cc", lang))
            if len(items) == 1:
                items.append((self.t("player_cc_none"), "noop", None))
        elif self.player_menu == "codec":
            # v3.2: SmartTube-style video codec picker
            cur = self.session_codec or self.prefs.get("video_codec",
                                                       "Auto")
            for c in YX.CODEC_OPTIONS:
                items.append(("%s%s" % (c, "  <" if c == cur else ""),
                              "codec", c))
        elif self.player_menu == "audio_lang":
            # v3.6: audio track language picker (multi-audio / dubbed
            # videos). 'Original' is always offered; the rest come from
            # the video's audio formats / live master manifest.
            cur = self._current_audio_lang()
            if len(self._available_audio_langs()) <= 1:
                items.append((self.t("player_audio_single"), "noop", None))
            for code, label in self._available_audio_langs():
                items.append(("%s%s" % (label, "  <" if code == cur
                                        else ""), "audio_lang", code))
        else:   # options (gear menu - mirrors SmartTube's player menu)
            cur = self.session_quality or self.prefs.get("quality", "Auto")
            items.append(("%s: %s" % (self.t("player_quality"), cur),
                          "menu_quality", None))
            cur_c = self.session_codec or self.prefs.get("video_codec",
                                                         "Auto")
            items.append(("%s: %s" % (self.t("player_codec"), cur_c),
                          "menu_codec", None))
            # v3.6: audio track language (SmartTube's audio picker)
            items.append(("%s: %s" % (self.t("player_audio_lang"),
                                      self._audio_lang_label()),
                          "menu_audio_lang", None))
            items.append(("%s: %sx" % (self.t("player_speed"),
                                       self.current_speed),
                          "menu_speed", None))
            cc = self.t("settings_on") if (self.player and
                                           self.player.sub_file) \
                else self.t("settings_off")
            items.append(("%s: %s" % (self.t("player_captions"), cc),
                          "menu_captions", None))
            items.append(("%s: %s" % (self.t("player_loop"),
                                      self.t("settings_on") if self.player_loop
                                      else self.t("settings_off")),
                          "loop", None))
            items.append(("%s: %s" % (self.t("player_volume"),
                                      "%d%%" % self.player_volume_pct),
                          "volume", None))
            items.append(("%s: %s" % (self.t("player_stats"),
                                      self.t("settings_on") if self.player_stats
                                      else self.t("settings_off")),
                          "stats", None))
            if self.current_chapters:
                items.append((self.t("player_chapters"), "menu_chapters",
                              None))
            if self.current_video:
                items.append((self.t("player_open_channel"),
                              "channel", None))
                items.append((self.t("ctx_queue_add"), "queue", None))
            items.append((self.t("player_showtime_menu"), "time", None))
        return items

    def _render_player_menu(self, player):
        items = self._player_menu_items(player)
        n = len(items)
        title = {
            "quality": self.t("player_quality"),
            "speed": self.t("player_speed"),
            "options": self.t("player_options"),
            "chapters": self.t("player_chapters"),
            "captions": self.t("player_captions"),
            "codec": self.t("player_codec"),
            "audio_lang": self.t("player_audio_lang"),
        }.get(self.player_menu, self.t("player_options"))
        panel_w = 400
        row_h = 30
        panel_h = 56 + n * row_h
        panel_x = (SCREEN_WIDTH - panel_w) // 2
        panel_y = max(20, (SCREEN_HEIGHT - panel_h) // 2)
        self.draw_rect(panel_x, panel_y, panel_w, panel_h, (0, 0, 0), 235)
        self.draw_rect(panel_x, panel_y, panel_w, 34, (30, 30, 30), 255)
        self.draw_rect(panel_x, panel_y + 34, panel_w, 2, self.C.YT_RED)
        self.draw_text(title, panel_x + 14, panel_y + 9,
                       self.C.TEXT_PRIMARY, self.font_small)
        self.draw_text("[B]", panel_x + panel_w - 40, panel_y + 9,
                       self.C.TEXT_TERTIARY, self.font_small)
        self.player_menu_sel = max(0, min(self.player_menu_sel, n - 1))
        for i, (label, kind, payload) in enumerate(items):
            ry = panel_y + 44 + i * row_h
            selected = i == self.player_menu_sel
            if selected:
                self.draw_rect(panel_x + 6, ry, panel_w - 12, row_h,
                               (60, 60, 60), 255)
                self.draw_rect(panel_x + 6, ry, 3, row_h, self.C.YT_RED)
            self.draw_text(label[:44], panel_x + 18, ry + 7,
                           self.C.TEXT_PRIMARY if selected
                           else self.C.TEXT_SECONDARY, self.font_small)

    def _player_menu_action(self, direction):
        """dpad LEFT/RIGHT inside a menu: quick-adjust where it makes sense."""
        items = self._player_menu_items(self.player) if self.player else []
        if not items or self.player_menu_sel >= len(items):
            return
        label, kind, payload = items[self.player_menu_sel]
        if kind == "quality":
            opts = QUALITY_OPTIONS
            idx = opts.index(payload) if payload in opts else 0
            self.player_quality_set(opts[(idx + direction) % len(opts)])
        elif kind == "codec":
            # v3.2: LEFT/RIGHT quick-adjusts the codec too
            opts = YX.CODEC_OPTIONS
            idx = opts.index(payload) if payload in opts else 0
            self.player_codec_set(opts[(idx + direction) % len(opts)])
        elif kind == "audio_lang":
            # v3.6: LEFT/RIGHT quick-adjusts the audio language
            opts = [c for c, _l in self._available_audio_langs()]
            idx = opts.index(payload) if payload in opts else 0
            self.player_audio_lang_set(
                opts[(idx + direction) % len(opts)])
        elif kind == "speed":
            idx = SPEED_STEPS.index(payload) if payload in SPEED_STEPS else 0
            idx = max(0, min(len(SPEED_STEPS) - 1, idx + direction))
            self.player_set_speed(SPEED_STEPS[idx])

    # ------------------------------------------------------------ menu nav
    def player_menu_move(self, delta):
        if not self.player_menu:
            return
        items = self._player_menu_items(self.player) if self.player else []
        n = max(1, len(items))
        self.player_menu_sel = (self.player_menu_sel + delta) % n
        self.hud_last_activity = SDL_GetTicks()

    def player_menu_select(self):
        if not self.player or not self.player_menu:
            return
        items = self._player_menu_items(self.player)
        if not items or self.player_menu_sel >= len(items):
            return
        label, kind, payload = items[self.player_menu_sel]
        self.hud_last_activity = SDL_GetTicks()

        if kind == "quality":
            self.player_quality_set(payload)
            self.player_menu = None
        elif kind == "codec":
            self.player_codec_set(payload)
            self.player_menu = None
        elif kind == "audio_lang":
            self.player_audio_lang_set(payload)
            self.player_menu = None
        elif kind == "speed":
            self.player_set_speed(payload)
            self.player_menu = None
        elif kind == "chapter":
            self.player_seek_absolute(payload + 0.1)
            self.player_menu = None
        elif kind == "cc":
            self._restart_with_captions(payload)
            self.player_menu = None
        elif kind == "menu_quality":
            self.player_menu = "quality"
            self.player_menu_sel = 0
        elif kind == "menu_codec":
            self.player_menu = "codec"
            self.player_menu_sel = 0
        elif kind == "menu_audio_lang":
            self.player_menu = "audio_lang"
            self.player_menu_sel = 0
        elif kind == "menu_speed":
            self.player_menu = "speed"
            self.player_menu_sel = 0
        elif kind == "menu_captions":
            self.player_menu = "captions"
            self.player_menu_sel = 0
        elif kind == "menu_chapters":
            self.player_menu = "chapters"
            self.player_menu_sel = 0
        elif kind == "loop":
            self.player_loop = not self.player_loop
        elif kind == "volume":
            # cycle 100 -> 75 -> 50 -> 25 -> 0 -> 100
            if self.player_volume_pct <= 0:
                self.player_volume_pct = 100
                if self.player:
                    self.player.set_volume(100)
                self._player_toast("%s 100%%" % self.t("player_volume"),
                                   self.C.TEXT_PRIMARY, 1000)
            else:
                self.player_volume(-25)
        elif kind == "stats":
            self.player_stats = not self.player_stats
        elif kind == "channel":
            video = self.current_video
            self.player_menu = None
            if video:
                self.stop_playback(user=False)
                self.user_stopped = True
                self.open_channel(video)
        elif kind == "queue":
            video = self.current_video
            if video:
                self.queue_add(video)
                self._player_toast(self.t("msg_queue_added"),
                                   (120, 255, 140), 1400)
        elif kind == "time":
            self.player_show_time()
        elif kind == "noop":
            pass

    def _restart_with_captions(self, lang):
        """Restart playback with burned-in captions (payload None = off)."""
        if not self.player or not self.play_info:
            return
        sub_file = None
        if lang:
            vtt = "/tmp/yt_sub_%d.vtt" % os.getpid()
            srt = vtt.rsplit(".", 1)[0] + ".srt"
            if YX.pick_subtitle(self.play_info, lang, vtt, self.prefs) and \
                    self._vtt_to_srt(vtt, srt):
                try:
                    os.remove(vtt)
                except OSError:
                    pass
                sub_file = srt
        if lang and not sub_file:
            self._player_toast(self.t("player_cc_none"),
                               self.C.STATUS_ERROR, 1600)
            return
        pos = self.player.position
        old_sub = self.player.sub_file
        self.player.sub_file = sub_file
        self.player.seek(pos)
        if old_sub and old_sub != sub_file:
            try:
                os.remove(old_sub)
            except OSError:
                pass
        if sub_file:
            self._player_toast("%s: %s" % (self.t("player_captions"),
                                           LANG_NAMES.get(lang, lang)),
                               (120, 255, 140), 1600)
        else:
            self._player_toast(self.t("player_cc_off"),
                               self.C.TEXT_SECONDARY, 1400)

    def render_queue_screen(self):
        self.draw_rect(0, 0, SCREEN_WIDTH, SCREEN_HEIGHT, (0, 0, 0), 235)
        self.draw_text_centered(self.t("queue_title"), SCREEN_WIDTH // 2, 18,
                                self.C.TEXT_PRIMARY, self.font_large)
        if not self.queue:
            self.draw_text_centered(self.t("queue_empty"), SCREEN_WIDTH // 2, 200,
                                    self.C.TEXT_SECONDARY, self.font)
            return
        item_h = 44
        max_items = 8
        start_y = 56
        for i, v in enumerate(self.queue[:max_items]):
            y = start_y + i * item_h
            selected = i == self.queue_selected
            if selected:
                self.draw_rect(20, y, SCREEN_WIDTH - 40, item_h - 4,
                               self.C.CARD_SELECTED)
                self.draw_rect(20, y, 4, item_h - 4, self.C.YT_RED)
            else:
                self.draw_rect(20, y, SCREEN_WIDTH - 40, item_h - 4, self.C.CARD_BG)
            self.draw_text("%d." % (i + 1), 30, y + 12, self.C.TEXT_TERTIARY,
                           self.font_small)
            title = v.title[:34]
            self.draw_text(title, 60, y + 5,
                           self.C.TEXT_PRIMARY if selected else self.C.TEXT_SECONDARY,
                           self.font_small)
            self.draw_text((v.channel or "")[:30], 60, y + 22,
                           self.C.TEXT_TERTIARY, self.font_tiny)
        if len(self.queue) > max_items:
            self.draw_text_centered("... +%d" % (len(self.queue) - max_items),
                                    SCREEN_WIDTH // 2, start_y + max_items * item_h,
                                    self.C.TEXT_TERTIARY, self.font_small)

    def open_queue(self):
        self.queue_open = True
        self.queue_selected = 0
        self.need_redraw = True

    def queue_action_select(self):
        if not self.queue:
            self.queue_open = False
            return
        idx = min(self.queue_selected, len(self.queue) - 1)
        video = self.queue[idx]
        self.queue = self.queue[idx + 1:]
        self.queue_open = False
        self.play_video(video)

    def queue_remove(self):
        if not self.queue:
            return
        idx = min(self.queue_selected, len(self.queue) - 1)
        self.queue.pop(idx)
        if self.queue and self.queue_selected >= len(self.queue):
            self.queue_selected = len(self.queue) - 1
        if not self.queue:
            self.queue_selected = 0
        self.need_redraw = True

    def _player_direction(self, d, now=None):
        """One gated direction press inside the player (SmartTube rules)."""
        player = self.player
        if player is None:
            return
        now = SDL_GetTicks() if now is None else now
        self.hud_last_activity = now
        # modal menu open: up/down walk the rows, left/right quick-adjust
        if self.player_menu:
            if d == "up":
                self.player_menu_move(-1)
            elif d == "down":
                self.player_menu_move(1)
            elif d == "left":
                self._player_menu_action(-1)
            elif d == "right":
                self._player_menu_action(1)
            return
        if self.hud_visible:
            # options row is showing: dpad/stick navigates THE BUTTONS
            # (options bar sits below the progress bar, SmartTube style)
            if d == "left":
                self._hud_focus_move(-1)
                self.key_held, self.key_hold_start = "left", now
            elif d == "right":
                self._hud_focus_move(1)
                self.key_held, self.key_hold_start = "right", now
            elif d in ("up", "down"):
                self._player_hud_toggle()     # hide the HUD
            return
        # HUD hidden: SmartTube quick controls
        if d == "left":
            self.player_seek(-self._seek_step())
        elif d == "right":
            self.player_seek(self._seek_step())
        elif d == "down":
            self._player_hud_toggle()         # show the HUD
        elif d == "up":
            if self.current_chapters:
                self.player_menu = "chapters"
                self.player_menu_sel = 0
                self.hud_visible = True
            else:
                self.player_volume(5)

    def _seek_step(self):
        try:
            return max(5, min(60, int(self.prefs.get("seek_interval", "10"))))
        except ValueError:
            return 10

    def _hud_focus_move(self, delta):
        """Move the focus in the HUD options row (skipping spacers)."""
        player = self.player
        buttons = self._player_buttons(player) if player else []
        n = len(buttons)
        if n == 0:
            return
        idx = self.hud_focus
        for _ in range(n):
            idx = (idx + delta) % n
            if buttons[idx][0] != "spacer":
                break
        self.hud_focus = idx
        self.hud_last_activity = SDL_GetTicks()

    def _hud_activate(self):
        """A on the visible HUD: run the focused option (SmartTube)."""
        player = self.player
        if player is None:
            return
        buttons = self._player_buttons(player)
        if not buttons or self.hud_focus >= len(buttons):
            return
        icon = buttons[self.hud_focus][0]
        step = self._seek_step()
        if icon == "prev":
            self.player_prev_video()
        elif icon == "back10":
            self.player_seek(-step)
        elif icon in ("play", "pause"):
            self.player_toggle_pause()
        elif icon == "fwd10":
            self.player_seek(step)
        elif icon == "next":
            self.player_next_video()
        elif icon == "cc":
            self.player_menu = "captions"
            self.player_menu_sel = 0
            self.hud_visible = True
        elif icon == "speed":
            self.player_menu = "speed"
            self.player_menu_sel = 0
            self.hud_visible = True
        elif icon == "quality":
            self.player_menu = "quality"
            self.player_menu_sel = 0
            self.hud_visible = True
        elif icon == "chapters":
            self.player_menu = "chapters"
            self.player_menu_sel = 0
            self.hud_visible = True
        elif icon == "loop":
            self.player_loop = not self.player_loop
        elif icon == "gear":
            self.player_menu = "options"
            self.player_menu_sel = 0
            self.hud_visible = True
        self.hud_last_activity = SDL_GetTicks()
