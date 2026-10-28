#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
PilasTube v0.3.9 - PilasTube.py (application core)

App state and lifecycle: __init__, preferences/JSON stores, history and
resume positions, the first-boot wizard, every data loader (recommended
home feed, categories, search, RSS + account subscriptions, channels),
the settings engine, keyboard/suggestions/context-menu logic, the whole
gamepad input pipeline (event gating, dedup, analog hysteresis, R2/L2
section switching) and the main run loop.

Module map (v3.5 restructure):
    PilasTube.py - app core: state, data, settings, input, main loop
    player.py    - FFPlayer engine + PlayerMixin (playback/HUD/queue)
    ui.py        - UIMixin (renderers + drawing toolkit + crash screen)
    auth.py      - AuthMixin (login / account / subscriptions history)
    utils.py     - bootstrap, logging, SDL2 load, constants, VideoItem
    yt_extras.py - network + InnerTube/RSS/SponsorBlock/format layer
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
    APP_VERSION,
    BTN_LTRIG,
    BTN_RTRIG,
    CATEGORY_DEFS,
    LANGUAGES,
    LOG,
    NAV_CATEGORIES,
    NAV_COUNT,
    NAV_FAVORITES,
    NAV_HISTORY,
    NAV_HOME,
    NAV_SEARCH,
    NAV_SETTINGS,
    NAV_SUBS,
    PLog,
    QUALITY_OPTIONS,
    SCALE_MODE,
    SCREEN_HEIGHT,
    SCREEN_WIDTH,
    FILL_SCALE_X,
    FILL_SCALE_Y,
    UI_SCALE,
    WINDOW_HEIGHT,
    WINDOW_WIDTH,
    SCRIPT_DIR,
    SDLK_DOWN,
    SDLK_ESCAPE,
    SDLK_LEFT,
    SDLK_RETURN,
    SDLK_RIGHT,
    SDLK_UP,
    SDLK_c,
    SDLK_q,
    SDLK_x,
    SDLK_z,
    SDL_BLENDMODE_BLEND,
    SDL_CONTROLLERAXISMOTION,
    SDL_CONTROLLERBUTTONDOWN,
    SDL_CONTROLLERBUTTONUP,
    SDL_CONTROLLER_AXIS_LEFTX,
    SDL_CONTROLLER_AXIS_LEFTY,
    SDL_CONTROLLER_BUTTON_A,
    SDL_CONTROLLER_BUTTON_B,
    SDL_CONTROLLER_BUTTON_DPAD_DOWN,
    SDL_CONTROLLER_BUTTON_DPAD_LEFT,
    SDL_CONTROLLER_BUTTON_DPAD_RIGHT,
    SDL_CONTROLLER_BUTTON_DPAD_UP,
    SDL_CONTROLLER_BUTTON_LEFTSHOULDER,
    SDL_CONTROLLER_BUTTON_RIGHTSHOULDER,
    SDL_CONTROLLER_BUTTON_SELECT,
    SDL_CONTROLLER_BUTTON_START,
    SDL_CONTROLLER_BUTTON_X,
    SDL_CONTROLLER_BUTTON_Y,
    SDL_CreateRenderer,
    SDL_CreateWindow,
    SDL_Delay,
    SDL_DestroyRenderer,
    SDL_DestroyTexture,
    SDL_DestroyWindow,
    SDL_Event,
    SDL_GameControllerClose,
    SDL_GameControllerGetAxis,
    SDL_GameControllerGetButton,
    SDL_GameControllerName,
    SDL_GameControllerOpen,
    SDL_GetCurrentVideoDriver,
    SDL_GetTicks,
    SDL_HAT_DOWN,
    SDL_HAT_LEFT,
    SDL_HAT_RIGHT,
    SDL_HAT_UP,
    SDL_IMAGE_AVAILABLE,
    SDL_INIT_AUDIO,
    SDL_INIT_GAMECONTROLLER,
    SDL_INIT_JOYSTICK,
    SDL_INIT_VIDEO,
    SDL_Init,
    SDL_IsGameController,
    SDL_JOYHATMOTION,
    SDL_JoystickClose,
    SDL_JoystickGetHat,
    SDL_JoystickOpen,
    SDL_KEYDOWN,
    SDL_KEYUP,
    SDL_NumJoysticks,
    SDL_PollEvent,
    SDL_PushEvent,
    SDL_QUIT,
    SDL_Quit,
    SDL_RENDERER_ACCELERATED,
    SDL_RENDERER_PRESENTVSYNC,
    SDL_RENDERER_SOFTWARE,
    SDL_SetRenderDrawBlendMode,
    SDL_WINDOWPOS_CENTERED,
    SDL_WINDOW_FULLSCREEN,
    SDL_WINDOW_FULLSCREEN_DESKTOP,
    SDL_WINDOW_SHOWN,
    SLOG,
    TRANSLATIONS,
    VideoItem,
    WIZARD_DEVICES,
    WIZARD_STEPS,
    _PLOG,
    _atexit_note,
    _dbm_to_bars,
    _destroy_icon_cache,
    _first_line,
    _icon_pixels,
    _link_to_bars,
    _py_version,
    _read_wifi_state,
    _sdl_err,
    fmt_clock,
    run_logged_thread,
    sdl2,
    sdlimage,
    ttf,
)
from player import (
    FFMPEG_PATH,
    FFPlayer,
    PLAYER_IS_MPV,
    SB_COLORS,
    USE_BUILTIN_PLAYER,
    VIDEO_PLAYER,
    YTDLP_PATH,
)
from ui import (
    _show_crash_screen,
)
import yt_extras as YX
import player
import ui
import auth
import utils   # v0.3.9: module handle for refresh_geometry/apply_logical_mapping

# ----------------------------------------------------------------------------
# Main application
# ----------------------------------------------------------------------------
class PilasTubeApp(auth.AuthMixin, player.PlayerMixin, ui.UIMixin):
    def __init__(self):
        # --- SDL init with graceful degradation ---------------------------
        rc = SDL_Init(SDL_INIT_VIDEO | SDL_INIT_JOYSTICK |
                      SDL_INIT_GAMECONTROLLER)
        if rc != 0:
            LOG("SDL_Init(video+joystick+gamecontroller) failed: %s - "
                "retrying with video only" % _sdl_err(), "SDL")
            rc = SDL_Init(SDL_INIT_VIDEO)
            if rc != 0:
                LOG("FATAL: SDL_Init(video) failed: %s" % _sdl_err(), "SDL")
                raise RuntimeError("SDL_Init failed: %s" % _sdl_err())
        try:
            _drv = SDL_GetCurrentVideoDriver()
            LOG("SDL_Init OK - video driver: %s" %
                (_drv.decode("utf-8", "replace") if _drv else "?"), "SDL")
        except Exception:
            LOG("SDL_Init OK", "SDL")

        # Knulli / Miyoo Flip fix: Initialize audio subsystem on the main thread during startup.
        # Initializing it later on background threads can cause race conditions or SIGSEGV with PipeWire/ALSA.
        try:
            if hasattr(sdl2, "SDL_InitSubSystem"):
                sdl2.SDL_InitSubSystem(SDL_INIT_AUDIO)
        except Exception as _ea:
            LOG("SDL audio init warning (main thread): %s" % _ea, "SDL")

        # v0.3.9: SDL video is initialised - THE ONLY PLACE IT EVER IS,
        # exactly like v0.3.7 (0.3.8 also initialised it at utils import
        # and that contributed to the KMSDRM black-screen regression).
        # Now that it exists we can ask SDL for the real desktop mode:
        # if the import-time framebuffer probe got the panel wrong,
        # utils.refresh_geometry() recomputes the whole geometry +
        # device.txt BEFORE the window opens. On real handhelds the
        # probes agree and this is a no-op.
        try:
            _dm_cls = getattr(sdl2, "SDL_DisplayMode", None)
            _get_dm = getattr(sdl2, "SDL_GetDesktopDisplayMode", None)
            if _dm_cls and _get_dm:
                _dm = _dm_cls()
                try:
                    _dm_ref = ctypes.byref(_dm)
                except TypeError:
                    _dm_ref = _dm
                if _get_dm(0, _dm_ref) == 0:
                    # Knulli / Miyoo Flip fix: propagate refreshed SDL desktop geometry into local module variables
                    if utils.refresh_geometry(int(getattr(_dm, "w", 0) or 0),
                                           int(getattr(_dm, "h", 0) or 0)):
                        global WINDOW_WIDTH, WINDOW_HEIGHT, SCREEN_WIDTH, SCREEN_HEIGHT, UI_SCALE, SCALE_MODE
                        WINDOW_WIDTH = utils.WINDOW_WIDTH
                        WINDOW_HEIGHT = utils.WINDOW_HEIGHT
                        SCREEN_WIDTH = utils.SCREEN_WIDTH
                        SCREEN_HEIGHT = utils.SCREEN_HEIGHT
                        UI_SCALE = utils.UI_SCALE
                        SCALE_MODE = utils.SCALE_MODE
        except Exception:
            pass
        if ttf.TTF_Init() != 0:
            LOG("WARN: TTF_Init failed: %s (app runs without text)" %
                _sdl_err(), "SDL")
            SLOG("Warning: text rendering unavailable")

        # --- window with fallback chain -----------------------------------
        # v0.3.9: the v0.3.7-proven sequence is the PRIMARY path again:
        # SDL_WINDOW_SHOWN + CENTERED at the NATIVE size. v0.3.8 opened
        # the window with SDL_WINDOW_FULLSCREEN_DESKTOP at position (0,0)
        # and on several KMSDRM builds (dArkOSRE's SDL2 among them) that
        # window presents a DEAD surface: the app runs, input works, the
        # panel stays black - the 0.3.8 field report. On 640x480 handhelds
        # this call is byte-identical to v0.3.7; on 1024x768 / 16:9 / 1:1
        # panels the SAME call simply opens at the bigger native size
        # (that is what makes the resolution adaptative).
        self.window = SDL_CreateWindow(
            b"PilasTube",
            SDL_WINDOWPOS_CENTERED, SDL_WINDOWPOS_CENTERED,
            WINDOW_WIDTH, WINDOW_HEIGHT,
            SDL_WINDOW_SHOWN
        )
        if not self.window:
            LOG("window (SHOWN %dx%d) failed: %s - trying FULLSCREEN" %
                (WINDOW_WIDTH, WINDOW_HEIGHT, _sdl_err()), "SDL")
            self.window = SDL_CreateWindow(
                b"PilasTube", 0, 0, WINDOW_WIDTH, WINDOW_HEIGHT,
                SDL_WINDOW_FULLSCREEN)
        if not self.window:
            LOG("window (FULLSCREEN) failed: %s - trying FULLSCREEN_DESKTOP"
                % _sdl_err(), "SDL")
            self.window = SDL_CreateWindow(
                b"PilasTube", 0, 0, WINDOW_WIDTH, WINDOW_HEIGHT,
                SDL_WINDOW_FULLSCREEN_DESKTOP)
        if not self.window:
            LOG("window (FULLSCREEN_DESKTOP) failed: %s - trying logical "
                "size" % _sdl_err(), "SDL")
            self.window = SDL_CreateWindow(
                b"PilasTube", SDL_WINDOWPOS_CENTERED, SDL_WINDOWPOS_CENTERED,
                SCREEN_WIDTH, SCREEN_HEIGHT, 0)
        if not self.window:
            LOG("FATAL: window creation failed: %s" % _sdl_err(), "SDL")
            raise RuntimeError("SDL_CreateWindow failed: %s" % _sdl_err())

        # --- renderer with fallback chain ---------------------------------
        self.renderer = SDL_CreateRenderer(
            self.window, -1,
            SDL_RENDERER_ACCELERATED | SDL_RENDERER_PRESENTVSYNC)
        if not self.renderer:
            LOG("renderer (accel+vsync) failed: %s - trying accel" %
                _sdl_err(), "SDL")
            self.renderer = SDL_CreateRenderer(
                self.window, -1, SDL_RENDERER_ACCELERATED)
        if not self.renderer:
            LOG("renderer (accel) failed: %s - trying software" % _sdl_err(),
                "SDL")
            self.renderer = SDL_CreateRenderer(
                self.window, -1, SDL_RENDERER_SOFTWARE)
        if not self.renderer:
            LOG("renderer (software) failed: %s - trying any" % _sdl_err(),
                "SDL")
            self.renderer = SDL_CreateRenderer(self.window, -1, 0)
        if not self.renderer:
            LOG("FATAL: renderer creation failed: %s" % _sdl_err(), "SDL")
            raise RuntimeError("SDL_CreateRenderer failed: %s" % _sdl_err())
        SDL_SetRenderDrawBlendMode(self.renderer, SDL_BLENDMODE_BLEND)
        # v0.3.8/0.3.9: map the logical coordinate system onto the
        # physical window - ONLY when they actually differ. 640x480
        # devices skip this entirely and keep the exact v0.3.7 render
        # path (identity mapping, no extra SDL state); bigger panels get
        # SDL_RenderSetLogicalSize (fit) / SDL_RenderSetScale (fill) plus
        # the linear scale-quality hint. See utils.apply_logical_mapping.
        self._logical_set = utils.apply_logical_mapping(self.renderer)

        # v0.3.9 diagnostics: record EXACTLY what SDL handed us (window
        # flags + renderer backend) so any future display problem is
        # diagnosable from logs/detailed.txt alone.
        _wflags = "n/a"
        try:
            _gwflags = getattr(sdl2, "SDL_GetWindowFlags", None)
            if _gwflags and self.window:
                _wflags = "0x%08x" % (int(_gwflags(self.window)) &
                                      0xFFFFFFFF)
        except Exception:
            pass
        _rname = "n/a"
        try:
            _info_cls = getattr(sdl2, "SDL_RendererInfo", None)
            _get_ri = getattr(sdl2, "SDL_GetRendererInfo", None)
            if _info_cls and _get_ri and self.renderer:
                _info = _info_cls()
                try:
                    _iref = ctypes.byref(_info)
                except TypeError:
                    _iref = _info
                if _get_ri(self.renderer, _iref) == 0:
                    _n = getattr(_info, "name", None)
                    if _n:
                        _rname = (_n.decode("utf-8", "replace")
                                  if isinstance(_n, bytes) else str(_n))
        except Exception:
            pass
        LOG("window + renderer ready (native %dx%d, logical %dx%d, scale "
            "%.2f, mode %s, mapped=%s, flags=%s, renderer=%s)" %
            (WINDOW_WIDTH, WINDOW_HEIGHT, SCREEN_WIDTH, SCREEN_HEIGHT,
             UI_SCALE, SCALE_MODE, self._logical_set, _wflags, _rname), "SDL")

        # Controller
        self.controller = None
        self.joystick = None
        if SDL_NumJoysticks() > 0:
            if SDL_IsGameController(0):
                self.controller = SDL_GameControllerOpen(0)
                _cname = "FAILED"
                if self.controller:
                    try:
                        _n = SDL_GameControllerName(self.controller)
                        _cname = _n.decode("utf-8", "replace") if _n else "?"
                    except Exception:
                        _cname = "?"
                LOG("game controller opened: %s" % _cname, "SDL")
            else:
                self.joystick = SDL_JoystickOpen(0)
                LOG("joystick opened (raw)", "SDL")
        else:
            LOG("no joysticks detected - keyboard input only", "SDL")

        # Font
        # v0.3.8: fonts are rasterised at PHYSICAL size (design size x
        # UI_SCALE) and draw_text divides the destination rect back to
        # logical coordinates - text occupies the same layout space as on
        # a 640x480 screen but renders pixel-crisp at native resolution.
        font_path = self._find_font()
        LOG("font file: %s" % (font_path or "NONE FOUND"), "SDL")
        self.font = self.font_large = self.font_small = self.font_tiny = None
        if font_path:
            def _fsize(n):
                return max(8, int(round(n * UI_SCALE)))
            self.font = ttf.TTF_OpenFont(font_path.encode(), _fsize(18))
            self.font_large = ttf.TTF_OpenFont(font_path.encode(), _fsize(24))
            self.font_small = ttf.TTF_OpenFont(font_path.encode(), _fsize(14))
            self.font_tiny = ttf.TTF_OpenFont(font_path.encode(), _fsize(12))
        if self.font:
            LOG("ttf fonts opened (design 18/24/14/12 x scale %.2f)" %
                UI_SCALE, "SDL")
        else:
            LOG("WARN: no font loaded - UI text will be invisible", "SDL")
            SLOG("Warning: no font file found - UI text missing")

        # Caches
        self.text_cache = {}
        self.image_cache = {}
        self.failed_images = set()
        self.loading_images = set()
        self.image_cache_dir = os.path.join(SCRIPT_DIR, ".thumb_cache")
        os.makedirs(self.image_cache_dir, exist_ok=True)

        if SDL_IMAGE_AVAILABLE:
            try:
                sdlimage.IMG_Init(sdlimage.IMG_INIT_JPG | sdlimage.IMG_INIT_PNG)
                LOG("SDL_image initialised (jpg+png)", "SDL")
            except Exception as _e:
                LOG("WARN: IMG_Init: %s" % _e, "SDL")

        # Preferences + theme
        self.prefs = YX.Preferences()
        self._apply_theme()
        # v3.2: activate the SmartTube-style network route (Default / Cronet
        # / OkHttp) for every net_get call in yt_extras
        try:
            YX.set_active_route(self.prefs.get("route", "Default"))
        except Exception:
            pass
        LOG("prefs loaded from %s (first_boot_done=%s, language=%s)" %
            (self.prefs.path, self.prefs.get("first_boot_done", "0"),
             self.prefs.get("language", "English")))

        # Services
        self.subs = YX.SubscriptionsManager(self.prefs)
        self.sponsorblock = YX.SponsorBlockClient(self.prefs)
        self.dearrow = YX.DeArrowClient(self.prefs)
        self.ryd = YX.RYDClient(self.prefs)

        # State
        self.running = True
        self.need_redraw = True
        self.frame_count = 0

        self.current_nav = NAV_HOME
        self.selected = 0
        self.scroll = 0

        self.ytdlp_path = YTDLP_PATH
        self.video_player = VIDEO_PLAYER

        # Data lists
        self.home_videos = []          # real Trending feed
        self.sub_videos = []           # subscriptions feed
        self.search_results = []
        self.favorites = self._load_json("yt_favorites.json")
        self.history = self._load_json("yt_history.json")
        self.queue = []                # playback queue (VideoItems)
        self.positions = self._load_positions()
        self.blocked = self._load_blocked()
        self.search_history = YX.load_search_history()
        self.last_search_query = ""

        # batch loading
        self.home_batch = 1
        self.search_batch = 1
        self.home_batch_loading = False
        self.search_batch_loading = False
        self.home_first_batch_count = 0
        self.search_first_batch_count = 0
        self.home_existing_ids = set()
        self.search_existing_ids = set()
        self.subs_loading = False
        self.home_feed_failed = False      # v2.2: last trending load failed
        self.home_fail_reason = ""
        self.home_feed_source = ""         # which chain step produced the feed
        # v3.3: account home/recommended feed cache
        self._account_home_at = 0.0
        self._account_home_loading = False

        # v3.4 Categories tab state
        self.category_open = None      # None = category list; else (key, src)
        self.category_videos = []
        self.category_batch = 1
        self.category_batch_loading = False
        self.category_existing_ids = set()
        self.category_failed = False
        self.category_fail_reason = ""

        # WiFi indicator state (v2.2)
        self.wifi_level = 0
        self.wifi_connected = False
        self._wifi_next_check = 0.0

        # v3.6 network watchdog: real internet connectivity (not just the
        # wifi interface being "up"). While offline the app keeps running,
        # shows a reconnecting screen and auto-retries the interrupted
        # operation the moment the connection returns.
        self.net_offline = False
        self.net_attempts = 0          # probe rounds since going offline
        self._net_pending = None       # callable re-run when back online
        self._net_watch_started = False
        self._net_last_change = 0.0

        # Settings screen (v3.3: two-pane, section list left + rows right,
        # value picker overlay - the screen can NEVER scroll)
        self.settings_section = 0     # index into settings_sections
        self.settings_pane = "left"   # which pane has focus
        self.settings_row = 0         # row index inside the section
        self.settings_picker = None   # {label, key, options, selected, row}
        self.settings_sections = []
        # legacy aliases kept so old tests / save code keep working
        self.settings_selected = 0
        self.settings_scroll = 0
        self._update_settings_items()
        # v3.3 account state (restored from oauth_token.json at startup)
        self.account_name = ""
        self.account_avatar = ""
        self.login_active = False
        self.login_state = {}
        self.login_cancel = None
        self.account_feed_fallback = False   # True when authed feed failed
        self.account_history = []
        self.account_history_loading = False
        self.account_history_at = 0.0
        self._account_subs_at = 0.0
        self.ytdlp_ver = YX.ytdlp_version(self.ytdlp_path)

        # Status bar
        status_parts = []
        status_parts.append("yt-dlp %s" % self.ytdlp_ver if self.ytdlp_path else "NO yt-dlp!")
        if self.video_player:
            status_parts.append("Player: %s" % os.path.basename(self.video_player))
        else:
            status_parts.append("NO player!")
        self.status = " | ".join(status_parts)
        self.status_type = "ok" if (self.ytdlp_path and self.video_player) else "error"
        self.is_loading = False

        # Search keyboard
        self.search_active = False
        self.search_query = ""
        self.keyboard_row = 0
        self.keyboard_col = 0
        self.caps_lock = False
        self.sym_page = False
        self.keyboard_mode = "search"     # or "proxy"
        self.keyboard_layout = [
            list("1234567890"),
            list("qwertyuiop"),
            list("asdfghjkl"),
            list("zxcvbnm"),
        ]
        self.symbol_layout = [
            list("@#$%&*+-._"),
            list("!?,.'\"/:;("),
            list("0123456789"),
            list("[]{}<>"),
        ]

        # suggestions overlay
        self.sugg_visible = False
        self.sugg_items = []              # list of strings
        self.sugg_selected = 0
        self.sugg_loading = False
        self.sugg_fetched_for = ""
        self._suggest_thread = None

        # input repeat
        self.key_held = None
        self.key_hold_start = 0
        self.last_repeat = 0

        # v3.1 direction gate - ONE edge-triggered debouncer for every
        # direction source (controller buttons, joystick hats, analog
        # stick axes, keyboard arrows). A direction only acts on its
        # press TRANSITION and at most once per cooldown window; the
        # held flag auto-expires and is verified against the live
        # hardware state, so neither event floods (settings "runaway",
        # seek storm) nor lost release events can lock anything up.
        self._dir_held = {}        # "up"/"down"/"left"/"right" -> ms pressed
        self._dir_last = {}        # direction -> ms of last accepted action
        self._hat_prev = {}        # joystick instance id -> last hat value
        self._axis_dir = {}        # axis index -> "left"/"right"/"up"/"down"
        self._kb_dir = {}          # keyboard direction -> held?
        self._truth_next_ms = 0    # next hardware truth-check timestamp
        # generic per-action debounce (A/B/X/Y/START/SELECT...)
        self._act_last = {}
        # HUD options-row focus (SmartTube bottom bar navigation)
        self.hud_focus = 2         # defaults to the play/pause button
        self._hud_last_seek_ms = 0

        # playback
        self.is_playing = False
        self.is_loading_video = False
        self.is_searching = False
        self.player_process = None
        self.current_video = None
        self.player_paused = False
        self.mpv_socket = None
        self.mpv_query_id = 0
        self.session_quality = None      # per-session quality override
        self.session_codec = None         # v3.2: per-session codec override
        self.session_audio_lang = None    # v3.6: per-session audio language
        self.current_speed = 1.0
        self.current_chapters = []
        self.current_segments = []       # sponsorblock segments
        self.last_time_pos = 0.0
        self.last_duration = 0.0
        self.user_stopped = True         # False while auto-chain allowed
        self.monitor_thread = None
        self.sb_skipped_ids = set()
        self.sleep_deadline = None
        self.next_info = None            # (title, height, note) for loading screen
        self.loading_ryd = None
        self._skip_to_next = False
        self._restart_requested = False
        self.last_subs_refresh_forced = False

        # v3.0 built-in player state
        self.player = None               # FFPlayer while playing
        self.audio_dev = None            # SDL audio device id
        self.audio_driver_ok = True      # False when no audio device at all
        self.play_info = None            # yt-dlp info dict of current video
        self.player_hw = (640, 360)      # video w/h of current stream
        self.player_fps = 30.0
        self.hud_visible = True          # SmartTube-style controls overlay
        self.hud_last_activity = 0
        self.player_toast = None         # (text, until_ticks, color)
        self.player_menu = None          # "quality" | "speed" | "options" |
                                         # "chapters" | "captions"
        self.player_menu_sel = 0
        self.player_stats = False        # stats-for-nerds overlay
        self.player_loop = False
        self.autoplay_countdown = None   # (video, deadline_ticks)
        self.player_volume_pct = 100
        self._trig_armed = {4: True, 5: True}   # L2/R2 volume-repeat state
        self.player_start_pos = 0.0
        self._player_started_at = 0
        self._sb_last_shown = 0.0
        self._player_audio_warned = False
        self.battery_pct = None
        self.battery_charging = False
        self._battery_next_check = 0.0

        # overlays
        self.ctx_open = False            # video context menu
        self.ctx_items = []
        self.ctx_selected = 0
        self.ctx_video = None
        self.queue_open = False
        self.queue_selected = 0
        self.channel_view = None         # {"title", "videos": [], "channel_id"}
        self.channel_loading = False
        self.channel_prev_nav = None
        self.info_open = False
        self.info_video = None
        self.info_ryd = None

        # first-boot wizard
        self.wizard_active = self.prefs.get("first_boot_done", "0") != "1"
        self.wizard_step = 0
        self.wizard_choice = 0
        if self.wizard_active:
            LOG("first-boot wizard will run", "WIZARD")
            SLOG("First-run setup wizard started")

        # v0.3.8: yt-dlp background update check -> Yes/No popup.
        # _ytdlp_update_offer is set by the check thread; the main loop
        # turns it into self.update_popup once the UI is idle.
        self._ytdlp_update_offer = None      # (current, latest) or None
        self._ytdlp_check_started = False
        self.update_popup = None             # {"current","latest","choice"}

        # loading spinner sticky flag
        self.loading_spinner_triggered = False

        LOG("app initialised - yt-dlp: %s | player: %s | prefs: %s" %
            (self.ytdlp_path, self.video_player, self.prefs.path))
        LOG("yt-dlp version: %s" % self.ytdlp_ver, "YTDLP")
        print("PilasTube %s" % APP_VERSION)
        print("yt-dlp: %s" % self.ytdlp_path)
        print("Player: %s" % self.video_player)
        print("Prefs: %s" % self.prefs.path)

    # ------------------------------------------------------------- json store
    def _load_json(self, filename):
        try:
            path = os.path.join(SCRIPT_DIR, filename)
            if os.path.exists(path):
                with open(path, "r", encoding="utf-8") as f:
                    return [VideoItem(v) for v in json.load(f)]
        except Exception as e:
            print("Load %s error: %s" % (filename, e))
        return []

    def _save_json(self, filename, items):
        try:
            path = os.path.join(SCRIPT_DIR, filename)
            with open(path, "w", encoding="utf-8") as f:
                json.dump([v.to_dict() for v in items[:60]], f, ensure_ascii=False)
        except Exception as e:
            print("Save %s error: %s" % (filename, e))

    def _load_positions(self):
        try:
            path = os.path.join(SCRIPT_DIR, "yt_positions.json")
            if os.path.exists(path):
                with open(path, "r", encoding="utf-8") as f:
                    return json.load(f)
        except Exception:
            pass
        return {}

    def _save_positions(self):
        try:
            path = os.path.join(SCRIPT_DIR, "yt_positions.json")
            with open(path, "w", encoding="utf-8") as f:
                json.dump(self.positions, f)
        except Exception as e:
            print("positions save error: %s" % e)

    def _load_blocked(self):
        try:
            path = os.path.join(SCRIPT_DIR, "yt_blocked.json")
            if os.path.exists(path):
                with open(path, "r", encoding="utf-8") as f:
                    return json.load(f)
        except Exception:
            pass
        return []

    def _save_blocked(self):
        try:
            path = os.path.join(SCRIPT_DIR, "yt_blocked.json")
            with open(path, "w", encoding="utf-8") as f:
                json.dump(self.blocked, f, ensure_ascii=False)
        except Exception as e:
            print("blocked save error: %s" % e)

    def is_blocked(self, video):
        cid = video.channel_id if hasattr(video, "channel_id") else ""
        name = (video.channel or "").lower()
        for b in self.blocked:
            if (cid and b.get("id") == cid) or (name and b.get("name", "").lower() == name):
                return True
        return False

    # -------------------------------------------------------------- translate
    def t(self, key):
        lang = self.prefs.get("language", "English")
        if lang in TRANSLATIONS and key in TRANSLATIONS[lang]:
            return TRANSLATIONS[lang][key]
        return TRANSLATIONS["English"].get(key, key)

    def set_status(self, text, stype="ok"):
        self.status = text
        self.status_type = stype
        self.need_redraw = True

    # ------------------------------------------------------------- history
    def add_to_history(self, video):
        self.history = [v for v in self.history if v.id != video.id]
        self.history.insert(0, video)
        self._save_json("yt_history.json", self.history)

    def get_position(self, video_id):
        pos = self.positions.get(video_id)
        if not pos:
            return None
        try:
            return float(pos[0]), float(pos[1])
        except (TypeError, ValueError, IndexError):
            return None

    def save_position(self, video_id, pos, duration):
        if not video_id:
            return
        try:
            pos = float(pos or 0)
            duration = float(duration or 0)
        except (TypeError, ValueError):
            return
        if duration > 0 and pos >= duration * 0.95:
            self.positions.pop(video_id, None)   # fully watched
        elif pos > 5:
            self.positions[video_id] = [pos, duration]
        else:
            self.positions.pop(video_id, None)
        self._save_positions()

    # =====================================================================
    # FIRST-BOOT WIZARD
    # =====================================================================
    def wizard_options(self, step):
        """Options list for the current wizard step."""
        key = WIZARD_STEPS[step]
        if key == "language":
            return LANGUAGES
        if key == "device":
            return WIZARD_DEVICES
        if key == "quality":
            return QUALITY_OPTIONS
        if key == "hwdec":
            return [self.t("settings_on"), self.t("settings_off")]
        if key == "sponsorblock":
            return ["Off", "Minimal", "Core", "All"]
        if key == "done":
            return [self.t("wiz_finish")]
        return []

    def wizard_store(self, step, value):
        key = WIZARD_STEPS[step]
        if key == "language":
            self.prefs.set("language", value, save=False)
            self.text_cache.clear()
        elif key == "device":
            self.prefs.set("device", value, save=False)
        elif key == "quality":
            self.prefs.set("quality", value, save=False)
        elif key == "hwdec":
            self.prefs.set("hwdec", "On" if value == self.t("settings_on") else "Off", save=False)
        elif key == "sponsorblock":
            self.prefs.set("sponsorblock", value, save=False)

    def wizard_advance(self):
        """A pressed on current selection."""
        opts = self.wizard_options(self.wizard_step)
        if not opts:
            return
        value = opts[self.wizard_choice]
        key = WIZARD_STEPS[self.wizard_step]
        if key == "done":
            self.prefs.set("first_boot_done", "1", save=False)
            self.prefs.set("wizard_date", time.strftime("%Y-%m-%d"), save=False)
            self.prefs.set("app_version", APP_VERSION, save=False)
            self.prefs.save()
            self.wizard_active = False
            self._update_settings_items()
            self.set_status("Ready")
            LOG("first-boot wizard completed", "WIZARD")
            SLOG("Setup wizard completed")
            return
        self.wizard_store(self.wizard_step, value)
        self.wizard_step += 1
        self.wizard_choice = 0
        self.need_redraw = True

    def wizard_back(self):
        if self.wizard_step > 0:
            self.wizard_step -= 1
            self.wizard_choice = 0
            self.need_redraw = True

    def wizard_move(self, delta):
        opts = self.wizard_options(self.wizard_step)
        if not opts:
            return
        self.wizard_choice = (self.wizard_choice + delta) % len(opts)
        self.need_redraw = True

    # =====================================================================
    # FEEDS: Trending (multi-source fallback chain), honest search
    # pagination, subscriptions, channel browsing
    # =====================================================================
    def _run_ytdlp(self, args, timeout=60):
        cmd = [self.ytdlp_path] + args
        result = subprocess.run(cmd, stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE,
                                universal_newlines=True, timeout=timeout)
        # v2.2: never swallow failures silently - a nonzero exit or an
        # empty dump with stderr output is logged so logs/detailed.txt
        # always explains WHY a feed/search came back empty.
        try:
            out = (result.stdout or "").strip()
            if result.returncode != 0 or not out:
                tail = " | ".join(
                    [l for l in (result.stderr or "").strip().split("\n")
                     if l.strip()][-3:])[:300]
                LOG("yt-dlp rc=%s out_lines=%d tail='%s' args=%s" %
                    (result.returncode,
                     len([l for l in out.split("\n") if l.strip()]),
                     tail, " ".join(args[-3:])), "YTDLP")
        except Exception:
            pass
        return result

    def _ytdlp_args(self, for_video=False):
        return YX.ytdlp_common_args(self.prefs, for_video=for_video)

    # ---- v3.6 network watchdog -------------------------------------------
    def start_net_watch(self):
        """Launch the connectivity watchdog (once). A daemon thread probes
        the internet every ~4s: while offline it keeps the reconnecting
        overlay alive and counts attempts; the moment connectivity returns
        it flips the state and the MAIN loop re-runs the interrupted
        operation (never a worker thread - only the main thread renders)."""
        if self._net_watch_started:
            return
        self._net_watch_started = True
        run_logged_thread("net-watch", self._net_watch_worker, daemon=True)

    def _net_watch_worker(self):
        while self.running:
            try:
                # The probe is the ONLY source of truth (never the wifi
                # interface state: ethernet-only test setups / USB NICs
                # report no wlan yet route perfectly).
                ok = YX.probe_online(
                    timeout=4, proxy=self.prefs.get("proxy", ""))
            except Exception:
                ok = False
            was = self.net_offline
            self.net_offline = not ok
            if not ok:
                self.net_attempts += 1
                if not was:
                    self._net_last_change = time.time()
                    LOG("network OFFLINE - watchdog active "
                        "(auto-retry queued)", "NET")
                    try:
                        self.set_status(self.t("msg_reconnecting"), "error")
                    except Exception:
                        pass
                    self.need_redraw = True
                else:
                    # periodic nudges so the attempt counter updates
                    self.need_redraw = True
            else:
                if was:
                    self._net_last_change = time.time()
                    LOG("network back ONLINE after %d probes" %
                        self.net_attempts, "NET")
                    self.net_attempts = 0
                    try:
                        self.set_status(self.t("msg_back_online"), "success")
                    except Exception:
                        pass
                    self.need_redraw = True
            time.sleep(4)

    def net_run_pending(self):
        """Main-loop hook: re-run the operation that was interrupted when
        the connection dropped (only after connectivity is confirmed)."""
        if self._net_pending is None or self.net_offline:
            return False
        pending, self._net_pending = self._net_pending, None
        try:
            LOG("network recovered - retrying interrupted operation", "NET")
            pending()
        except Exception as e:
            LOG("pending retry failed: %s" % e, "NET")
        return True

    def _net_fail(self, exc, pending):
        """Worker-thread helper: register a pending retry when a failure
        looks like a connectivity drop; returns True when the offline
        state was entered (callers should stop retrying)."""
        if self.net_offline:
            self._net_pending = pending
            return True
        if exc is not None and YX.net_looks_offline(exc):
            try:
                if not YX.probe_online(timeout=4,
                                       proxy=self.prefs.get("proxy", "")):
                    self.net_offline = True
                    self.net_attempts += 1
                    self._net_pending = pending
                    LOG("feed op failed offline (%s) - watchdog takes over"
                        % str(exc)[:60], "NET")
                    self.set_status(self.t("msg_reconnecting"), "error")
                    self.need_redraw = True
                    return True
            except Exception:
                pass
        return False

    # ---- Recommended (home feed) ----------------------------------------
    # v2.2 history: YouTube removed /feed/trending for API clients (it
    # redirects to the home page, so yt-dlp returns nothing - that's why the
    # old Trending tab used public APIs).
    # v3.4: the first tab is now RECOMMENDED (SmartTube home). The feed is
    # built from a chain:
    #   batch 1: account home feed (signed in, SmartTube's FEwhat_should_watch)
    #            -> anonymous keyless home -> Piped/Invidious trending APIs
    #            -> Top-100 charts playlist -> local disk cache
    #            (with an on-screen [A] retry on fail)
    #   batch 2: Piped/Invidious trending (extends the feed)
    #   batch 3: Top-100 charts playlist (first slice)
    #   batch 4: Top-100 charts playlist (second slice)
    #   batch 5: trending gaming search mix
    TRENDING_SOURCES = [
        {"kind": "home", "label": "Recommended"},
        {"kind": "api", "label": "Trending"},
        {"kind": "charts", "label": "Music Top 100 (1)",
         "items": "1:24"},
        {"kind": "charts", "label": "Music Top 100 (2)",
         "items": "25:48"},
        {"kind": "search", "label": "Trending Gaming",
         "query": "trending gaming this week"},
    ]

    def _trend_region(self):
        return YX.trend_region_for_language(self.prefs.get("language", "English"))

    def load_trending(self):
        """v3.4: load the RECOMMENDED feed (kept under the old name for the
        saved state + tests)."""
        if self.prefs.get("auto_load", "On") == "Off":
            LOG("trending skipped: auto_load=Off", "FEED")
            return
        LOG("loading trending feed (batch 1)...", "FEED")
        SLOG("Loading Trending...")
        self.home_batch = 1
        self.home_existing_ids = set()
        self.home_first_batch_count = 0
        self.home_videos = []
        self.home_feed_failed = False
        self.home_fail_reason = ""
        # close stale overlays pointing at the old feed and reset selection
        self.ctx_open = False
        self.queue_open = False
        self.info_open = False
        self.selected = 0
        self.scroll = 0
        self.is_loading = True
        self.set_status(self.t("msg_loading_videos"), "loading")
        self.render()
        self._load_trending_batch(1)

    def _feed_add_items(self, dicts):
        """Append normalised video dicts to the home feed (dedup-safe)."""
        added = 0
        for d in dicts:
            vid = d.get("id")
            if not vid or vid in self.home_existing_ids:
                continue
            self.home_existing_ids.add(vid)
            self.home_videos.append(VideoItem(d))
            added += 1
        return added

    def _load_trending_batch(self, batch_num):
        if self.home_batch_loading:
            return
        if batch_num > len(self.TRENDING_SOURCES):
            self.set_status("%d %s" % (len(self.home_videos), self.t("msg_videos")))
            return
        self.home_batch_loading = True
        src = self.TRENDING_SOURCES[batch_num - 1]

        def worker():
            reason = ""
            try:
                # v3.6: fast-fail while offline - the watchdog auto-retries
                # the whole chain the moment the connection returns
                if self.net_offline:
                    self.home_batch_loading = False
                    if batch_num == 1:
                        self.is_loading = False
                    self._net_pending = lambda: self.load_trending()
                    self.set_status(self.t("msg_reconnecting"), "error")
                    self.need_redraw = True
                    return
                if src["kind"] == "home":
                    self._recommended_from_home()
                elif src["kind"] == "api":
                    self._trending_from_api()
                elif src["kind"] == "charts":
                    added = self._trending_from_charts(src["items"])
                    if not self.home_videos:
                        reason = "charts playlist returned no videos"
                elif src["kind"] == "search":
                    added = self._trending_from_search(src["query"])
                    if not self.home_videos:
                        reason = "search mix returned no videos"
                self.home_batch = batch_num
                self.home_batch_loading = False
                self.loading_spinner_triggered = False
                if batch_num == 1:
                    self.home_first_batch_count = len(self.home_videos)
                    self.is_loading = False
                    if not self.home_videos:
                        # every live source failed -> try the disk cache
                        self._trending_from_cache()
                if self.home_videos:
                    if self.home_feed_source:
                        self.set_status("%d %s (%s)" % (
                            len(self.home_videos), self.t("msg_videos"),
                            self.home_feed_source))
                    else:
                        self.set_status("%d %s" % (
                            len(self.home_videos), self.t("msg_videos")))
                    self.home_feed_failed = False
                    if batch_num == 1:
                        YX.save_home_cache(
                            [v.to_dict() for v in self.home_videos],
                            self.home_feed_source)
                else:
                    self.home_feed_failed = True
                    self.home_fail_reason = reason or "no results"
                    LOG("trending FAILED - reason: %s" % self.home_fail_reason,
                        "FEED")
                    # v3.6: if this was a connectivity drop, the watchdog
                    # owns the retry (no dead "failed" screen)
                    if self._net_fail(
                            RuntimeError(self.home_fail_reason),
                            lambda: self.load_trending()):
                        self.need_redraw = True
                        return
                    if not self.wifi_connected:
                        self.set_status(self.t("msg_no_internet"), "error")
                    else:
                        self.set_status(self.t("msg_feed_failed"), "error")
                self.need_redraw = True
            except subprocess.TimeoutExpired as e:
                self.home_batch_loading = False
                if batch_num == 1:
                    self.is_loading = False
                    self.home_feed_failed = True
                    self.home_fail_reason = "timeout"
                    if self._net_fail(e, lambda: self.load_trending()):
                        self.need_redraw = True
                        return
                    self.set_status(self.t("msg_timeout"), "error")
                self.need_redraw = True
            except Exception as e:
                self.home_batch_loading = False
                if batch_num == 1:
                    self.is_loading = False
                    self.home_feed_failed = True
                    self.home_fail_reason = str(e)[:80]
                    if self._net_fail(e, lambda: self.load_trending()):
                        self.need_redraw = True
                        return
                    self.set_status("Error: %s" % str(e)[:24], "error")
                self.need_redraw = True

        run_logged_thread("home-batch", worker)

    def _recommended_from_home(self):
        """v3.4 batch 1: the SmartTube home/recommended feed.

        Signed in -> the account's personalised home feed (v0.3.7: browseId
        'default', SmartTube's exact TV home query, with the full TV app
        context + X-Goog-Pageid so YouTube returns the real feed instead of
        the anonymous shell); logged out -> anonymous keyless home (WEB
        client); both fall through to the public-API trending chain so the
        first tab is never empty."""
        hl = YX.YTDLP_LANG.get(self.prefs.get("language", "English"), "en")
        gl = self._trend_region()
        # 1) signed-in account home (cache 10 min)
        if self._account_ready():
            try:
                items = YX.get_auth().fetch_account_feed("home",
                                                         hl=hl, gl=gl)
                if items:
                    added = self._feed_add_items(items)
                    if added:
                        self.home_feed_source = "account"
                        self._account_home_at = time.time()
                        LOG("account home feed: %d items" % added, "AUTH")
                        return
                LOG("account home feed empty - falling through", "AUTH")
            except Exception as e:
                LOG("account home feed failed: %s" % e, "AUTH")
        # 2) anonymous keyless home (v3.6: WEB client, browser headers)
        try:
            items = YX.fetch_keyless_feed("FEwhat_to_watch", hl=hl, gl=gl)
            if items:
                added = self._feed_add_items(items)
                if added:
                    self.home_feed_source = "home"
                    LOG("keyless home feed: %d items" % added, "FEED")
                    return
            else:
                LOG("keyless home feed: 0 items", "FEED")
        except Exception as e:
            LOG("keyless home feed failed: %s" % e, "FEED")
        # 3) public-API trending chain (itself falls back to charts)
        LOG("home feeds unavailable - falling back to trending APIs", "FEED")
        self._trending_from_api()

    def _trending_from_api(self):
        """Chain step 1+2: Piped / Invidious public trending APIs."""
        region = self._trend_region()
        LOG("trending: public APIs (region=%s)" % region, "FEED")
        self.set_status(self.t("msg_loading_videos"), "loading")
        items, label = YX.fetch_api_trending(
            region,
            proxy=self.prefs.get("proxy", ""),
            prefer_ipv4=self.prefs.get("prefer_ipv4", "Off") == "On")
        LOG("trending api source=%s items=%d" % (label, len(items)), "FEED")
        if items:
            added = self._feed_add_items(items)
            if added:
                self.home_feed_source = label.split(":")[0]
                return
        # API down -> fall straight through to the charts playlist so the
        # user still gets a full grid of playable videos.
        LOG("trending api failed (%s) - falling back to charts playlist" % label,
            "FEED")
        self._trending_from_charts("1:24")

    def _trending_from_charts(self, items_spec):
        """Chain step 3: YouTube Top-100 music charts via yt-dlp."""
        if not self.ytdlp_path:
            return 0
        args = self._ytdlp_args() + [
            "--flat-playlist", "--dump-json",
            "--playlist-items", items_spec, YX.charts_playlist_url()]
        result = self._run_ytdlp(args, timeout=45)
        added = self._ingest_flat(result, self.home_videos,
                                  self.home_existing_ids)
        LOG("trending charts items=%s added=%d" % (items_spec, added), "FEED")
        if added:
            self.home_feed_source = "charts"
        return added

    def _trending_from_search(self, query):
        """Chain step 4: search-based trending mix (last live resort)."""
        if not self.ytdlp_path:
            return 0
        args = self._ytdlp_args() + [
            "--flat-playlist", "--dump-json",
            "ytsearch24:%s" % query]
        result = self._run_ytdlp(args, timeout=45)
        added = self._ingest_flat(result, self.home_videos,
                                  self.home_existing_ids)
        LOG("trending search-mix added=%d" % added, "FEED")
        if added:
            self.home_feed_source = "search"
        return added

    def _trending_from_cache(self):
        """Final resort: last successful feed from disk (offline rescue)."""
        dicts, ts = YX.load_home_cache()
        if dicts:
            self._feed_add_items(dicts[:30])
            self.home_feed_source = "%s %s" % (
                self.t("msg_cached"),
                time.strftime("%d/%m %H:%M", time.localtime(ts))
                if ts else "")
            LOG("trending served from disk cache (%d videos)" % len(dicts),
                "FEED")

    def _ingest_flat(self, result, target_list, existing_ids):
        """Parse --dump-json (one JSON per line) into target list."""
        added = 0
        for line in (result.stdout or "").strip().split("\n"):
            line = line.strip()
            if not line:
                continue
            try:
                data = json.loads(line)
            except ValueError:
                continue
            vid_id = data.get("id")
            if not vid_id or vid_id in existing_ids:
                continue
            # skip channel / playlist headers from search results
            if data.get("_type") in ("playlist", "url") and not data.get("duration") \
                    and not data.get("live_status"):
                continue
            existing_ids.add(vid_id)
            target_list.append(VideoItem(data))
            added += 1
        return added

    # ---- Categories tab (v3.4, SmartTube "Explore"-style) -----------------
    def category_title(self, key):
        return self.t("cat_%s" % key)

    def _category_def(self, key):
        for k, _icon, src in CATEGORY_DEFS:
            if k == key:
                return src
        return "search"

    def open_category(self, key):
        """A on a category tile: load that category's videos. B returns to
        this list (see action_back)."""
        src = self._category_def(key)
        self.category_open = (key, src)
        self.category_videos = []
        self.category_batch = 1
        self.category_existing_ids = set()
        self.category_failed = False
        self.category_fail_reason = ""
        self.selected = 0
        self.scroll = 0
        self.ctx_close()
        self.queue_open = False
        self.info_open = False
        if src == "favorites":
            # local list - no loading screen, no network
            self.category_videos = [v for v in self.favorites
                                    if not self.is_blocked(v)]
            self.set_status("%d %s" % (len(self.category_videos),
                                       self.t("msg_videos")))
            self.need_redraw = True
            return
        self.is_loading = True
        self.set_status(self.t("msg_loading_videos"), "loading")
        self.render()
        self._load_category_batch(1)

    def close_category(self):
        """B inside a category video list: back to the category tiles."""
        self.category_open = None
        self.category_videos = []
        self.selected = 0
        self.scroll = 0
        self.need_redraw = True

    def _load_category_batch(self, batch_num):
        if self.category_batch_loading or not self.category_open:
            return
        key, src = self.category_open
        self.category_batch_loading = True

        def worker():
            try:
                # v3.6: fast-fail while offline; watchdog re-opens the
                # category when the connection returns
                if self.net_offline:
                    if batch_num == 1:
                        self.category_failed = False
                    self._net_pending = lambda: self.open_category(key)
                    self.set_status(self.t("msg_reconnecting"), "error")
                    return
                if src == "trending":
                    region = self._trend_region()
                    items, label = YX.fetch_api_trending(
                        region,
                        proxy=self.prefs.get("proxy", ""),
                        prefer_ipv4=self.prefs.get("prefer_ipv4", "Off") == "On")
                    LOG("category trending source=%s items=%d" % (
                        label, len(items)), "FEED")
                    if not items:
                        self.category_failed = True
                        self.category_fail_reason = label
                    else:
                        for d in items:
                            if d.get("id") not in self.category_existing_ids:
                                self.category_existing_ids.add(d["id"])
                                self.category_videos.append(VideoItem(d))
                elif src == "charts":
                    if self.ytdlp_path:
                        args = self._ytdlp_args() + [
                            "--flat-playlist", "--dump-json",
                            "--playlist-items", "1:30",
                            YX.charts_playlist_url()]
                        result = self._run_ytdlp(args, timeout=45)
                        self._ingest_flat(result, self.category_videos,
                                          self.category_existing_ids)
                else:   # search with a server-side filter token
                    if self.ytdlp_path:
                        url = YX.category_search_url(
                            key, self.prefs.get("language", "English"))
                        rng = "%d:%d" % ((batch_num - 1) * 15 + 1,
                                         batch_num * 15)
                        args = self._ytdlp_args() + [
                            "--flat-playlist", "--dump-json",
                            "--playlist-items", rng, url]
                        result = self._run_ytdlp(args, timeout=45)
                        self._ingest_flat(result, self.category_videos,
                                          self.category_existing_ids)
                self.category_batch = batch_num
                if not self.category_videos and not self.category_failed:
                    self.category_failed = True
                    self.category_fail_reason = "no results"
                if self.category_videos:
                    # v3.6: page-aware status like search
                    self.set_status(self._page_label(
                        batch_num, self.category_videos))
                elif self._net_fail(
                        RuntimeError(self.category_fail_reason or "empty"),
                        lambda: self.open_category(key)):
                    return
                elif self.wifi_connected:
                    self.set_status(self.t("msg_cat_empty"), "error")
                else:
                    self.set_status(self.t("msg_no_internet"), "error")
            except subprocess.TimeoutExpired as e:
                self.category_failed = True
                self.category_fail_reason = "timeout"
                if not self._net_fail(e, lambda: self.open_category(key)):
                    self.set_status(self.t("msg_timeout"), "error")
            except Exception as e:
                self.category_failed = True
                self.category_fail_reason = str(e)[:80]
                if not self._net_fail(e, lambda: self.open_category(key)):
                    self.set_status("Error: %s" % str(e)[:24], "error")
            finally:
                self.category_batch_loading = False
                self.is_loading = False
                self.loading_spinner_triggered = False
                self.need_redraw = True

        run_logged_thread("category-batch", worker)

    # ---- Search (honest pagination via --playlist-items) -----------------
    def search_youtube(self, query):
        LOG("search: %r" % query[:60], "SEARCH")
        SLOG("Searching: %s" % query[:60])
        if not self.ytdlp_path:
            self.set_status(self.t("msg_no_ytdlp"), "error")
            return
        query = (query or "").strip()
        if not query:
            return
        self.last_search_query = query
        self.search_batch = 1
        self.search_existing_ids = set()
        self.search_first_batch_count = 0
        self.search_results = []
        self.selected = 0
        self.scroll = 0
        self.current_nav = NAV_SEARCH
        self.search_active = False
        self.sugg_visible = False

        # remember search history
        if query in self.search_history:
            self.search_history.remove(query)
        self.search_history.insert(0, query)
        self.search_history = self.search_history[:12]
        YX.save_search_history(self.search_history)

        self.is_loading = True
        self.is_searching = True
        self.set_status(self.t("msg_searching"), "loading")
        self._load_search_batch(1)

    def _search_count(self):
        try:
            return max(1, int(self.prefs.get("search_count", "16")))
        except ValueError:
            return 16

    def _page_label(self, batch, videos):
        """"Página N - X vídeos" for the status line (v3.6: search results
        arrive as pages of search_count (16 by default) and the user must
        always see WHICH page they're on). `videos` is the list or its
        length."""
        count = videos if isinstance(videos, int) else len(videos)
        return "%s %d - %d %s" % (self.t("msg_page"), batch, count,
                                  self.t("msg_videos"))

    def _load_search_batch(self, batch_num):
        if self.search_batch_loading:
            return
        self.search_batch_loading = True
        count = self._search_count()
        total = batch_num * count
        start = (batch_num - 1) * count + 1
        end = batch_num * count

        def worker():
            try:
                # v3.6: fast-fail while offline (the watchdog auto-retries
                # when the connection returns instead of stacking 60s of
                # subprocess timeouts)
                if self.net_offline:
                    self.search_batch_loading = False
                    if batch_num == 1:
                        self.is_loading = False
                        self.is_searching = False
                    self._net_pending = lambda: self.search_youtube(
                        self.last_search_query)
                    self.set_status(self.t("msg_reconnecting"), "error")
                    self.need_redraw = True
                    return
                query = "ytsearch%d:%s" % (total, self.last_search_query)
                args = self._ytdlp_args() + [
                    "--flat-playlist", "--dump-json",
                    "--playlist-items", "%d:%d" % (start, end), query]
                result = self._run_ytdlp(args, timeout=60)
                before = len(self.search_results)
                self._ingest_flat(result, self.search_results,
                                  self.search_existing_ids)
                added = len(self.search_results) - before
                self.search_batch = batch_num
                self.search_batch_loading = False
                self.loading_spinner_triggered = False
                if batch_num == 1:
                    self.search_first_batch_count = len(self.search_results)
                    self.is_loading = False
                    self.is_searching = False
                if self.search_results:
                    if added:
                        # v3.6: page-aware status ("Página 2 - 32 vídeos")
                        self.set_status(self._page_label(
                            batch_num, self.search_results), "success")
                    else:
                        # page boundary reached with no new videos
                        self.set_status(self.t("msg_end_results"), "success")
                else:
                    self.set_status(self.t("msg_no_results"), "error")
                self.need_redraw = True
            except subprocess.TimeoutExpired as e:
                self.search_batch_loading = False
                if batch_num == 1:
                    self.is_loading = False
                    self.is_searching = False
                    if self._net_fail(e, lambda: self.search_youtube(
                            self.last_search_query)):
                        self.need_redraw = True
                        return
                    self.set_status(self.t("msg_timeout"), "error")
                self.need_redraw = True
            except Exception as e:
                self.search_batch_loading = False
                if batch_num == 1:
                    self.is_loading = False
                    self.is_searching = False
                    self.set_status("Error: %s" % str(e)[:24], "error")
                self.need_redraw = True

        run_logged_thread("search-batch", worker)

    def check_load_next_batch(self):
        if self.current_nav == NAV_HOME:
            if (self.home_batch >= 1 and not self.home_batch_loading
                    and len(self.home_videos) < self.max_feed()
                    and self.selected >= len(self.home_videos) - 4
                    and self.home_batch < len(self.TRENDING_SOURCES)):
                self._load_trending_batch(self.home_batch + 1)
        elif self.current_nav == NAV_SEARCH:
            if (self.search_batch >= 1 and not self.search_batch_loading
                    and len(self.search_results) < self.max_feed()
                    and self.selected >= len(self.search_results) - 3):
                self._load_search_batch(self.search_batch + 1)
        elif self.current_nav == NAV_CATEGORIES and self.category_open:
            # v3.4: search-based categories paginate like search results
            key, src = self.category_open
            if (src == "search" and self.category_batch >= 1
                    and not self.category_batch_loading
                    and len(self.category_videos) < self.max_feed()
                    and self.selected >= len(self.category_videos) - 3):
                self._load_category_batch(self.category_batch + 1)

    def max_feed(self):
        # v3.6: 200 = ~12 pages of 16 search results (was 60 = under 4)
        return 200

    # ---- Subscriptions ---------------------------------------------------
    def load_subs_feed(self, force=False):
        if self.subs_loading:
            return
        # v3.3: signed in -> the ACCOUNT's subscriptions feed first (the
        # exact feed the user sees on youtube.com, ordered by recency);
        # the local RSS machinery remains as automatic fallback
        if self._account_ready():
            self._load_account_subs(force)
            return
        self._load_rss_subs(force)

    def _load_rss_subs(self, force=False, render_first=True):
        if not self.subs.channels:
            self.sub_videos = []
            return
        # refresh at most every 15 minutes unless forced
        if not force and self.subs.feed and \
                (time.time() - self.subs.last_refresh) < 900:
            self.sub_videos = [VideoItem(v) for v in self.subs.feed]
            return
        self.subs_loading = True
        self.set_status(self.t("msg_loading_videos"), "loading")
        self.need_redraw = True
        if render_first:
            # (the account-feed fallback calls this from its worker thread;
            # only the main thread may touch the SDL renderer)
            self.render()

        def worker():
            try:
                feed = self.subs.refresh()
                self.sub_videos = [VideoItem(v) for v in feed]
                # optional DeArrow titles for the first entries
                if self.prefs.get("dearrow", "Off") == "On":
                    for item in self.sub_videos[:15]:
                        try:
                            self.dearrow.fetch_title(item.id)
                        except Exception:
                            pass
                self.subs_loading = False
                self.set_status("%d %s" % (len(self.sub_videos),
                                           self.t("msg_videos")))
                self.need_redraw = True
            except Exception as e:
                self.subs_loading = False
                self.set_status("Error: %s" % str(e)[:24], "error")
                self.need_redraw = True

        run_logged_thread("subs-refresh", worker)

    def mark_subs_seen(self):
        if self.sub_videos:
            self.subs.mark_seen([v.id for v in self.sub_videos])

    # ---- Channel view ----------------------------------------------------
    def open_channel(self, video):
        cid = getattr(video, "channel_id", "") or ""
        name = video.channel or ""
        if not cid:
            self.set_status(self.t("msg_no_channel"), "error")
            return
        self.channel_prev_nav = self.current_nav
        self.channel_view = {
            "title": name, "channel_id": cid,
            "videos": [], "selected": 0, "scroll": 0,
        }
        self.channel_loading = True
        self.current_nav = NAV_HOME  # render inside content area
        self.selected = 0
        self.scroll = 0
        self.ctx_close()
        self.set_status(self.t("msg_loading_videos"), "loading")
        self.need_redraw = True

        def worker():
            try:
                url = "https://www.youtube.com/channel/%s/videos" % cid
                args = self._ytdlp_args() + [
                    "--flat-playlist", "--dump-json",
                    "--playlist-items", "1:40", url]
                result = self._run_ytdlp(args, timeout=60)
                videos = []
                seen = set()
                self._ingest_flat(result, videos, seen)
                if self.channel_view:
                    self.channel_view["videos"] = videos
                self.channel_loading = False
                self.set_status("%d %s" % (len(videos), self.t("msg_videos")))
                self.need_redraw = True
            except Exception as e:
                self.channel_loading = False
                self.set_status("Error: %s" % str(e)[:24], "error")
                self.need_redraw = True

        run_logged_thread("channel-load", worker)

    def close_channel(self):
        if self.channel_prev_nav is not None:
            self.current_nav = self.channel_prev_nav
        self.channel_view = None
        self.channel_loading = False
        self.selected = 0
        self.scroll = 0
        self.need_redraw = True

    # ---- List access -----------------------------------------------------
    def _get_list(self):
        if self.channel_view:
            return self.channel_view.get("videos", [])
        if self.current_nav == NAV_HOME:
            return self.home_videos
        if self.current_nav == NAV_SUBS:
            return self.sub_videos
        if self.current_nav == NAV_SEARCH:
            return self.search_results
        if self.current_nav == NAV_CATEGORIES:
            # v3.4: a category's video list (the tile list itself renders
            # through render_category_list, not through the video cards)
            return self.category_videos
        if self.current_nav == NAV_HISTORY:
            # v3.3: signed in -> the account's YouTube watch history
            if self._account_ready() and \
                    (self.account_history or self.account_history_loading):
                return self.account_history
            return self.history
        return []

    def _get_filtered_list(self):
        items = [v for v in self._get_list() if not self.is_blocked(v)]
        hist = {}
        prefs = self.prefs
        # v3.4: inside the LIVE category the live videos ARE the content -
        # a global "hide live" filter must not empty the screen
        if self.current_nav == NAV_CATEGORIES and self.category_open \
                and self.category_open[0] == "live" \
                and prefs.get("hide_live", "Off") == "On":
            prefs = {"hide_shorts": self.prefs.get("hide_shorts", "Off"),
                     "hide_live": "Off",
                     "hide_watched": self.prefs.get("hide_watched", "Off")}
        return YX.apply_filters(items, prefs, self.positions, hist)

    def display_title(self, video):
        if self.prefs.get("dearrow", "Off") == "On":
            alt = self.dearrow.cache.get(video.id)
            if alt:
                return alt
        return video.title

    # =====================================================================
    # SETTINGS
    # =====================================================================
    def _update_settings_items(self):
        """v3.3 REFORMULATED settings: SmartTube-style two-pane layout.

        The old flat 34-row list with pixel scrolling was the single most
        problem-prone screen on the device (runaway scroll, stuck focus).
        Now: a LEFT pane with 8 sections and a RIGHT pane with that
        section's rows (max 7 each - everything fits on one screen with
        ZERO scrolling). Same options as before, regrouped; the new
        Account section holds the SmartTube-style YouTube sign-in."""
        tr = self.t
        # v3.4 BUG FIX ("two Desligados in the picker"): option lists must
        # carry RAW values ("On"/"Off"); the picker translates them ONLY at
        # render time. The old code stored the TRANSLATED strings here, and
        # the picker then translated them AGAIN - "Ligado" != "On" so BOTH
        # options rendered as "Desligado" in Portuguese.
        on_off = ["On", "Off"]
        auth = YX.get_auth()
        if auth.logged_in():
            name = auth.account_name() or "YouTube"
            account_rows = [
                ("info", "%s: %s" % (tr("settings_signed_in_as"),
                                     name[:22]), "account_name", None),
                ("action", tr("settings_logout"), "logout", None),
            ]
        else:
            account_rows = [
                ("info", tr("settings_not_signed_in"), "account_none", None),
                ("action", tr("settings_login"), "login", None),
            ]
        self.settings_sections = [
            ("account", tr("sec_account"), account_rows),
            ("general", tr("sec_general"), [
                ("choice", tr("settings_language"), "language", LANGUAGES),
                ("choice", tr("settings_theme"), "theme", ["Dark", "OLED"]),
                ("choice", tr("settings_search_count"), "search_count",
                 ["16", "24", "32", "48"]),
                ("choice", tr("settings_auto_load"), "auto_load", on_off),
            ]),
            ("playback", tr("sec_playback"), [
                ("choice", tr("settings_quality"), "quality",
                 QUALITY_OPTIONS),
                ("choice", tr("settings_codec"), "video_codec",
                 ["Auto", "H.264", "VP9", "AV1"]),
                ("choice", tr("settings_hwdec"), "hwdec", on_off),
                ("choice", tr("settings_seek_interval"), "seek_interval",
                 ["5", "10", "15", "30", "60"]),
                ("choice", tr("settings_playback_mode"), "playback_mode",
                 ["Normal", "Autoplay", "Repeat One", "Shuffle"]),
                ("choice", tr("settings_speed_memory"), "speed_memory",
                 on_off),
            ]),
            ("audio", tr("sec_audio"), [
                ("choice", tr("settings_subtitles"), "subtitles",
                 ["Auto", "Off", "English", "Portugues", "Espanol", "Turkce",
                  "Deutsch", "Francais"]),
                ("choice", tr("settings_audio_lang"), "audio_lang",
                 YX.AUDIO_LANG_OPTIONS),
                ("choice", tr("settings_sleep_timer"), "sleep_timer",
                 ["Off", "15", "30", "60"]),
                ("choice", tr("settings_volume_boost"), "volume_boost",
                 on_off),
            ]),
            ("sponsorblock", tr("sec_sponsorblock"), [
                ("choice", tr("settings_sponsorblock"), "sponsorblock",
                 ["Off", "Minimal", "Core", "All"]),
                ("choice", tr("settings_dearrow"), "dearrow", on_off),
                ("choice", tr("settings_ryd"), "ryd", on_off),
                ("choice", tr("settings_suggestions"), "suggestions",
                 on_off),
            ]),
            ("content", tr("sec_content"), [
                ("choice", tr("settings_hide_shorts"), "hide_shorts",
                 on_off),
                ("choice", tr("settings_hide_live"), "hide_live", on_off),
                ("choice", tr("settings_hide_watched"), "hide_watched",
                 on_off),
            ]),
            ("network", tr("sec_network"), [
                ("action", tr("settings_proxy"), "proxy", None),
                ("choice", tr("settings_route"), "route",
                 ["Default", "Cronet", "OkHttp"]),
                ("choice", tr("settings_prefer_ipv4"), "prefer_ipv4",
                 on_off),
                ("choice", tr("settings_player_client"), "player_client",
                 ["Default", "web", "tv", "android", "ios"]),
                ("choice", tr("settings_socket_timeout"), "socket_timeout",
                 ["10", "15", "30"]),
                ("info", tr("settings_ytdlp_ver"), "ytdlp_ver", None),
                ("action", tr("settings_ytdlp_update"), "ytdlp_update",
                 None),
            ]),
            ("data", tr("sec_data"), [
                ("action", tr("settings_clear_favorites"),
                 "clear_favorites", None),
                ("action", tr("settings_clear_history"), "clear_history",
                 None),
                ("action", tr("settings_clear_cache"), "clear_cache", None),
                ("action", tr("settings_clear_positions"),
                 "clear_positions", None),
                ("action", tr("settings_clear_searches"),
                 "clear_searches", None),
                ("action", tr("settings_clear_blocked"), "clear_blocked",
                 None),
                ("action", tr("settings_reset"), "reset_prefs", None),
            ]),
        ]
        # keep the indices inside their panes
        self.settings_section = max(0, min(self.settings_section,
                                           len(self.settings_sections) - 1))
        rows = self._settings_rows()
        self.settings_row = max(0, min(self.settings_row, len(rows) - 1))

    def _settings_rows(self):
        """Rows of the section that is selected in the left pane."""
        try:
            return self.settings_sections[self.settings_section][2] or []
        except (IndexError, TypeError):
            return []

    def _current_setting_row(self):
        rows = self._settings_rows()
        if 0 <= self.settings_row < len(rows):
            return rows[self.settings_row]
        return None

    def _setting_value_display(self, key, options):
        if key == "ytdlp_ver":
            return getattr(self, "ytdlp_ver", "?")
        current = self.prefs.get(key, options[0] if options else "")
        # repair values stored translated by older versions ("Ligado" etc.)
        if current == self.t("settings_on") and current not in ("On", "Off"):
            current = "On"
        elif current == self.t("settings_off") and current not in ("On", "Off"):
            current = "Off"
        if current in ("On", "Off"):
            # booleans and boolean-ish rows (subtitles Off, sleep Off) all
            # display through the same translation pair
            return self.t("settings_on") if current == "On" \
                else self.t("settings_off")
        if key == "sleep_timer" and current not in ("Off", ""):
            return "%s %s" % (current, self.t("settings_min"))
        if key == "seek_interval":
            return "%ss" % current
        return current

    # ------------------------------------------------------------------
    # v3.3 settings navigation (two-pane, no wrap-around, no auto-repeat)
    # ------------------------------------------------------------------
    ON_OFF_KEYS = ("hwdec", "auto_load", "speed_memory", "ryd", "dearrow",
                   "suggestions", "hide_shorts", "hide_live", "hide_watched",
                   "prefer_ipv4", "volume_boost")

    def settings_dir(self, d):
        """Direction dispatch for the settings screen.

        UP/DOWN move inside the focused pane; LEFT/RIGHT switch panes; the
        value picker (when open) takes precedence. Values only ever change
        through the picker - dpad can never flick a setting by accident."""
        if self.settings_picker is not None:
            if d == "up":
                self.settings_picker_move(-1)
            elif d == "down":
                self.settings_picker_move(1)
            return
        if self.settings_pane == "left":
            if d == "up":
                self.settings_section = max(0, self.settings_section - 1)
                self.settings_row = 0
            elif d == "down":
                n = len(self.settings_sections or [])
                self.settings_section = min(n - 1, self.settings_section + 1)
                self.settings_row = 0
            elif d == "right":
                if self._settings_rows():
                    self.settings_pane = "right"
                    self.settings_row = 0
        else:
            rows = self._settings_rows()
            if d == "up":
                self.settings_row = max(0, self.settings_row - 1)
            elif d == "down":
                self.settings_row = min(len(rows) - 1, self.settings_row + 1)
            elif d == "left":
                self.settings_pane = "left"
            elif d == "right":
                # stay: value changes only via the picker (A button)
                self.set_status(self.t("settings_pick_hint"))
        self.need_redraw = True
        self.last_repeat = SDL_GetTicks()

    def settings_select(self):
        """A button: pick a section (left pane) / open picker or run the
        action row (right pane)."""
        if self.settings_picker is not None:
            self.settings_picker_confirm()
            return
        if self.settings_pane == "left":
            if self._settings_rows():
                self.settings_pane = "right"
                self.settings_row = 0
            self.need_redraw = True
            return
        row = self._current_setting_row()
        if not row:
            return
        kind, label, key, options = row
        if kind == "choice" and options:
            current = self.prefs.get(key, options[0])
            if key in self.ON_OFF_KEYS and current not in ("On", "Off"):
                current = "On" if current == self.t("settings_on") else "Off"
            try:
                idx = options.index(current)
            except ValueError:
                idx = 0
            self.settings_picker = {"label": label, "key": key,
                                    "options": list(options),
                                    "selected": idx, "row": row}
        elif kind == "action":
            self.execute_setting_action(key)
        self.need_redraw = True

    def settings_back(self):
        """B button: close picker -> left pane -> exit settings."""
        if self.settings_picker is not None:
            self.settings_picker_cancel()
            return
        if self.settings_pane == "right":
            self.settings_pane = "left"
            self.need_redraw = True
            return
        self.action_back()

    def settings_picker_move(self, delta):
        p = self.settings_picker
        if not p:
            return
        options = p.get("options") or []
        if not options:
            return
        p["selected"] = max(0, min(len(options) - 1,
                                   p.get("selected", 0) + delta))
        self.need_redraw = True

    def settings_picker_confirm(self):
        p = self.settings_picker
        self.settings_picker = None
        if not p:
            return
        options = p.get("options") or []
        idx = p.get("selected", 0)
        if not (0 <= idx < len(options)):
            return
        row = p.get("row") or (None, p.get("label"), p.get("key"), options)
        kind, label, key, _opts = row
        new_val = options[idx]
        if kind == "choice":
            self.settings_apply_value(key, label, options, new_val)

    def settings_picker_cancel(self):
        self.settings_picker = None
        self.need_redraw = True

    def settings_apply_value(self, key, label, options, new_val):
        """Store one settings value + run its side effects (shared by the
        picker and any legacy callers)."""
        if key in self.ON_OFF_KEYS:
            if new_val not in ("On", "Off"):
                new_val = "On" if new_val == self.t("settings_on") else "Off"
        self.prefs.set(key, new_val, save=True)

        if key == "theme":
            self._apply_theme()
            self.text_cache.clear()
        elif key == "language":
            self._update_settings_items()
            self.text_cache.clear()
        elif key == "route":
            # v3.2: apply the network route immediately + drop pooled
            # keep-alive connections from the previous route
            try:
                YX.set_active_route(new_val)
                YX.close_connection_pool()
            except Exception:
                pass
        val = self._setting_value_display(key, options)
        self.set_status("%s: %s" % (label, val))
        self.need_redraw = True

    def change_setting(self, direction):
        """Legacy one-step value cycle (kept for compatibility)."""
        row = self._current_setting_row()
        if not row:
            return
        kind, label, key, options = row
        if kind != "choice" or not options:
            return
        current = self.prefs.get(key, options[0])
        # options hold RAW values; prefs always store RAW On/Off (v3.4)
        if current not in options and key in self.ON_OFF_KEYS:
            # repair legacy/translated values
            current = "On" if current == self.t("settings_on") else "Off"
        try:
            idx = options.index(current)
        except ValueError:
            idx = 0
        idx = (idx + direction) % len(options)
        self.settings_apply_value(key, label, options, options[idx])

    def execute_setting_action(self, key):
        if key == "login":
            # v3.3: SmartTube-style YouTube account sign-in (device code)
            self.start_login()
        elif key == "logout":
            self.sign_out_account()
        elif key == "clear_favorites":
            self.favorites = []
            self._save_json("yt_favorites.json", [])
            self.set_status(self.t("msg_fav_cleared"))
        elif key == "clear_history":
            self.history = []
            self._save_json("yt_history.json", [])
            self.set_status(self.t("msg_history_cleared"))
        elif key == "clear_cache":
            try:
                import shutil
                if os.path.exists(self.image_cache_dir):
                    shutil.rmtree(self.image_cache_dir)
                    os.makedirs(self.image_cache_dir, exist_ok=True)
                for tex, _, _ in self.image_cache.values():
                    if tex:
                        SDL_DestroyTexture(tex)
                self.image_cache.clear()
                self.failed_images.clear()
                self.set_status(self.t("msg_cache_cleared"))
            except Exception as e:
                self.set_status("Error: %s" % str(e)[:20], "error")
        elif key == "clear_positions":
            self.positions = {}
            self._save_positions()
            self.set_status(self.t("msg_positions_cleared"))
        elif key == "clear_searches":
            self.search_history = []
            YX.save_search_history([])
            self.set_status(self.t("msg_searches_cleared"))
        elif key == "clear_blocked":
            self.blocked = []
            self._save_blocked()
            self.set_status(self.t("msg_blocked_cleared"))
        elif key == "reset_prefs":
            keep_lang = self.prefs.get("language", "English")
            keep_device = self.prefs.get("device", "")
            for k in list(self.prefs.data.keys()):
                self.prefs.data[k] = YX.DEFAULT_PREFS.get(k, "")
            self.prefs.set("language", keep_lang, save=False)
            self.prefs.set("device", keep_device, save=False)
            self.prefs.set("first_boot_done", "1", save=False)
            self.prefs.save()
            self._apply_theme()
            self._update_settings_items()
            self.text_cache.clear()
            self.set_status(self.t("msg_prefs_reset"))
        elif key == "proxy":
            self.search_active = True
            self.keyboard_mode = "proxy"
            self.search_query = self.prefs.get("proxy", "")
            self.keyboard_row = self.keyboard_col = 0
            self.sugg_visible = False
        elif key == "ytdlp_update":
            self._run_ytdlp_update()
        self.need_redraw = True

    def _run_ytdlp_update(self):
        if not self.ytdlp_path:
            self.set_status(self.t("msg_no_ytdlp"), "error")
            return

        def worker():
            try:
                self.set_status(self.t("msg_updating"), "loading")
                self.need_redraw = True
                ok, msg = YX.ytdlp_self_update(
                    self.ytdlp_path,
                    proxy=self.prefs.get("proxy", ""))
                self.ytdlp_ver = YX.ytdlp_version(self.ytdlp_path)
                self.set_status(msg[:44], "ok" if ok else "error")
                self.need_redraw = True
            except Exception as e:
                self.set_status("Error: %s" % str(e)[:24], "error")
                self.need_redraw = True

        run_logged_thread("update-ytdlp", worker)

    # ------------------------------------------------------------------
    # v0.3.8: background yt-dlp update check (every app open)
    # ------------------------------------------------------------------
    def _ytdlp_update_check(self):
        """Compare the bundled yt-dlp with the latest GitHub release.

        Runs in a daemon thread so startup is NEVER blocked (offline =
        the check silently skips). When a newer version exists the main
        loop shows a gamepad Yes/No popup; answering Yes reuses the exact
        settings updater (download -> replace -> refresh version).
        """
        try:
            if not self.ytdlp_path or not os.path.exists(self.ytdlp_path):
                return
            if self.net_offline:
                LOG("yt-dlp update check skipped (offline)", "YTDLP")
                return
            current = YX.ytdlp_version(self.ytdlp_path)
            latest = YX.ytdlp_latest_version(self.prefs.get("proxy", ""))
            if not latest:
                LOG("yt-dlp update check: latest version unreachable",
                    "YTDLP")
                return
            if current and current not in ("unknown", "not found") and \
                    str(latest) <= str(current):
                LOG("yt-dlp up to date (%s)" % current, "YTDLP")
                return
            LOG("yt-dlp update available: %s -> %s" % (current, latest),
                "YTDLP")
            # hand over to the main thread - workers never touch the UI
            self._ytdlp_update_offer = (current, latest)
        except Exception:
            pass

    def _ytdlp_maybe_show_popup(self):
        """Main-loop side: turn a finished check into the popup (idle UI
        only - never over the player, wizard, keyboard, sign-in or any
        other modal)."""
        offer = self._ytdlp_update_offer
        if offer is None or self.update_popup is not None:
            return
        if self.wizard_active or self.search_active or self.login_active or \
                self.is_loading_video or self.ctx_open or self.info_open or \
                self.queue_open or self.is_playing or self.player is not \
                None or self.autoplay_countdown is not None or \
                self.channel_view is not None:
            return
        self._ytdlp_update_offer = None
        self.update_popup = {
            "current": offer[0], "latest": offer[1], "choice": 0}
        self.need_redraw = True
        LOG("showing yt-dlp update popup (%s -> %s)" % offer, "YTDLP")

    def _ytdlp_popup_answer(self, yes):
        """Close the popup; Yes runs the real updater, No just dismisses."""
        p = self.update_popup
        self.update_popup = None
        self.need_redraw = True
        if p is None:
            return
        if yes:
            LOG("user accepted yt-dlp update", "YTDLP")
            self._run_ytdlp_update()
        else:
            LOG("user skipped yt-dlp update (%s available)" %
                p.get("latest"), "YTDLP")
            self.set_status(self.t("update_skipped"), "ok")

    def _suggest_async(self):
        """Fetch suggestions for the current query (v3.6: on demand ONLY).

        Called from sugg_show (the SUG keyboard key / X button). The old
        while-typing auto-fetch is gone - it popped the suggestion panel
        over the keyboard mid-word and hijacked the dpad, making it
        impossible to keep typing."""
        if self.keyboard_mode != "search":
            return
        if self.prefs.get("suggestions", "On") != "On":
            self.sugg_visible = False
            return
        query = self.search_query.strip()
        if len(query) < 2 or query == self.sugg_fetched_for:
            if query == self.sugg_fetched_for and self.sugg_items:
                # re-show the cached results for this query
                self.sugg_selected = 0
                self.sugg_visible = True
                self.sugg_loading = False
                self.need_redraw = True
            elif not self.sugg_items:
                self.sugg_items = list(self.search_history)
                self.sugg_selected = 0
                self.sugg_visible = bool(self.sugg_items)
                self.sugg_loading = False
                self.need_redraw = True
            return
        self.sugg_fetched_for = query
        self.sugg_loading = True
        self.need_redraw = True

        def worker():
            try:
                items = YX.fetch_suggestions(self.search_query.strip(), self.prefs)
                if self.search_active and self.sugg_fetched_for == query:
                    self.sugg_items = items or list(self.search_history)
                    self.sugg_selected = 0
                    self.sugg_loading = False
                    self.sugg_visible = bool(self.sugg_items)
                    self.need_redraw = True
            except Exception:
                self.sugg_loading = False
                self.need_redraw = True

        if self._suggest_thread and self._suggest_thread.is_alive():
            return
        self._suggest_thread = run_logged_thread("suggestions", worker)

    def sugg_move(self, delta):
        if not self.sugg_items:
            return
        self.sugg_selected = (self.sugg_selected + delta) % len(self.sugg_items)
        self.need_redraw = True

    def sugg_select(self):
        if not self.sugg_items:
            return
        chosen = self.sugg_items[self.sugg_selected]
        self.search_query = chosen
        self.sugg_visible = False
        self.search_youtube(chosen)

    # =====================================================================
    # CONTEXT MENU / QUEUE / INFO / WIZARD RENDERERS
    # =====================================================================
    def build_ctx_menu(self, video):
        items = []
        pos = self.get_position(video.id)
        if pos and pos[0] > 30:
            items.append(("%s %s" % (self.t("ctx_resume"), fmt_clock(pos[0])), "resume"))
        else:
            items.append((self.t("ctx_play"), "play"))
        items.append((self.t("ctx_beginning"), "beginning"))
        if any(q.id == video.id for q in self.queue):
            items.append((self.t("queue_title"), "queue_view"))
        else:
            items.append((self.t("ctx_queue_add"), "queue_add"))
        items.append((self.t("ctx_queue_next"), "queue_next"))
        items.append((self.t("ctx_play_all"), "play_all"))
        if any(f.id == video.id for f in self.favorites):
            items.append((self.t("msg_removed_fav"), "fav_remove"))
        else:
            items.append((self.t("msg_added_fav"), "fav_add"))
        if video.channel_id or video.channel:
            items.append((self.t("ctx_channel"), "channel"))
            if self.subs.is_subscribed(video.channel_id):
                items.append((self.t("ctx_unsubscribe"), "unsub"))
            else:
                items.append((self.t("ctx_subscribe"), "sub"))
        if self.is_blocked(video):
            items.append((self.t("ctx_unblock"), "unblock"))
        else:
            items.append((self.t("ctx_block"), "block"))
        items.append((self.t("ctx_info"), "info"))
        if self.current_nav == NAV_HISTORY and not self.channel_view:
            items.append((self.t("ctx_remove_history"), "remove_history"))
        self.ctx_items = items
        self.ctx_video = video
        self.ctx_selected = 0
        self.ctx_open = True
        self.need_redraw = True

    def ctx_close(self):
        self.ctx_open = False
        self.ctx_items = []
        self.ctx_video = None
        self.need_redraw = True

    def ctx_execute(self, action):
        video = self.ctx_video
        if not video:
            self.ctx_close()
            return
        videos = self._get_filtered_list()
        idx = -1
        for i, v in enumerate(videos):
            if v.id == video.id:
                idx = i
                break

        if action in ("play", "resume"):
            self.ctx_close()
            self.play_video(video)
        elif action == "beginning":
            self.ctx_close()
            self.positions.pop(video.id, None)
            self.play_video(video)
        elif action == "queue_add":
            self.queue_add(video)
        elif action == "queue_next":
            self.queue_add(video, front=True)
        elif action == "queue_view":
            self.ctx_close()
            self.queue_open = True
            self.queue_selected = 0
        elif action == "play_all":
            if idx >= 0:
                self.queue_play_all(videos, idx)
        elif action == "fav_add":
            if not any(f.id == video.id for f in self.favorites):
                self.favorites.insert(0, video)
                self._save_json("yt_favorites.json", self.favorites)
            self.set_status(self.t("msg_added_fav"))
        elif action == "fav_remove":
            self.favorites = [f for f in self.favorites if f.id != video.id]
            self._save_json("yt_favorites.json", self.favorites)
            self.set_status(self.t("msg_removed_fav"))
        elif action == "channel":
            self.open_channel(video)
        elif action == "sub":
            if self.subs.subscribe(video.channel_id, video.channel):
                self.set_status(self.t("msg_subscribed"))
                self.last_subs_refresh_forced = True
        elif action == "unsub":
            if self.subs.unsubscribe(video.channel_id):
                self.set_status(self.t("msg_unsubscribed"))
        elif action == "block":
            self.blocked.append({"id": video.channel_id, "name": video.channel})
            self._save_blocked()
            self.set_status(self.t("msg_blocked"))
        elif action == "unblock":
            self.blocked = [b for b in self.blocked
                            if b.get("id") != video.channel_id]
            self._save_blocked()
            self.set_status(self.t("msg_unblocked"))
        elif action == "info":
            self.info_video = video
            self.info_ryd = None
            self.info_open = True
            if self.prefs.get("ryd", "On") == "On":
                def worker():
                    votes = self.ryd.fetch_votes(video.id)
                    if votes:
                        self.info_ryd = "+%s / -%s" % (
                            self._short_num(votes.get("likes", 0)),
                            self._short_num(votes.get("dislikes", 0)))
                        self.need_redraw = True
                run_logged_thread("info-ryd", worker)
        elif action == "remove_history":
            self.history = [h for h in self.history if h.id != video.id]
            self._save_json("yt_history.json", self.history)
            self.set_status(self.t("msg_history_cleared"))
        if action not in ("play", "resume", "beginning", "queue_view", "channel"):
            self.ctx_close()

    # =====================================================================
    # INPUT HANDLING
    # =====================================================================
    def _keyboard_layout_lens(self):
        if self.sym_page:
            return [len(r) for r in self.symbol_layout] + [5]
        return [10, 10, 9, 7, 5]

    def handle_keyboard_nav(self, d):
        lens = self._keyboard_layout_lens()
        if d == "up" and self.keyboard_row > 0:
            self.keyboard_row -= 1
            self.keyboard_col = min(self.keyboard_col, lens[self.keyboard_row] - 1)
        elif d == "down" and self.keyboard_row < 4:
            self.keyboard_row += 1
            self.keyboard_col = min(self.keyboard_col, lens[self.keyboard_row] - 1)
        elif d == "left" and self.keyboard_col > 0:
            self.keyboard_col -= 1
        elif d == "right" and self.keyboard_col < lens[self.keyboard_row] - 1:
            self.keyboard_col += 1
        self.need_redraw = True

    def handle_keyboard_select(self):
        if self.keyboard_row < 4:
            layout = self.symbol_layout if self.sym_page else self.keyboard_layout.copy()
            if self.caps_lock and not self.sym_page:
                layout = [layout[0]] + [[c.upper() for c in row] for row in layout[1:4]]
            row = layout[self.keyboard_row]
            if self.keyboard_col < len(row) and len(self.search_query) < 60:
                self.search_query += row[self.keyboard_col]
        else:
            # v3.6: control row is [SYM/ABC, SPACE, backspace, SUG, GO]
            if self.keyboard_col == 0:
                self.sym_page = not self.sym_page
                self.keyboard_col = 0
            elif self.keyboard_col == 1 and len(self.search_query) < 60:
                self.search_query += " "
            elif self.keyboard_col == 2 and self.search_query:
                self.search_query = self.search_query[:-1]
            elif self.keyboard_col == 3:
                # SUG: suggestions ONLY on explicit request - they never
                # pop up while typing (v3.6: the old auto-fetch replaced
                # the keyboard mid-typing and swallowed the input).
                self.sugg_show()
            elif self.keyboard_col == 4:
                self._keyboard_go()
        self.need_redraw = True

    def sugg_show(self):
        """v3.6: open the suggestion panel ON DEMAND (SUG key / X button).

        Empty query -> recent searches. Otherwise fresh suggestions are
        fetched for the current query; typing is never interrupted."""
        if self.keyboard_mode != "search":
            return
        if self.prefs.get("suggestions", "On") != "On":
            return
        if not self.search_query.strip():
            self.sugg_items = list(self.search_history)
            self.sugg_selected = 0
            self.sugg_visible = bool(self.sugg_items)
            self.need_redraw = True
            return
        self.sugg_items = []
        self.sugg_selected = 0
        self.sugg_visible = True
        self.sugg_loading = True
        self.need_redraw = True
        self._suggest_async()

    def _keyboard_go(self):
        query = self.search_query.strip()
        if self.keyboard_mode == "proxy":
            self.prefs.set("proxy", query, save=True)
            self.search_active = False
            self.keyboard_mode = "search"
            self.search_query = ""
            self.sugg_visible = False
            self.set_status("Proxy: %s" % (query if query else "direct"))
        elif query:
            self.sugg_visible = False
            self.search_youtube(query)

    # ------------------------------------------------------------ actions
    def action_up(self):
        if self.selected > 0:
            self.selected -= 1
            self.need_redraw = True

    def action_down(self):
        videos = self._get_filtered_list()
        if self.selected < len(videos) - 1:
            self.selected += 1
            self.need_redraw = True
            self.check_load_next_batch()

    def action_left(self):
        if self.channel_view:
            self.close_channel()
            return
        if self.current_nav == NAV_SUBS:
            self.mark_subs_seen()
        self._leave_category()
        self.current_nav = (self.current_nav - 1) % NAV_COUNT
        self.selected = self.scroll = 0
        self.loading_spinner_triggered = False
        if self.current_nav == NAV_SUBS:
            self.load_subs_feed()
        elif self.current_nav == NAV_HISTORY:
            self._maybe_load_account_history()
        elif self.current_nav == NAV_HOME and not self.home_videos:
            self.load_trending()
        self.need_redraw = True

    def action_right(self):
        if self.channel_view:
            return
        if self.current_nav == NAV_SUBS:
            self.mark_subs_seen()
        self._leave_category()
        self.current_nav = (self.current_nav + 1) % NAV_COUNT
        self.selected = self.scroll = 0
        self.loading_spinner_triggered = False
        if self.current_nav == NAV_SUBS:
            self.load_subs_feed()
        elif self.current_nav == NAV_HISTORY:
            self._maybe_load_account_history()
        elif self.current_nav == NAV_HOME and not self.home_videos:
            self.load_trending()
        self.need_redraw = True

    def _leave_category(self):
        """v3.4: switching tabs always drops the open category view."""
        if self.category_open is not None:
            self.category_open = None
            self.category_videos = []
            self.category_failed = False

    def action_select(self):
        if self.channel_view:
            videos = self._get_filtered_list()
            if videos and self.selected < len(videos):
                self.play_video(videos[self.selected])
            return
        # v3.4: A on a category tile opens that category's videos
        if self.current_nav == NAV_CATEGORIES and not self.category_open:
            if 0 <= self.selected < len(CATEGORY_DEFS):
                self.open_category(CATEGORY_DEFS[self.selected][0])
            return
        if self.current_nav == NAV_SEARCH and not self.search_results \
                and not self.search_active:
            self.action_search()
            return
        # v2.2: [A] on a failed Trending feed retries the whole chain
        if self.current_nav == NAV_HOME and self.home_feed_failed \
                and not self.home_batch_loading \
                and not self._get_filtered_list():
            self.load_trending()
            return
        videos = self._get_filtered_list()
        if videos and self.selected < len(videos):
            self.play_video(videos[self.selected])
        self.need_redraw = True

    def action_back(self):
        if self.wizard_active:
            self.wizard_back()
            return
        if self.search_active:
            if self.sugg_visible:
                self.sugg_visible = False
                self.need_redraw = True
                return
            self.search_active = False
            self.keyboard_mode = "search"
            self.sugg_visible = False
        elif self.info_open:
            self.info_open = False
            self.info_video = None
        elif self.ctx_open:
            self.ctx_close()
        elif self.queue_open:
            self.queue_open = False
        elif self.channel_view:
            self.close_channel()
        elif self.is_playing:
            self.stop_playback(user=True)
        elif self.current_nav == NAV_CATEGORIES and self.category_open:
            # v3.4: B inside a category goes back to the category tiles
            self.close_category()
        else:
            # v2.2: B NEVER closes the app - START+SELECT is the only exit.
            # Tell the user how to leave instead of quitting silently.
            self.set_status(self.t("msg_exit_hint"))
        self.need_redraw = True

    def action_search(self):
        self.search_active = True
        self.keyboard_mode = "search"
        self.search_query = ""
        self.keyboard_row = self.keyboard_col = 0
        self.sym_page = False
        self.current_nav = NAV_SEARCH
        self.sugg_visible = False
        self.sugg_items = list(self.search_history)
        self.need_redraw = True

    def toggle_favorite(self):
        videos = self._get_filtered_list()
        if not videos or self.selected >= len(videos):
            return
        video = videos[self.selected]
        if any(v.id == video.id for v in self.favorites):
            self.favorites = [v for v in self.favorites if v.id != video.id]
            self.set_status(self.t("msg_removed_fav"))
        else:
            self.favorites.insert(0, video)
            self._save_json("yt_favorites.json", self.favorites)
            self.set_status(self.t("msg_added_fav"))
        self.need_redraw = True

    # ---------------------------------------------------- direction gate
    # v3.1: every dpad/stick/hat/key direction funnels through these two
    # methods. _dir_press() accepts only the press TRANSITION of a
    # direction that is not currently considered held (and not inside the
    # cooldown). Cheap handheld controllers re-fire button/hat events
    # while a direction is down (axis jitter, hat+button duplicates);
    # those are all swallowed here.
    DIR_COOLDOWN_MS = 230         # min spacing between accepted actions

    DIR_STALE_MS = 900            # held flag auto-expires after this

    def _dir_press(self, direction, now=None):
        """Accept a raw direction press; True only on a real transition."""
        now = SDL_GetTicks() if now is None else now
        held_since = self._dir_held.get(direction)
        if held_since is not None:
            if now - held_since < self.DIR_STALE_MS:
                return False          # still held: duplicate event, skip
            # stale hold (release event was lost) - fall through and
            # treat this press as a fresh one
        if now - self._dir_last.get(direction, -1 << 30) < self.DIR_COOLDOWN_MS:
            # inside the cooldown: refresh the held marker so a jittering
            # source keeps getting swallowed, but do not act
            self._dir_held[direction] = now
            return False
        self._dir_held[direction] = now
        self._dir_last[direction] = now
        return True

    def _dir_release(self, direction):
        """A direction source reports the direction is no longer active."""
        self._dir_held.pop(direction, None)

    def _gate_directions(self, now=None):
        """Periodic truth check: drop held flags the hardware no longer
        reports. Missed release events (hat spam, axis jitter, focus
        switches) otherwise freeze a direction gate shut forever."""
        now = SDL_GetTicks() if now is None else now
        if now < self._truth_next_ms:
            return
        self._truth_next_ms = now + 300
        if not self._dir_held:
            return
        live = {}
        if self.controller:
            pairs = (
                ("up", SDL_CONTROLLER_BUTTON_DPAD_UP),
                ("down", SDL_CONTROLLER_BUTTON_DPAD_DOWN),
                ("left", SDL_CONTROLLER_BUTTON_DPAD_LEFT),
                ("right", SDL_CONTROLLER_BUTTON_DPAD_RIGHT),
            )
            for direction, gc_btn in pairs:
                try:
                    if SDL_GameControllerGetButton(self.controller, gc_btn):
                        live[direction] = True
                except Exception:
                    pass
            # the analog stick counts as hardware truth too
            try:
                ax = SDL_GameControllerGetAxis(
                    self.controller, SDL_CONTROLLER_AXIS_LEFTX) or 0
                ay = SDL_GameControllerGetAxis(
                    self.controller, SDL_CONTROLLER_AXIS_LEFTY) or 0
                if abs(ax) > 12000:
                    live["right" if ax > 0 else "left"] = True
                if abs(ay) > 12000:
                    live["down" if ay > 0 else "up"] = True
            except Exception:
                pass
        elif self.joystick:
            try:
                hat = SDL_JoystickGetHat(self.joystick, 0)
                if hat & SDL_HAT_UP:
                    live["up"] = True
                if hat & SDL_HAT_DOWN:
                    live["down"] = True
                if hat & SDL_HAT_LEFT:
                    live["left"] = True
                if hat & SDL_HAT_RIGHT:
                    live["right"] = True
            except Exception:
                pass
        # keyboard-held directions (dev/test path)
        for direction, on in self._kb_dir.items():
            if on:
                live[direction] = True
        for direction in list(self._dir_held.keys()):
            if direction in live:
                # genuinely held: keep the timestamp fresh so auto-repeat
                # (process_repeat) keeps running while the user holds
                self._dir_held[direction] = now
            elif now - self._dir_held[direction] > 500:
                # nothing holds it down any more - free the gate
                self._dir_held.pop(direction, None)

    def _act_ok(self, name, cooldown=160):
        """Debounce for non-direction buttons (A double-fires etc.)."""
        now = SDL_GetTicks()
        if now - self._act_last.get(name, -1 << 30) < cooldown:
            return False
        self._act_last[name] = now
        return True

    def _hat_transitions(self, event):
        """Newly-pressed directions of a joystick hat event (edge view)."""
        which = 0
        try:
            which = event.jhat.which
        except Exception:
            pass
        value = event.jhat.value
        old = self._hat_prev.get(which, 0)
        self._hat_prev[which] = value
        new_dirs = []
        for mask, name in ((SDL_HAT_UP, "up"), (SDL_HAT_DOWN, "down"),
                           (SDL_HAT_LEFT, "left"), (SDL_HAT_RIGHT, "right")):
            if (value & mask) and not (old & mask):
                new_dirs.append(name)
            elif not (value & mask) and (old & mask):
                self._dir_release(name)
        return new_dirs

    def _axis_transitions(self, event):
        """Analog-stick direction edges with hysteresis (flick = press)."""
        try:
            axis = event.caxis.axis
            value = event.caxis.value
        except AttributeError:
            return []
        axis_lx = getattr(sdl2, "SDL_CONTROLLER_AXIS_LEFTX", 0)
        axis_ly = getattr(sdl2, "SDL_CONTROLLER_AXIS_LEFTY", 1)
        if axis not in (axis_lx, axis_ly):
            return []
        horizontal = axis == axis_lx
        # engage at ~50% deflection, release at ~30%; between those two
        # thresholds the PREVIOUS state is kept (hysteresis - jitter in
        # the band must not re-fire or release anything)
        pressed = self._axis_dir.get(axis)
        if horizontal:
            if value > 16000:
                pressed = "right"
            elif value < -16000:
                pressed = "left"
            elif abs(value) < 9000:
                pressed = None
        else:
            if value > 16000:
                pressed = "down"
            elif value < -16000:
                pressed = "up"
            elif abs(value) < 9000:
                pressed = None
        prev = self._axis_dir.get(axis)
        self._axis_dir[axis] = pressed
        out = []
        if pressed and pressed != prev:
            out.append(pressed)
        elif prev and prev != pressed:
            self._dir_release(prev)
        return out

    def process_repeat(self):
        if not self.key_held:
            return
        now = SDL_GetTicks()
        # v3.1: auto-repeat only while the direction gate still sees the
        # direction genuinely held (truth-checked against the hardware).
        held_since = self._dir_held.get(self.key_held)
        if held_since is None or now - held_since > self.DIR_STALE_MS:
            self.key_held = None
            return
        if now - self.key_hold_start < 400:
            return
        if now - self.last_repeat >= 100:
            self.last_repeat = now
            if self.search_active:
                self.handle_keyboard_nav(self.key_held)
            elif self.is_playing:
                # v3.1: repeat drives the HUD options row (smooth focus
                # movement while holding) - seeks stay edge-triggered
                if self.player is not None and self.hud_visible and \
                        not self.player_menu and \
                        self.key_held in ("left", "right"):
                    self._hud_focus_move(
                        -1 if self.key_held == "left" else 1)
            elif self.key_held == "up":
                # v3.2: NO auto-repeat in the settings menu - one press = one
                # row ("take off auto-scroll from the configs menu"). Lists
                # keep their smooth hold-scroll.
                if self.current_nav != NAV_SETTINGS or self.channel_view:
                    self.action_up()
            elif self.key_held == "down":
                if self.current_nav != NAV_SETTINGS or self.channel_view:
                    self.action_down()

    # ------------------------------------------------------------ events
    def handle_event(self, event):
        """v2.2 iron rule: INPUT CAN NEVER CRASH OR CLOSE THE APP.

        Any exception raised while handling a button press is logged to
        detailed.txt and swallowed - the app stays open. (v2.1 shipped a
        NameError on an SDL constant that made "any button" quit the app.)
        The ONLY exits are the START+SELECT combo and window close.
        """
        try:
            self._handle_event_impl(event)
        except Exception:
            _PLOG.crash("input event (ignored - app stays open)",
                        sys.exc_info())
            try:
                self.set_status(self.t("msg_err_ignored"), "error")
            except Exception:
                pass

    def _is_exit_combo(self, btn):
        """True when this just-pressed button completes START+SELECT."""
        if not self.controller:
            return False
        try:
            start_held = SDL_GameControllerGetButton(
                self.controller, SDL_CONTROLLER_BUTTON_START)
            select_held = SDL_GameControllerGetButton(
                self.controller, SDL_CONTROLLER_BUTTON_SELECT)
        except Exception:
            return False
        if btn == SDL_CONTROLLER_BUTTON_START and select_held:
            return True
        if btn == SDL_CONTROLLER_BUTTON_SELECT and start_held:
            return True
        return False

    def _hat_dup_of_button(self, hat):
        """v3.0: SDL2 delivers the SAME physical d-pad press as BOTH a
        controller button event and a joystick hat event. Acting on both
        made every menu scroll two rows per press ("the config menu runs
        away"). When the game controller reports the corresponding d-pad
        button as held right now, the hat event is a duplicate - skip it."""
        if not self.controller:
            return False
        try:
            pairs = (
                (SDL_HAT_UP, SDL_CONTROLLER_BUTTON_DPAD_UP),
                (SDL_HAT_DOWN, SDL_CONTROLLER_BUTTON_DPAD_DOWN),
                (SDL_HAT_LEFT, SDL_CONTROLLER_BUTTON_DPAD_LEFT),
                (SDL_HAT_RIGHT, SDL_CONTROLLER_BUTTON_DPAD_RIGHT),
            )
            for hat_mask, gc_btn in pairs:
                if hat & hat_mask and \
                        SDL_GameControllerGetButton(self.controller, gc_btn):
                    return True
        except Exception:
            return False
        return False

    def _trigger_section_event(self, event):
        """v3.4: L2/R2 (analog trigger axes) switch the MAIN section when
        no video is playing. Returns True when the event was consumed.

        Works everywhere outside the player - lists AND inside the settings
        screen (pressing a trigger leaves settings and lands on the next
        section, which is exactly how the user asked to escape the menu).
        Overlays that own the input (keyboard, context menu, queue, info,
        login, loading) simply consume nothing here - the triggers stay
        inert until the overlay closes."""
        try:
            axis = event.caxis.axis
            value = event.caxis.value
        except AttributeError:
            return False
        if self.wizard_active or self.search_active or self.ctx_open or \
                self.info_open or self.queue_open or self.login_active or \
                self.is_loading_video:
            return False
        try:
            axis_lt = getattr(sdl2, "SDL_CONTROLLER_AXIS_TRIGGERLEFT",
                              getattr(sdl2, "SDL_CONTROLLER_AXIS_LEFTTRIGGER", 4))
            axis_rt = getattr(sdl2, "SDL_CONTROLLER_AXIS_TRIGGERRIGHT",
                              getattr(sdl2, "SDL_CONTROLLER_AXIS_RIGHTTRIGGER", 5))
        except AttributeError:
            axis_lt, axis_rt = 4, 5
        if axis not in (axis_lt, axis_rt):
            return False
        armed = self._trig_armed.get(axis, True)
        if value > 16000 and armed:
            self._trig_armed[axis] = False
            # leaving settings: drop its modal state so no picker overlay
            # survives the screen change
            if self.current_nav == NAV_SETTINGS and not self.channel_view:
                self.settings_picker = None
                self.settings_pane = "left"
            if axis == axis_rt:
                self.action_right()      # R2 -> next section
            else:
                self.action_left()       # L2 -> previous section
            return True
        if value < 8000:
            self._trig_armed[axis] = True
        return True      # trigger axes are always consumed outside playback

    def _gate_input(self, event):
        """v3.1 input normaliser: turns any direction event (controller
        button, joystick hat, analog stick axis, keyboard key) into a
        short list of ACCEPTED direction edges. Everything else returns
        [] and the event keeps flowing through the normal handlers.

        The direction gate makes every navigation action edge-triggered
        and debounced, no matter how many times SDL re-reports the same
        physical press or how much the stick jitters."""
        accepted = []
        etype = event.type
        if etype == SDL_CONTROLLERBUTTONDOWN:
            btn = event.cbutton.button
            for b, d in ((SDL_CONTROLLER_BUTTON_DPAD_UP, "up"),
                         (SDL_CONTROLLER_BUTTON_DPAD_DOWN, "down"),
                         (SDL_CONTROLLER_BUTTON_DPAD_LEFT, "left"),
                         (SDL_CONTROLLER_BUTTON_DPAD_RIGHT, "right")):
                if btn == b:
                    if self._dir_press(d):
                        accepted.append(d)
                    break
        elif etype == SDL_CONTROLLERBUTTONUP:
            btn = event.cbutton.button
            for b, d in ((SDL_CONTROLLER_BUTTON_DPAD_UP, "up"),
                         (SDL_CONTROLLER_BUTTON_DPAD_DOWN, "down"),
                         (SDL_CONTROLLER_BUTTON_DPAD_LEFT, "left"),
                         (SDL_CONTROLLER_BUTTON_DPAD_RIGHT, "right")):
                if btn == b:
                    self._dir_release(d)
                    if self.key_held == d:
                        self.key_held = None
                    break
        elif etype == SDL_JOYHATMOTION:
            for d in self._hat_transitions(event):
                if self._dir_press(d):
                    accepted.append(d)
        elif etype == SDL_CONTROLLERAXISMOTION:
            for d in self._axis_transitions(event):
                if self._dir_press(d):
                    accepted.append(d)
        elif etype == SDL_KEYDOWN:
            try:
                if event.key.repeat:
                    return []
            except AttributeError:
                pass
            key = event.key.keysym.sym
            for k, d in ((SDLK_UP, "up"), (SDLK_DOWN, "down"),
                         (SDLK_LEFT, "left"), (SDLK_RIGHT, "right"),
                         (ord("w"), "up"), (ord("s"), "down"),
                         (ord("a"), "left"), (ord("d"), "right")):
                if key == k:
                    if self._dir_press(d):
                        self._kb_dir[d] = True
                        accepted.append(d)
                    break
        elif etype == SDL_KEYUP:
            key = event.key.keysym.sym
            for k, d in ((SDLK_UP, "up"), (SDLK_DOWN, "down"),
                         (SDLK_LEFT, "left"), (SDLK_RIGHT, "right"),
                         (ord("w"), "up"), (ord("s"), "down"),
                         (ord("a"), "left"), (ord("d"), "right")):
                if key == k:
                    self._dir_release(d)
                    self._kb_dir[d] = False
                    if self.key_held == d:
                        self.key_held = None
                    break
        return accepted

    def _dispatch_directions(self, dirs, now=None):
        """Route gated direction presses to the active screen."""
        for d in dirs:
            self._dispatch_one_direction(d, now)

    def _dispatch_one_direction(self, d, now=None):
        now = SDL_GetTicks() if now is None else now
        # --- v0.3.8 yt-dlp update popup: LEFT/RIGHT toggle Yes/No ---
        # (modal - it consumes every direction while open)
        if self.update_popup is not None:
            if d in ("left", "right"):
                self.update_popup["choice"] ^= 1
                self.need_redraw = True
            return
        # --- first-boot wizard ---
        if self.wizard_active:
            if d == "up":
                self.wizard_move(-1)
            elif d == "down":
                self.wizard_move(1)
            return
        # --- search keyboard / suggestion list ---
        if self.search_active:
            if self.sugg_visible and self.sugg_items:
                if d == "up":
                    self.sugg_move(-1)
                elif d == "down":
                    self.sugg_move(1)
            elif d in ("up", "down", "left", "right"):
                self.handle_keyboard_nav(d)
                if d in ("up", "down"):
                    self.key_held, self.key_hold_start = d, now
            return
        # --- context menu ---
        if self.ctx_open:
            if d == "up" and self.ctx_selected > 0:
                self.ctx_selected -= 1
                self.need_redraw = True
            elif d == "down" and self.ctx_selected < len(self.ctx_items) - 1:
                self.ctx_selected += 1
                self.need_redraw = True
            return
        # --- video info panel: directions are consumed, buttons close ---
        if self.info_open:
            return
        # --- queue screen ---
        if self.queue_open:
            if d == "up" and self.queue_selected > 0:
                self.queue_selected -= 1
                self.need_redraw = True
            elif d == "down" and self.queue_selected < len(self.queue) - 1:
                self.queue_selected += 1
                self.need_redraw = True
            return
        # --- player (autoplay countdown swallows directions: A/B buttons
        #     handle it in the event section above) ---
        if self.autoplay_countdown is not None:
            return
        if self.is_playing or self.player is not None:
            self._player_direction(d, now)
            return
        # --- settings screen ---
        if self.current_nav == NAV_SETTINGS and not self.channel_view:
            if not self.login_active:      # sign-in screen: no navigation
                self.settings_dir(d)
            return
        # --- category tile grid (v3.4 + v3.6): 2-column grid navigation.
        #     UP/DOWN walk ROWS (+/- 2 tiles - v3.6 FIX: the old branch
        #     swallowed UP/DOWN without acting, so only the first row was
        #     reachable and every tile below it was dead), LEFT/RIGHT walk
        #     columns. L2/R2 keep switching main sections. ---
        if self.current_nav == NAV_CATEGORIES and not self.channel_view \
                and not self.category_open:
            n = len(CATEGORY_DEFS)
            if d == "up" and self.selected >= 2:
                self.selected -= 2
                self.need_redraw = True
            elif d == "down" and self.selected + 2 < n:
                self.selected += 2
                self.need_redraw = True
            elif d == "left" and self.selected % 2 == 1:
                self.selected -= 1
                self.need_redraw = True
            elif d == "right" and self.selected % 2 == 0 \
                    and self.selected + 1 < n:
                self.selected += 1
                self.need_redraw = True
            return
        # --- video lists ---
        if d == "up":
            self.action_up()
            self.key_held, self.key_hold_start = "up", now
        elif d == "down":
            self.action_down()
            self.key_held, self.key_hold_start = "down", now
        elif d == "left":
            self.action_left()
        elif d == "right":
            self.action_right()

    def _handle_event_impl(self, event):
        now = SDL_GetTicks()

        # ---------- GLOBAL EXIT COMBO (START + SELECT) ----------
        # Checked before every screen-specific handler so the combo always
        # works - in the wizard, keyboard, player, lists, settings, anywhere.
        if event.type == SDL_CONTROLLERBUTTONDOWN and \
                self._is_exit_combo(event.cbutton.button):
            LOG("exit requested: START+SELECT combo", "APP")
            SLOG("Exiting PilasTube (Start+Select)")
            self.running = False
            return

        # ---------- v3.1 DIRECTION GATE (all dpad/stick/hat/key sources) ----
        # Every direction event is normalised into an edge-triggered,
        # debounced "accepted direction" here. Duplicate events (SDL2
        # delivering the same physical press as button + hat + axis, axis
        # jitter, hat re-fires) are swallowed by the gate - this is the
        # fix for both the settings "runs away" bug and the player seek
        # storm that relaunched ffmpeg many times per second.
        accepted_dirs = self._gate_input(event)
        if accepted_dirs:
            if not self.is_loading_video:
                self._dispatch_directions(accepted_dirs, now)
            return

        # auto-repeated KEYDOWN events (PC keyboards only): skip
        if event.type == SDL_KEYDOWN:
            try:
                if event.key.repeat:
                    return
            except AttributeError:
                pass

        if self.is_loading_video:
            # never leave a stale auto-repeat running across a screen change
            self.key_held = None
            self._dir_held.clear()
            return

        # ---------- v0.3.8 yt-dlp UPDATE POPUP (Yes/No) ----------
        # A modal: while it is up it owns the input (LEFT/RIGHT toggle the
        # choice, A confirms, B = No). It only ever opens on an idle main
        # UI, so no other handler competes for these buttons.
        if self.update_popup is not None:
            if event.type == SDL_CONTROLLERBUTTONDOWN:
                btn = event.cbutton.button
                if btn == SDL_CONTROLLER_BUTTON_A:
                    self._ytdlp_popup_answer(self.update_popup["choice"] == 0)
                elif btn == SDL_CONTROLLER_BUTTON_B:
                    self._ytdlp_popup_answer(False)
                elif btn in (SDL_CONTROLLER_BUTTON_DPAD_LEFT,
                             SDL_CONTROLLER_BUTTON_DPAD_RIGHT):
                    self.update_popup["choice"] ^= 1
                    self.need_redraw = True
            elif event.type == SDL_KEYDOWN:
                key = event.key.keysym.sym
                if key in (SDLK_RETURN, SDLK_z):
                    self._ytdlp_popup_answer(self.update_popup["choice"] == 0)
                elif key in (SDLK_ESCAPE, SDLK_x):
                    self._ytdlp_popup_answer(False)
                elif key in (SDLK_LEFT, SDLK_RIGHT):
                    self.update_popup["choice"] ^= 1
                    self.need_redraw = True
            return

        # ---------- FIRST-BOOT WIZARD ----------
        if self.wizard_active:
            if event.type == SDL_CONTROLLERBUTTONDOWN:
                btn = event.cbutton.button
                if btn == SDL_CONTROLLER_BUTTON_A:
                    self.wizard_advance()
                elif btn == SDL_CONTROLLER_BUTTON_B:
                    self.wizard_back()
            elif event.type == SDL_KEYDOWN:
                key = event.key.keysym.sym
                if key in (SDLK_RETURN, SDLK_z):
                    self.wizard_advance()
                elif key in (SDLK_ESCAPE, SDLK_x):
                    self.wizard_back()
            return

        # ---------- SEARCH KEYBOARD ----------
        if self.search_active:
            if event.type == SDL_CONTROLLERBUTTONDOWN:
                btn = event.cbutton.button
                if self.sugg_visible and self.sugg_items:
                    if btn == SDL_CONTROLLER_BUTTON_A:
                        self.sugg_select()
                    elif btn == SDL_CONTROLLER_BUTTON_B:
                        self.sugg_visible = False
                        self.need_redraw = True
                    elif btn == SDL_CONTROLLER_BUTTON_START:
                        self._keyboard_go()
                    return
                if btn == SDL_CONTROLLER_BUTTON_A:
                    self.handle_keyboard_select()
                elif btn == SDL_CONTROLLER_BUTTON_B:
                    self.action_back()
                elif btn == SDL_CONTROLLER_BUTTON_START:
                    self._keyboard_go()
                elif btn == SDL_CONTROLLER_BUTTON_Y:
                    if self.search_query:
                        self.search_query = self.search_query[:-1]
                        self.need_redraw = True
                elif btn == SDL_CONTROLLER_BUTTON_X:
                    # v3.6: X = same as the SUG keyboard key - suggestions
                    # on demand, never while typing
                    self.sugg_show()
            return

        # ---------- CONTEXT MENU ----------
        if self.ctx_open:
            if event.type == SDL_CONTROLLERBUTTONDOWN:
                btn = event.cbutton.button
                if btn == SDL_CONTROLLER_BUTTON_A:
                    if self.ctx_items:
                        _, action = self.ctx_items[self.ctx_selected]
                        self.ctx_execute(action)
                elif btn == SDL_CONTROLLER_BUTTON_B:
                    self.ctx_close()
            elif event.type == SDL_KEYDOWN:
                key = event.key.keysym.sym
                if key in (SDLK_RETURN, SDLK_z):
                    if self.ctx_items:
                        _, action = self.ctx_items[self.ctx_selected]
                        self.ctx_execute(action)
                elif key in (SDLK_ESCAPE, SDLK_x):
                    self.ctx_close()
            return

        # ---------- VIDEO INFO PANEL ----------
        if self.info_open:
            if event.type == SDL_CONTROLLERBUTTONDOWN:
                self.info_open = False
                self.info_video = None
                self.need_redraw = True
            elif event.type == SDL_KEYDOWN:
                self.info_open = False
                self.need_redraw = True
            return

        # ---------- QUEUE SCREEN ----------
        if self.queue_open:
            if event.type == SDL_CONTROLLERBUTTONDOWN:
                btn = event.cbutton.button
                if btn == SDL_CONTROLLER_BUTTON_A:
                    self.queue_action_select()
                elif btn == SDL_CONTROLLER_BUTTON_Y:
                    self.queue_remove()
                elif btn == SDL_CONTROLLER_BUTTON_B:
                    self.queue_open = False
                    self.need_redraw = True
            elif event.type == SDL_KEYDOWN:
                key = event.key.keysym.sym
                if key == SDLK_RETURN:
                    self.queue_action_select()
                elif key == SDLK_ESCAPE:
                    self.queue_open = False
                    self.need_redraw = True
            return

        # ---------- PLAYBACK CONTROLS (SmartTube mapping) ----------
        # HUD hidden : A pause | B exit | LEFT/RIGHT seek | DOWN show HUD |
        #              UP chapters | L1/R1 prev/next | L2/R2 volume
        # HUD visible: LEFT/RIGHT move focus in the options row | A activate
        #              the focused option | B/UP/DOWN hide the HUD
        # X: quality | Y: speed | START: options | SELECT: time
        # (dpad/stick directions arrive pre-gated via _dispatch_directions)
        if event.type == SDL_CONTROLLERBUTTONDOWN:
            # --- autoplay countdown owns the input (player already ended,
            #     so is_playing may be False here - handle it FIRST) ---
            if self.autoplay_countdown is not None:
                btn = event.cbutton.button
                if btn == SDL_CONTROLLER_BUTTON_A:
                    self.autoplay_countdown = None
                    self.user_stopped = False
                    self._advance_playback()
                elif btn == SDL_CONTROLLER_BUTTON_B:
                    self.autoplay_countdown = None
                    self.current_video = None
                    self.set_status("Ready")
                    self.need_redraw = True
                return
            if self.is_playing or self.player is not None:
                btn = event.cbutton.button
                # --- modal menu open: it owns the input ---
                if self.player_menu:
                    if btn == SDL_CONTROLLER_BUTTON_A:
                        if self._act_ok("menu-a"):
                            self.player_menu_select()
                    elif btn == SDL_CONTROLLER_BUTTON_B:
                        self.player_menu = None
                        self.hud_last_activity = SDL_GetTicks()
                    return
                if btn == SDL_CONTROLLER_BUTTON_B:
                    # v3.1 (SmartTube): B closes the visible HUD first;
                    # only a second B press leaves the video
                    if self.hud_visible:
                        self._player_hud_toggle()
                    else:
                        self.stop_playback(user=True)
                elif btn == SDL_CONTROLLER_BUTTON_A:
                    if self._act_ok("player-a"):
                        if self.hud_visible:
                            self._hud_activate()
                        else:
                            self.player_toggle_pause()
                        self.hud_last_activity = SDL_GetTicks()
                elif btn == SDL_CONTROLLER_BUTTON_Y:
                    self.player_menu = "speed"
                    self.player_menu_sel = 0
                    self.hud_visible = True
                    self.hud_last_activity = SDL_GetTicks()
                elif btn == SDL_CONTROLLER_BUTTON_X:
                    self.player_menu = "quality"
                    self.player_menu_sel = 0
                    self.hud_visible = True
                    self.hud_last_activity = SDL_GetTicks()
                elif btn == SDL_CONTROLLER_BUTTON_LEFTSHOULDER:
                    self.player_prev_video()
                elif btn == SDL_CONTROLLER_BUTTON_RIGHTSHOULDER:
                    self.player_next_video()
                elif btn == BTN_LTRIG:
                    self.player_chapter_seek(-1)
                elif btn == BTN_RTRIG:
                    self.player_chapter_seek(1)
                elif btn == SDL_CONTROLLER_BUTTON_START:
                    self.player_menu = "options"
                    self.player_menu_sel = 0
                    self.hud_visible = True
                    self.hud_last_activity = SDL_GetTicks()
                elif btn == SDL_CONTROLLER_BUTTON_SELECT:
                    self.player_show_time()
                return

        # L2 / R2 analog triggers = volume (they are AXES in SDL2, not
        # buttons - SDL_CONTROLLER_BUTTON_LEFTTRIGGER does not exist there,
        # so the old "trigger" constants silently aliased the stick clicks)
        if event.type == SDL_CONTROLLERAXISMOTION and self.is_playing and \
                not self.player_menu and self.autoplay_countdown is None:
            try:
                axis = event.caxis.axis
                value = event.caxis.value
            except AttributeError:
                return
            try:
                # SDL2 calls them TRIGGERLEFT/TRIGGERRIGHT; SDL3 renamed
                axis_lt = getattr(sdl2, "SDL_CONTROLLER_AXIS_TRIGGERLEFT",
                                  getattr(sdl2, "SDL_CONTROLLER_AXIS_LEFTTRIGGER", 4))
                axis_rt = getattr(sdl2, "SDL_CONTROLLER_AXIS_TRIGGERRIGHT",
                                  getattr(sdl2, "SDL_CONTROLLER_AXIS_RIGHTTRIGGER", 5))
            except AttributeError:
                axis_lt, axis_rt = 4, 5
            if axis in (axis_lt, axis_rt):
                armed = self._trig_armed.get(axis, True)
                if value > 16000 and armed:
                    self._trig_armed[axis] = False
                    self.player_volume(-5 if axis == axis_lt else 5)
                elif value < 8000:
                    self._trig_armed[axis] = True
            return

        # L2 / R2 analog triggers OUTSIDE the player = main section switch
        # (v3.4, user request: "R2 and L2 are for going to the next section,
        # or the section before" - including ESCAPING the settings screen,
        # which used to swallow them). The triggers never touch the settings
        # rows themselves: those answer to dpad/analog stick only.
        if event.type == SDL_CONTROLLERAXISMOTION and not self.is_playing:
            if self._trigger_section_event(event):
                return

        if event.type == SDL_CONTROLLERBUTTONDOWN:
            btn = event.cbutton.button

            # ---------- SETTINGS SCREEN ----------
            if self.current_nav == NAV_SETTINGS and not self.channel_view:
                if self.login_active:
                    # login screen: B cancels, everything else is consumed
                    if btn == SDL_CONTROLLER_BUTTON_B:
                        self.cancel_login()
                    self.need_redraw = True
                    return
                if btn == SDL_CONTROLLER_BUTTON_A:
                    self.settings_select()
                elif btn == SDL_CONTROLLER_BUTTON_B:
                    self.settings_back()
                elif btn in (SDL_CONTROLLER_BUTTON_LEFTSHOULDER,
                             SDL_CONTROLLER_BUTTON_RIGHTSHOULDER):
                    # bumpers jump between sections (Quick nav, no scrolling)
                    if self.settings_picker is None:
                        n = len(self.settings_sections or [])
                        self.settings_pane = "right"
                        self.settings_row = 0
                        if btn == SDL_CONTROLLER_BUTTON_RIGHTSHOULDER:
                            self.settings_section = min(
                                n - 1, self.settings_section + 1)
                        else:
                            self.settings_section = max(
                                0, self.settings_section - 1)
                        if not self._settings_rows():
                            self.settings_pane = "left"
                # every other button is consumed silently on this screen so
                # it can never leak into the video-list handler (v3.0)
                self.need_redraw = True
                return

            # ---------- VIDEO LISTS ----------
            if btn == SDL_CONTROLLER_BUTTON_A:
                self.action_select()
            elif btn == SDL_CONTROLLER_BUTTON_B:
                self.action_back()
            elif btn == SDL_CONTROLLER_BUTTON_X:
                self.action_search()
            elif btn == SDL_CONTROLLER_BUTTON_Y:
                self.toggle_favorite()
            elif btn == SDL_CONTROLLER_BUTTON_START:
                videos = self._get_filtered_list()
                if videos and self.selected < len(videos):
                    self.build_ctx_menu(videos[self.selected])
            elif btn == SDL_CONTROLLER_BUTTON_SELECT:
                self.open_queue()
            elif btn in (SDL_CONTROLLER_BUTTON_LEFTSHOULDER,
                         SDL_CONTROLLER_BUTTON_RIGHTSHOULDER):
                if btn == SDL_CONTROLLER_BUTTON_LEFTSHOULDER:
                    self.action_left()
                else:
                    self.action_right()
            return

        if event.type == SDL_KEYDOWN:
            key = event.key.keysym.sym
            if self.current_nav == NAV_SETTINGS and not self.channel_view:
                # keyboard mirrors the gamepad settings model (v3.3)
                if self.login_active:
                    if key in (SDLK_ESCAPE, SDLK_x):
                        self.cancel_login()
                    return
                if key in (SDLK_RETURN, SDLK_z):
                    self.settings_select()
                elif key in (SDLK_ESCAPE, SDLK_x):
                    self.settings_back()
                return
            if key in (SDLK_RETURN, SDLK_z):
                self.action_select()
            elif key in (SDLK_ESCAPE, SDLK_x):
                self.action_back()
            elif key == SDLK_c:
                videos = self._get_filtered_list()
                if videos and self.selected < len(videos):
                    self.build_ctx_menu(videos[self.selected])
            elif key == SDLK_q:
                self.open_queue()

    # =====================================================================
    # MAIN LOOP
    # =====================================================================
    def run(self):
        LOG("entering main loop", "APP")
        event = SDL_Event()
        last_render_time = 0

        # v3.3: restore a saved account session in the background
        # ("stay there" - the refresh token keeps the login across reboots)
        run_logged_thread("account-restore", self._restore_account,
                          daemon=True)
        # v3.6: connectivity watchdog - the app NEVER exits or freezes on a
        # wifi drop; it shows "reconnecting" and auto-retries whatever was
        # interrupted when the network comes back.
        self.start_net_watch()

        # v0.3.8: background yt-dlp update check - once per app open,
        # daemon thread (never blocks startup); a newer version triggers
        # the gamepad Yes/No popup once the UI is idle.
        if not self._ytdlp_check_started:
            self._ytdlp_check_started = True
            run_logged_thread("ytdlp-update-check",
                              self._ytdlp_update_check, daemon=True)

        # after the wizard, auto-load the trending feed
        if self.wizard_active:
            while self.running and self.wizard_active:
                while SDL_PollEvent(event):
                    if event.type == SDL_QUIT:
                        self.running = False
                    else:
                        self.handle_event(event)
                self._gate_directions()
                self.update_wifi()
                if self.need_redraw:
                    self.render()
                SDL_Delay(16)
            if not self.running:
                self.cleanup()
                return

        if not self.home_videos:
            self.load_trending()

        while self.running:
            while SDL_PollEvent(event):
                if event.type == SDL_QUIT:
                    self.running = False
                else:
                    self.handle_event(event)

            self._gate_directions()      # v3.1: drop ghost held directions
            self.update_wifi()
            # v3.6: re-run the operation that was interrupted by the wifi
            # drop, the moment connectivity is confirmed (main thread only)
            if not self.net_offline and self._net_pending is not None:
                self.net_run_pending()
            # v0.3.7: after a successful sign-in, rebuild the Recommended tab
            # with the account's own feed (workers may never touch the SDL
            # renderer - the reload happens here, on the main thread, when
            # no video is playing and no batch is in flight)
            if getattr(self, "_reload_home_after_login", False) and \
                    not self.is_playing and self.player is None and \
                    not self.home_batch_loading:
                self._reload_home_after_login = False
                if self.current_nav == NAV_HOME and not self.wizard_active:
                    LOG("reloading home feed after login", "AUTH")
                    self.load_trending()
                else:
                    # off the home tab: just drop the stale logged-out feed
                    # (the tab reload path will refetch on next entry)
                    self.home_videos = []
                    self.home_existing_ids = set()
                    self.home_feed_source = ""
            self.process_repeat()

            # v0.3.8: yt-dlp update popup (deferred to an idle main UI)
            self._ytdlp_maybe_show_popup()

            current_time = SDL_GetTicks()

            if self.is_loading_video:
                self.render_loading_screen(
                    self.t("msg_loading_video"),
                    self.display_title(self.current_video)
                    if self.current_video else "")
            elif self.login_active:
                # v3.3: sign-in screen - keep the spinner animating
                self.render()
            elif self.is_playing or self.player is not None or \
                    self.autoplay_countdown is not None:
                # v3.0: the built-in player renders + advances from the
                # main loop (single SDL process owns the display at all
                # times - no DRM handoff, no black screen)
                self._player_tick()
            elif not self.is_playing:
                is_batch_loading = self.home_batch_loading or \
                    self.search_batch_loading or self.subs_loading or \
                    self.channel_loading
                force_render = (current_time - last_render_time) >= 100
                if self.need_redraw or self.is_loading or self.loading_images or \
                        is_batch_loading or self.is_searching or force_render or \
                        self.net_offline:
                    self.render()
                    last_render_time = current_time

            SDL_Delay(16)

        self.cleanup()

    def cleanup(self):
        try:
            if self.player is not None:
                self._builtin_teardown()
        except Exception:
            pass
        try:
            if self.player_process:
                self.stop_playback(user=True)
        except Exception:
            pass
        try:
            if self.audio_dev is not None:
                self._close_audio_device()
        except Exception:
            pass
        try:
            self.prefs.save()
        except Exception:
            pass

        for tex, _, _ in self.text_cache.values():
            if tex:
                SDL_DestroyTexture(tex)
        for tex, _, _ in self.image_cache.values():
            if tex:
                SDL_DestroyTexture(tex)
        try:
            _destroy_icon_cache()
        except Exception:
            pass

        if self.font:
            ttf.TTF_CloseFont(self.font)
        if self.font_large:
            ttf.TTF_CloseFont(self.font_large)
        if self.font_small:
            ttf.TTF_CloseFont(self.font_small)
        if self.font_tiny:
            ttf.TTF_CloseFont(self.font_tiny)

        if self.controller:
            SDL_GameControllerClose(self.controller)
        if self.joystick:
            SDL_JoystickClose(self.joystick)

        ttf.TTF_Quit()
        if self.renderer:
            SDL_DestroyRenderer(self.renderer)
        if self.window:
            SDL_DestroyWindow(self.window)
        SDL_Quit()
        LOG("cleanup complete - exiting main loop", "APP")



# ----------------------------------------------------------------------------
# player.py keeps the original verbatim reference
# `PilasTubeApp._ffmpeg_subtitles_probe` (inside
# _ffmpeg_has_subtitles); inject the assembled class into
# player's namespace so that reference resolves exactly
# as it did in the monolith (class attribute read/write).
# ----------------------------------------------------------------------------
player.PilasTubeApp = PilasTubeApp



if __name__ == "__main__":
    print("Script dir: %s" % SCRIPT_DIR)
    print("PilasTube %s" % APP_VERSION)
    print("yt-dlp: %s" % YTDLP_PATH)
    print("Player: %s" % VIDEO_PLAYER)
    print("Python: %s" % _py_version())

    app = None
    try:
        app = PilasTubeApp()
        app.run()
    except SystemExit:
        raise
    except Exception as e:
        _PLOG.crash("main loop", sys.exc_info())
        SLOG("PilasTube crashed and closed - see logs/detailed.txt")
        print("FATAL ERROR: %s" % e)
        traceback.print_exc()
        _show_crash_screen(app, [
            "The app hit an unexpected error:",
            "",
            _first_line(e),
            "",
            "Full details were saved to:",
            "logs/detailed.txt",
        ])
        sys.exit(1)
