#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
PilasTube v3.5 - ui.py (rendering domain)

UIMixin: every main-screen renderer (tabs, video lists, category tiles,
two-pane settings, keyboard, suggestions, context menu, video info, wizard,
login screen assets) plus the drawing toolkit (fonts, text, rects, spinner,
thumbnails, logo, WiFi/battery indicators) and the fatal-error screen.
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
    CATEGORY_DEFS,
    LOG,
    NAV_CATEGORIES,
    NAV_HISTORY,
    NAV_HOME,
    NAV_SEARCH,
    NAV_SETTINGS,
    NAV_SUBS,
    SCREEN_HEIGHT,
    SCREEN_WIDTH,
    UI_SCALE,
    SCRIPT_DIR,
    SDL_CONTROLLERBUTTONDOWN,
    SDL_Color,
    SDL_CreateTextureFromSurface,
    SDL_Delay,
    SDL_DestroyTexture,
    SDL_Event,
    SDL_FreeSurface,
    SDL_GetTicks,
    SDL_IMAGE_AVAILABLE,
    SDL_JOYBUTTONDOWN,
    SDL_KEYDOWN,
    SDL_PollEvent,
    SDL_QUIT,
    SDL_Rect,
    SDL_RenderClear,
    SDL_RenderCopy,
    SDL_RenderFillRect,
    SDL_RenderPresent,
    SDL_SetRenderDrawColor,
    THEMES,
    WIZARD_STEPS,
    _read_wifi_state,
    fmt_clock,
    run_logged_thread,
    sdlimage,
    ttf,
)

def _show_crash_screen(app, exc_lines):
    """Best-effort on-screen fatal error display (needs a live renderer).

    Waits up to ~10 seconds or until any button/key event so the user can
    actually read what happened before the process exits.
    """
    try:
        if not app or not getattr(app, "renderer", None):
            return
        event = SDL_Event()
        end = SDL_GetTicks() + 10000
        while SDL_GetTicks() < end:
            while SDL_PollEvent(event):
                if event.type in (SDL_QUIT, SDL_KEYDOWN, SDL_JOYBUTTONDOWN,
                                  SDL_CONTROLLERBUTTONDOWN):
                    return
            SDL_SetRenderDrawColor(app.renderer, 24, 8, 8, 255)
            SDL_RenderClear(app.renderer)
            y = 40
            app.draw_text_centered("PilasTube - ERROR", SCREEN_WIDTH / 2, y,
                                   app.C.STATUS_ERROR, app.font_large)
            y += 60
            for line in exc_lines[:12]:
                app.draw_text(line[:74], 30, y, app.C.TEXT_PRIMARY,
                              app.font_small)
                y += 22
            y += 14
            app.draw_text("Details: logs/detailed.txt", 30, y,
                          app.C.TEXT_SECONDARY, app.font_small)
            y += 22
            app.draw_text("Press any button to exit", 30, y,
                          app.C.TEXT_TERTIARY, app.font_tiny)
            SDL_RenderPresent(app.renderer)
            SDL_Delay(50)
    except Exception:
        pass



class UIMixin(object):
    """Every main-screen renderer + the drawing toolkit.
    Hosted by PilasTubeApp; all state lives on self."""
    # ------------------------------------------------------------------ setup
    def _find_font(self):
        # Knulli / Miyoo Flip fix: search Knulli (Batocera-based) font paths and Knulli's PortMaster location.
        # Standard PortMaster on Knulli lives at /userdata/system/.local/share/PortMaster.
        # Batocera/Knulli system fonts live at /usr/share/fonts/dejavu/DejaVuSans.ttf (without 'truetype/').
        paths = [
            os.path.join(SCRIPT_DIR, "font.ttf"),
            "/userdata/system/.local/share/PortMaster/themes/default.ttf",
            "/userdata/system/.local/share/PortMaster/theme/default.ttf",
            "/usr/share/fonts/dejavu/DejaVuSans.ttf",
            "/usr/share/fonts/cantarell/Cantarell-Regular.ttf",
            "/usr/share/fonts/liberation/LiberationSans-Regular.ttf",
            "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
            "/usr/share/fonts/TTF/DejaVuSans.ttf",
            "/opt/system/Tools/PortMaster/themes/default.ttf",
        ]
        for p in paths:
            if os.path.exists(p):
                return p
        # Fallback for Knulli: scan /usr/share/fonts recursively for any usable TTF font
        import glob
        for font_candidate in glob.glob("/usr/share/fonts/**/*.ttf", recursive=True):
            if os.path.isfile(font_candidate):
                return font_candidate
        # Fallback for PortMaster themes: scan theme directory
        for font_candidate in glob.glob("/userdata/system/.local/share/PortMaster/**/*.ttf", recursive=True):
            if os.path.isfile(font_candidate):
                return font_candidate
        return None

    def _apply_theme(self):
        self.C = THEMES.get(self.prefs.get("theme", "Dark"), THEMES["Dark"])

    # =====================================================================
    # THUMBNAILS (cached, async - carried over from v1)
    # =====================================================================
    def get_thumb_path(self, url):
        h = hashlib.md5(url.encode()).hexdigest()
        return os.path.join(self.image_cache_dir, "%s.jpg" % h)

    def download_thumbnail(self, url):
        if not url or url in self.failed_images or url in self.loading_images:
            return
        if len(self.loading_images) >= 4:
            return
        self.loading_images.add(url)

        def worker():
            try:
                cache_path = self.get_thumb_path(url)
                if os.path.exists(cache_path):
                    return
                download_url = url
                if download_url.startswith("//"):
                    download_url = "https:" + download_url
                req = urllib.request.Request(download_url, headers={
                    "User-Agent": "Mozilla/5.0"})
                with urllib.request.urlopen(req, timeout=6,
                                            context=ssl._create_unverified_context()) as resp:
                    data = resp.read()
                if len(data) > 500:
                    with open(cache_path, "wb") as f:
                        f.write(data)
                else:
                    self.failed_images.add(url)
            except Exception:
                self.failed_images.add(url)
            finally:
                self.loading_images.discard(url)
                self.need_redraw = True

        run_logged_thread("image-loader", worker)

    def load_thumbnail(self, url):
        if not url:
            return None
        if url in self.image_cache:
            return self.image_cache[url]
        if url in self.failed_images:
            return None
        cache_path = self.get_thumb_path(url)
        if os.path.exists(cache_path) and SDL_IMAGE_AVAILABLE:
            try:
                surface = sdlimage.IMG_Load(cache_path.encode())
                if surface:
                    texture = SDL_CreateTextureFromSurface(self.renderer, surface)
                    w, h = surface.contents.w, surface.contents.h
                    SDL_FreeSurface(surface)
                    if texture:
                        if len(self.image_cache) > 40:
                            old_key = next(iter(self.image_cache))
                            old_tex = self.image_cache.pop(old_key)
                            if old_tex and old_tex[0]:
                                SDL_DestroyTexture(old_tex[0])
                        self.image_cache[url] = (texture, w, h)
                        return (texture, w, h)
            except Exception as e:
                print("Load thumbnail error: %s" % e)
        if url not in self.loading_images:
            self.download_thumbnail(url)
        return None

    def draw_thumbnail(self, x, y, width, height, url):
        self.draw_rect(x, y, width, height, self.C.THUMB_BG)
        if not url:
            return
        result = self.load_thumbnail(url)
        if result:
            texture, img_w, img_h = result
            if texture:
                aspect = img_w / img_h if img_h else 16 / 9
                target_aspect = width / height
                if aspect > target_aspect:
                    draw_w = width
                    draw_h = int(width / aspect)
                    draw_x = x
                    draw_y = y + (height - draw_h) // 2
                else:
                    draw_h = height
                    draw_w = int(height * aspect)
                    draw_x = x + (width - draw_w) // 2
                    draw_y = y
                dst = SDL_Rect(int(draw_x), int(draw_y), int(draw_w), int(draw_h))
                SDL_RenderCopy(self.renderer, texture, None, dst)
                return
        if url in self.loading_images:
            dots = "." * ((self.frame_count // 20) % 4)
            self.draw_text(dots, x + width // 2 - 10, y + height // 2 - 5,
                           self.C.TEXT_SECONDARY, self.font_small)

    # =====================================================================
    # DRAWING PRIMITIVES
    # =====================================================================
    def draw_rect(self, x, y, w, h, color, alpha=255):
        SDL_SetRenderDrawColor(self.renderer, color[0], color[1], color[2], alpha)
        SDL_RenderFillRect(self.renderer, SDL_Rect(int(x), int(y), int(w), int(h)))

    def draw_spinner(self, center_x, center_y, radius=12, dot_size=3):
        import math
        positions = []
        for i in range(8):
            angle = math.pi / 2 - (i * math.pi / 4)
            px = center_x + int(radius * math.cos(angle))
            py = center_y - int(radius * math.sin(angle))
            positions.append((px, py))
        active_index = (self.frame_count // 6) % 8
        for i, (px, py) in enumerate(positions):
            if i == active_index:
                self.draw_rect(px - dot_size, py - dot_size, dot_size * 2,
                               dot_size * 2, self.C.YT_RED)
            else:
                self.draw_rect(px - 1, py - 1, 2, 2, self.C.TEXT_TERTIARY)

    def text_factor(self, font):
        if font is self.font_large:
            return 7
        if font is self.font:
            return 5
        if font is self.font_small:
            return 4
        return 3

    def draw_text(self, text, x, y, color=None, font=None):
        if color is None:
            color = self.C.TEXT_PRIMARY
        if not font:
            font = self.font
        if not font:
            return 0
        text = str(text)[:80]
        key = (text, color, id(font))
        if key not in self.text_cache:
            if len(self.text_cache) > 200:
                for tex, _, _ in self.text_cache.values():
                    if tex:
                        SDL_DestroyTexture(tex)
                self.text_cache.clear()
            sdl_color = SDL_Color(color[0], color[1], color[2], 255)
            surface = ttf.TTF_RenderUTF8_Blended(font, text.encode("utf-8"), sdl_color)
            if not surface:
                return 0
            w, h = surface.contents.w, surface.contents.h
            texture = SDL_CreateTextureFromSurface(self.renderer, surface)
            SDL_FreeSurface(surface)
            self.text_cache[key] = (texture, w, h)
        tex, w, h = self.text_cache[key]
        if tex:
            # v0.3.8: fonts are rasterised at PHYSICAL size (design x
            # UI_SCALE) - divide the destination back to LOGICAL layout
            # coordinates so every existing position/size math is
            # unchanged while the glyphs stay pixel-crisp at native res.
            sc = UI_SCALE if UI_SCALE and UI_SCALE > 1.0 else 1.0
            dw, dh = w, h
            if sc != 1.0:
                dw = max(1, int(round(w / sc)))
                dh = max(1, int(round(h / sc)))
            SDL_RenderCopy(self.renderer, tex, None,
                           SDL_Rect(int(x), int(y), dw, dh))
            return dw
        return w

    def draw_text_centered(self, text, cx, y, color=None, font=None):
        if font is None:
            font = self.font
        text = str(text)
        approx = len(text) * self.text_factor(font)
        return self.draw_text(text, int(cx - approx / 2), y, color, font)

    # =====================================================================
    # RENDER
    # =====================================================================
    def render(self):
        self.draw_rect(0, 0, SCREEN_WIDTH, SCREEN_HEIGHT, self.C.BG_PRIMARY)
        if self.wizard_active:
            self.render_wizard()
            SDL_RenderPresent(self.renderer)
            self.need_redraw = False
            self.frame_count += 1
            return
        if self.login_active:
            # v3.3: the sign-in screen takes over the whole display
            self.render_login_screen()
            SDL_RenderPresent(self.renderer)
            self.need_redraw = False
            self.frame_count += 1
            return
        self.render_header()
        if self.search_active:
            self.render_keyboard()
        else:
            self.render_content()
        self.render_navigation()
        # v3.6: the reconnecting panel sits above content + nav (the tab
        # bar stays visible) but below menus; hidden while the player runs
        # (a buffering video is its own offline feedback).
        if self.net_offline and not self.is_playing and \
                self.player is None and not self.is_loading_video and \
                self.autoplay_countdown is None:
            self.render_offline_overlay()
        if self.ctx_open:
            self.render_context_menu()
        elif self.info_open:
            self.render_video_info()
        elif self.queue_open:
            self.render_queue_screen()
        # v0.3.8: the yt-dlp update popup sits above everything else
        # (it only ever opens on an idle main UI)
        if self.update_popup is not None:
            self._render_update_popup()
        SDL_RenderPresent(self.renderer)
        self.need_redraw = False
        self.frame_count += 1

    def _render_update_popup(self):
        """v0.3.8: yt-dlp update offer - SmartTube-style Yes/No dialog.

        LEFT/RIGHT move the focus, A confirms, B = No. Yes runs the real
        updater (the settings action); No dismisses until next launch.
        """
        p = self.update_popup or {}
        box_w = 330
        box_h = 190
        box_x = (SCREEN_WIDTH - box_w) // 2
        box_y = max(40, (SCREEN_HEIGHT - box_h) // 2 - 16)
        # scrim + card
        self.draw_rect(0, 0, SCREEN_WIDTH, SCREEN_HEIGHT, (0, 0, 0), 150)
        self.draw_rect(box_x, box_y, box_w, box_h, self.C.CARD_BG)
        self.draw_rect(box_x, box_y, box_w, 3, self.C.YT_RED)
        # header
        self.draw_text(self.t("update_title")[:30], box_x + 14, box_y + 12,
                       self.C.TEXT_PRIMARY, self.font_small)
        # version rows
        self.draw_text("%s:" % self.t("update_current"), box_x + 14,
                       box_y + 44, self.C.TEXT_SECONDARY, self.font_small)
        self.draw_text(str(p.get("current", "?"))[:20], box_x + 150,
                       box_y + 44, self.C.TEXT_PRIMARY, self.font_small)
        self.draw_text("%s:" % self.t("update_latest"), box_x + 14,
                       box_y + 64, self.C.TEXT_SECONDARY, self.font_small)
        self.draw_text(str(p.get("latest", "?"))[:20], box_x + 150,
                       box_y + 64, self.C.STATUS_LOADING, self.font_small)
        self.draw_text(self.t("update_ask"), box_x + 14, box_y + 90,
                       self.C.TEXT_PRIMARY, self.font)
        # Yes / No buttons
        choice = p.get("choice", 0)
        bw, bh, gap = 140, 34, 18
        by = box_y + box_h - 52
        bx1 = box_x + (box_w - bw * 2 - gap) // 2
        bx2 = bx1 + bw + gap
        for i, (bx, label) in enumerate(((bx1, "update_yes"),
                                         (bx2, "update_no"))):
            sel = (i == choice)
            self.draw_rect(bx, by, bw, bh,
                           self.C.CARD_SELECTED if sel else self.C.BG_TERTIARY)
            if sel:
                self.draw_rect(bx, by + bh - 3, bw, 3, self.C.YT_RED)
            self.draw_text_centered(self.t(label), bx + bw // 2, by + 10,
                                    self.C.TEXT_PRIMARY if sel
                                    else self.C.TEXT_SECONDARY,
                                    self.font_small)
        # hint line
        self.draw_text("< > : %s/%s   A: OK   B: %s" % (
            self.t("update_yes")[:10], self.t("update_no")[:8],
            self.t("update_no")[:8]), box_x + 14, box_y + box_h - 22,
            self.C.TEXT_TERTIARY, self.font_tiny)

    def render_offline_overlay(self):
        """v3.6: WiFi dropped - 'Reconnecting...' panel with a live attempt
        counter. The app keeps running; the interrupted operation is
        retried automatically by the watchdog when connectivity returns."""
        w, h = 400, 196
        x = (SCREEN_WIDTH - w) // 2
        y = (SCREEN_HEIGHT - h) // 2 - 20
        self.draw_rect(0, 0, SCREEN_WIDTH, SCREEN_HEIGHT, (0, 0, 0), 150)
        self.draw_rect(x, y, w, h, self.C.BG_SECONDARY, 255)
        self.draw_rect(x, y, w, 3, self.C.YT_RED)
        # big crossed-out wifi fan (centered expanding bars + dot + slash)
        cx, cy = SCREEN_WIDTH // 2, y + 34
        for i, half in enumerate((4, 8, 12, 16)):
            self.draw_rect(cx - half, cy + i * 4, half * 2, 3,
                           self.C.TEXT_SECONDARY)
        self.draw_rect(cx - 3, cy + 18, 6, 6, self.C.TEXT_SECONDARY)
        for i in range(18):        # red slash = no signal
            self.draw_rect(cx - 16 + i, cy + 22 - i, 2, 2,
                           self.C.STATUS_ERROR)
        self.draw_text_centered(self.t("msg_no_internet"),
                                SCREEN_WIDTH // 2, y + 84,
                                self.C.TEXT_PRIMARY, self.font)
        self.draw_text_centered(self.t("msg_reconnecting"),
                                SCREEN_WIDTH // 2, y + 108,
                                self.C.STATUS_ERROR, self.font_small)
        self.draw_spinner(SCREEN_WIDTH // 2, y + 134, 8)
        att = self.t("msg_net_attempts") % self.net_attempts \
            if "%s" in self.t("msg_net_attempts") else \
            "%d" % self.net_attempts
        self.draw_text_centered(att, SCREEN_WIDTH // 2, y + 152,
                                self.C.TEXT_TERTIARY, self.font_tiny)
        self.draw_text_centered(self.t("msg_exit_hint"),
                                SCREEN_WIDTH // 2, y + h - 18,
                                self.C.TEXT_TERTIARY, self.font_tiny)

    def render_loading_screen(self, title="Loading...", subtitle=""):
        self.draw_rect(0, 0, SCREEN_WIDTH, SCREEN_HEIGHT, (0, 0, 0))
        # PilasTube logo
        self.draw_logo(SCREEN_WIDTH // 2 - 20, SCREEN_HEIGHT // 2 - 110,
                       40, 28)

        y = SCREEN_HEIGHT // 2 - 55
        self.draw_text_centered(title, SCREEN_WIDTH // 2, y,
                                self.C.TEXT_PRIMARY, self.font_large)
        # subtitle (video title)
        if subtitle:
            short = subtitle[:44] + "..." if len(subtitle) > 44 else subtitle
            self.draw_text_centered(short, SCREEN_WIDTH // 2, y + 38,
                                    self.C.TEXT_SECONDARY, self.font_small)
        # quality note + resume info
        extra = []
        if self.next_info and len(self.next_info) >= 2:
            note = self.next_info[2] if len(self.next_info) > 2 else ""
            height = self.next_info[1]
            extra.append("%s%s" % (("%sp " % height) if height else "", note))
        pos = self.get_position(self.current_video.id) if self.current_video else None
        if pos and pos[0] > 30:
            extra.append("%s %s" % (self.t("msg_resuming"), fmt_clock(pos[0])))
        if extra:
            self.draw_text_centered("  |  ".join(extra), SCREEN_WIDTH // 2, y + 62,
                                    self.C.TEXT_TERTIARY, self.font_small)
        # dislike info (async RYD)
        if self.loading_ryd:
            self.draw_text_centered(self.loading_ryd, SCREEN_WIDTH // 2, y + 82,
                                    self.C.TEXT_SECONDARY, self.font_small)
        # animated progress bar
        bar_width, bar_height = 200, 4
        bar_x = SCREEN_WIDTH // 2 - bar_width // 2
        bar_y = SCREEN_HEIGHT // 2 + 55
        self.draw_rect(bar_x, bar_y, bar_width, bar_height, self.C.PROGRESS_BG)
        progress_width = 60
        offset = (self.frame_count * 3) % (bar_width + progress_width)
        start_x = bar_x + offset - progress_width
        if start_x < bar_x:
            draw_start = bar_x
            draw_width = progress_width - (bar_x - start_x)
        else:
            draw_start = start_x
            draw_width = min(progress_width, bar_x + bar_width - start_x)
        if draw_width > 0 and draw_start < bar_x + bar_width:
            self.draw_rect(int(draw_start), bar_y, int(draw_width), bar_height,
                           self.C.YT_RED)
        SDL_RenderPresent(self.renderer)
        self.frame_count += 1

    def draw_logo(self, x, y, w=34, h=24):
        """The PilasTube mark: a battery ('pilha' in Portuguese) with a
        white play button inside - distinct from any YouTube asset."""
        c = self.C.YT_RED
        body_w = w - 5
        # battery body with rounded corners
        self.draw_rect(x + 2, y, body_w - 4, h, c)
        self.draw_rect(x, y + 2, body_w, h - 4, c)
        self.draw_rect(x + 1, y + 1, body_w - 2, h - 2, c)
        # battery terminal (the positive nub)
        self.draw_rect(x + body_w, y + h // 2 - 4, 5, 8, c)
        # white play triangle inside the body
        tri_h = max(8, h - 10)
        tri_w = max(6, tri_h * 5 // 6)
        tri_x = x + (body_w - tri_w) // 2 - 1
        tri_y = y + (h - tri_h) // 2
        if tri_h > 1:
            for i in range(tri_h):
                row_w = int(round(
                    tri_w * 2.0 * min(i, tri_h - 1 - i) / float(tri_h - 1)))
                if row_w < 1:
                    row_w = 1
                self.draw_rect(tri_x, tri_y + i, row_w, 1,
                               self.C.TEXT_PRIMARY)

    def draw_wifi_icon(self, x, y):
        """Top-left WiFi indicator (v2.2): fan arcs show the signal
        strength of the router connection; red + slash when offline.
        v3.6: the watchdog's net_offline state wins even when the interface
        is up ("internet" indicator, not "interface" indicator)."""
        connected = self.wifi_connected and not self.net_offline
        level = self.wifi_level if connected else 0
        on = self.C.STATUS_SUCCESS if connected else self.C.STATUS_ERROR
        off = self.C.TEXT_TERTIARY
        # three arcs (outer/middle/inner), two pixel rows each, all centred
        arcs = [
            (y + 0, x + 2, 13), (y + 1, x + 1, 15),   # outer arc
            (y + 3, x + 4, 9),  (y + 4, x + 3, 11),   # middle arc
            (y + 6, x + 6, 5),  (y + 7, x + 5, 7),    # inner arc
        ]
        lit = max(0, min(4, level))          # 1 = dot only ... 4 = full fan
        for pair in range(3):
            arc_on = connected and lit >= (4 - pair)
            color = on if (arc_on or not connected) else off
            top = arcs[pair * 2]
            bot = arcs[pair * 2 + 1]
            self.draw_rect(top[1], top[0], top[2], 1, color)
            self.draw_rect(bot[1], bot[0], bot[2], 1, color)
        # signal dot at the bottom - lit whenever connected
        self.draw_rect(x + 7, y + 10, 3, 3,
                       on if connected else self.C.STATUS_ERROR)
        if not connected:
            # red slash across the fan = "no WiFi"
            for i in range(12):
                self.draw_rect(x + 2 + i, y + 11 - i, 2, 2,
                               self.C.STATUS_ERROR)

    def update_wifi(self):
        """Refresh the WiFi indicator from the kernel (throttled to 3s)."""
        now = time.time()
        if self._wifi_next_check and now < self._wifi_next_check:
            return
        self._wifi_next_check = now + 3.0
        try:
            level, connected = _read_wifi_state()
        except Exception:
            level, connected = 0, False
        if (level, connected) != (self.wifi_level, self.wifi_connected):
            LOG("wifi: connected=%s bars=%d" % (connected, level), "NET")
            self.wifi_level = level
            self.wifi_connected = connected
            self.need_redraw = True

    def render_header(self):
        self.draw_rect(0, 0, SCREEN_WIDTH, 50, self.C.BG_PRIMARY)
        # v2.2: WiFi signal indicator in the top-left corner (v3.6: red
        # when the watchdog says the INTERNET is down, interface or not)
        self.draw_wifi_icon(10, 17)
        # PilasTube mark + wordmark
        self.draw_logo(36, 12, 34, 24)
        w1 = self.draw_text("Pilas", 78, 13, self.C.TEXT_PRIMARY,
                            self.font_large)
        self.draw_text("Tube", 78 + w1 + 1, 13, self.C.YT_RED,
                       self.font_large)

        # status (top-right, coloured)
        if self.status:
            color = self.C.STATUS_SUCCESS
            if self.status_type == "loading":
                color = self.C.STATUS_LOADING
            elif self.status_type == "error":
                color = self.C.STATUS_ERROR
            self.draw_text(self.status[:38], SCREEN_WIDTH - 12 - len(self.status[:38]) * 3,
                           6, color, self.font_tiny)

        # queue badge
        if self.queue:
            qtxt = "Q:%d" % len(self.queue)
            self.draw_text(qtxt, SCREEN_WIDTH - 60, 28, self.C.BADGE_NEW, self.font_tiny)

        # channel view title
        if self.channel_view:
            ch = self.channel_view.get("title", "") or self.t("channel_title")
            self.draw_text("> %s" % ch[:24], 210, 20, self.C.TEXT_SECONDARY,
                           self.font_small)
        self.draw_rect(0, 49, SCREEN_WIDTH, 1, self.C.DIVIDER)

    def render_navigation(self):
        nav_y = SCREEN_HEIGHT - 55
        help_y = nav_y - 18
        self.draw_rect(0, help_y, SCREEN_WIDTH, 18, self.C.BG_SECONDARY)

        if self.search_active:
            help_text = self.t("help_keyboard")
        elif self.ctx_open or self.info_open:
            help_text = self.t("help_ctx")
        elif self.queue_open:
            help_text = self.t("help_queue")
        else:
            help_text = self.t("help_main")
        self.draw_text(help_text, SCREEN_WIDTH // 2 - len(help_text) * 3,
                       help_y + 3, self.C.TEXT_TERTIARY, self.font_tiny)

        self.draw_rect(0, nav_y, SCREEN_WIDTH, 55, self.C.NAV_BG)
        self.draw_rect(0, nav_y, SCREEN_WIDTH, 1, self.C.DIVIDER)

        items = [
            ("home", self.t("nav_recommended"), NAV_HOME),
            ("subs", self.t("nav_subs"), NAV_SUBS),
            ("search", self.t("nav_search"), NAV_SEARCH),
            ("categories", self.t("nav_categories"), NAV_CATEGORIES),
            ("history", self.t("nav_history"), NAV_HISTORY),
            ("settings", self.t("nav_settings"), NAV_SETTINGS),
        ]
        item_w = SCREEN_WIDTH // len(items)
        for i, (icon_type, label, nav_id) in enumerate(items):
            x = i * item_w
            cx = x + item_w // 2
            active = self.current_nav == nav_id and not self.channel_view
            if active:
                self.draw_rect(cx - 20, nav_y + 2, 40, 3, self.C.YT_RED)
            icon_color = self.C.NAV_ACTIVE if active else self.C.NAV_INACTIVE
            icon_y = nav_y + 12
            hole = self.C.NAV_BG if active else self.C.BG_PRIMARY

            if icon_type == "home":
                # v3.4 recommended: play button in a rounded screen
                self.draw_rect(cx - 6, icon_y, 12, 13, icon_color)
                self.draw_rect(cx - 4, icon_y + 2, 8, 9, hole)
                # play triangle (rows grow then shrink)
                self.draw_rect(cx - 1, icon_y + 4, 4, 5, icon_color)
                self.draw_rect(cx - 2, icon_y + 5, 6, 3, icon_color)
            elif icon_type == "subs":
                # bell
                self.draw_rect(cx - 4, icon_y + 1, 8, 2, icon_color)
                self.draw_rect(cx - 5, icon_y + 3, 10, 5, icon_color)
                self.draw_rect(cx - 4, icon_y + 8, 8, 2, icon_color)
                self.draw_rect(cx - 6, icon_y + 3, 2, 4, icon_color)
                self.draw_rect(cx + 4, icon_y + 3, 2, 4, icon_color)
                self.draw_rect(cx - 1, icon_y + 11, 2, 3, icon_color)
            elif icon_type == "search":
                self.draw_rect(cx - 3, icon_y, 6, 2, icon_color)
                self.draw_rect(cx - 5, icon_y + 2, 2, 2, icon_color)
                self.draw_rect(cx + 3, icon_y + 2, 2, 2, icon_color)
                self.draw_rect(cx - 6, icon_y + 4, 2, 4, icon_color)
                self.draw_rect(cx + 4, icon_y + 4, 2, 4, icon_color)
                self.draw_rect(cx - 5, icon_y + 8, 2, 2, icon_color)
                self.draw_rect(cx + 3, icon_y + 8, 2, 2, icon_color)
                self.draw_rect(cx - 3, icon_y + 10, 6, 2, icon_color)
                self.draw_rect(cx + 4, icon_y + 11, 3, 2, icon_color)
                self.draw_rect(cx + 6, icon_y + 13, 3, 2, icon_color)
            elif icon_type == "categories":
                # v3.4 categories: 2x3 grid (YouTube Explore style)
                self.draw_rect(cx - 5, icon_y + 1, 4, 4, icon_color)
                self.draw_rect(cx + 1, icon_y + 1, 4, 4, icon_color)
                self.draw_rect(cx - 5, icon_y + 7, 4, 4, icon_color)
                self.draw_rect(cx + 1, icon_y + 7, 4, 4, icon_color)
                self.draw_rect(cx - 5, icon_y + 13, 10, 2, icon_color)
            elif icon_type == "favorites":
                # kept for other renderers that still ask for it
                self.draw_rect(cx - 5, icon_y + 2, 4, 4, icon_color)
                self.draw_rect(cx + 1, icon_y + 2, 4, 4, icon_color)
                self.draw_rect(cx - 6, icon_y + 3, 2, 3, icon_color)
                self.draw_rect(cx + 4, icon_y + 3, 2, 3, icon_color)
                self.draw_rect(cx - 4, icon_y + 1, 2, 2, icon_color)
                self.draw_rect(cx + 2, icon_y + 1, 2, 2, icon_color)
                self.draw_rect(cx - 6, icon_y + 5, 12, 3, icon_color)
                self.draw_rect(cx - 5, icon_y + 8, 10, 2, icon_color)
                self.draw_rect(cx - 4, icon_y + 10, 8, 2, icon_color)
                self.draw_rect(cx - 3, icon_y + 12, 6, 1, icon_color)
                self.draw_rect(cx - 2, icon_y + 13, 4, 1, icon_color)
                self.draw_rect(cx - 1, icon_y + 14, 2, 1, icon_color)
            elif icon_type == "history":
                self.draw_rect(cx - 3, icon_y, 6, 2, icon_color)
                self.draw_rect(cx - 5, icon_y + 2, 2, 2, icon_color)
                self.draw_rect(cx + 3, icon_y + 2, 2, 2, icon_color)
                self.draw_rect(cx - 6, icon_y + 4, 2, 6, icon_color)
                self.draw_rect(cx + 4, icon_y + 4, 2, 6, icon_color)
                self.draw_rect(cx - 5, icon_y + 10, 2, 2, icon_color)
                self.draw_rect(cx + 3, icon_y + 10, 2, 2, icon_color)
                self.draw_rect(cx - 3, icon_y + 12, 6, 2, icon_color)
                self.draw_rect(cx - 1, icon_y + 6, 2, 2, icon_color)
                self.draw_rect(cx - 1, icon_y + 3, 2, 3, icon_color)
                self.draw_rect(cx + 1, icon_y + 6, 3, 2, icon_color)
            elif icon_type == "settings":
                self.draw_rect(cx - 3, icon_y + 4, 6, 6, icon_color)
                self.draw_rect(cx - 1, icon_y + 6, 2, 2, hole)
                self.draw_rect(cx - 2, icon_y, 4, 4, icon_color)
                self.draw_rect(cx - 2, icon_y + 10, 4, 4, icon_color)
                self.draw_rect(cx - 7, icon_y + 5, 4, 4, icon_color)
                self.draw_rect(cx + 3, icon_y + 5, 4, 4, icon_color)
                self.draw_rect(cx - 6, icon_y + 1, 3, 3, icon_color)
                self.draw_rect(cx + 3, icon_y + 1, 3, 3, icon_color)
                self.draw_rect(cx - 6, icon_y + 10, 3, 3, icon_color)
                self.draw_rect(cx + 3, icon_y + 10, 3, 3, icon_color)

            label_color = self.C.TEXT_PRIMARY if active else self.C.TEXT_TERTIARY
            self.draw_text(label, cx - len(label) * 3, nav_y + 35,
                           label_color, self.font_tiny)

    # ------------------------------------------------------------- content
    def render_content(self):
        y = 55
        h = SCREEN_HEIGHT - 55 - 73

        if self.current_nav == NAV_SETTINGS and not self.channel_view:
            self.render_settings(y, h)
            return
        if self.is_searching:
            self.render_searching(y)
            return
        # v3.4: the Categories tab shows the tile list until a category is
        # opened (then the normal video-card list takes over)
        if self.current_nav == NAV_CATEGORIES and not self.channel_view \
                and not self.category_open:
            self.render_category_list(y, h)
            return
        videos = self._get_filtered_list()
        if videos:
            self.render_video_list(videos, y, h)
        else:
            self.render_empty(y)

    def render_searching(self, y):
        msg = self.t("msg_searching")
        self.draw_text_centered(msg, SCREEN_WIDTH // 2, y + 100,
                                self.C.TEXT_SECONDARY, self.font)
        if self.last_search_query:
            query_text = '"%s"' % self.last_search_query
            if len(query_text) > 35:
                query_text = query_text[:32] + '..."'
            self.draw_text_centered(query_text, SCREEN_WIDTH // 2, y + 130,
                                    self.C.TEXT_TERTIARY, self.font_small)
        self.draw_spinner(SCREEN_WIDTH // 2, y + 190, radius=14, dot_size=4)

    def render_empty(self, y):
        msg = self.t("msg_press_search")
        if not self.ytdlp_path:
            msg = self.t("msg_no_ytdlp")
        elif not self.video_player:
            msg = self.t("msg_no_player")
        elif self.current_nav == NAV_SUBS and not self.channel_view:
            msg = self.t("msg_empty_subs")
            self.draw_text_centered(msg, SCREEN_WIDTH // 2, y + 90,
                                    self.C.TEXT_SECONDARY, self.font)
            self.draw_text_centered(self.t("msg_subs_hint"),
                                    SCREEN_WIDTH // 2, y + 125,
                                    self.C.TEXT_TERTIARY, self.font_small)
            if self.subs_loading:
                self.draw_spinner(SCREEN_WIDTH // 2, y + 180, radius=12, dot_size=3)
            return
        elif self.current_nav == NAV_HOME and not self.channel_view \
                and self.home_feed_failed:
            # v2.2: friendly "feed failed" state with retry instructions
            self.draw_text_centered(self.t("msg_feed_failed"),
                                    SCREEN_WIDTH // 2, y + 78,
                                    self.C.STATUS_ERROR, self.font_large)
            reason = self.home_fail_reason or ""
            if not self.wifi_connected:
                reason = self.t("msg_no_internet")
            reason = reason[:44]
            if reason:
                self.draw_text_centered(reason, SCREEN_WIDTH // 2, y + 120,
                                        self.C.TEXT_TERTIARY, self.font_small)
            self.draw_text_centered(self.t("msg_retry"), SCREEN_WIDTH // 2,
                                    y + 158, self.C.TEXT_SECONDARY, self.font)
            self.draw_text_centered(self.t("msg_exit_hint"),
                                    SCREEN_WIDTH // 2, y + 196,
                                    self.C.TEXT_TERTIARY, self.font_tiny)
            if self.is_loading or self.home_batch_loading:
                self.draw_spinner(SCREEN_WIDTH // 2, y + 240, radius=12,
                                  dot_size=3)
            return

        self.draw_text_centered(msg, SCREEN_WIDTH // 2, y + 100,
                                self.C.TEXT_SECONDARY, self.font)
        if not self.ytdlp_path:
            self.draw_text(self.t("msg_install_ytdlp"), 150, y + 140,
                           self.C.TEXT_TERTIARY, self.font_tiny)
        if not self.video_player:
            self.draw_text(self.t("msg_install_player"), 170, y + 160,
                           self.C.TEXT_TERTIARY, self.font_tiny)
        if self.current_nav == NAV_HOME and not self.channel_view and \
                (self.is_loading or self.home_batch_loading):
            self.draw_spinner(SCREEN_WIDTH // 2, y + 200, radius=12, dot_size=3)
            self.draw_text_centered(self.t("msg_loading_videos"),
                                    SCREEN_WIDTH // 2, y + 230,
                                    self.C.TEXT_TERTIARY, self.font_small)
        if self.channel_view and self.channel_loading:
            self.draw_spinner(SCREEN_WIDTH // 2, y + 200, radius=12, dot_size=3)
            self.draw_text_centered(self.t("msg_loading_videos"),
                                    SCREEN_WIDTH // 2, y + 230,
                                    self.C.TEXT_TERTIARY, self.font_small)

    # ------------------------------------------------------ category tiles
    def render_category_list(self, start_y, height):
        """v3.4: the Categories tab - a 2x5 grid of category tiles
        (SmartTube's 'Explore' layout, adapted to the 640x480 screen).
        Geometry: 10 tiles at 58px + 13px gaps = 342px, centred in the
        352px content area so the last row NEVER touches the help bar."""
        n = len(CATEGORY_DEFS)
        cols = 2
        tile_w = (SCREEN_WIDTH - 40 - 14) // cols     # 20px margins, 14 gap
        tile_h = 58
        gap = 13
        rows = (n + cols - 1) // cols
        grid_h = rows * tile_h + (rows - 1) * gap
        offset_y = start_y + max(0, (height - grid_h) // 2)
        visible_rows = max(1, (height + gap) // (tile_h + gap))
        # scroll by ROWS (self.selected is a flat tile index)
        sel_row = self.selected // cols
        scroll_row = self.scroll // cols
        if sel_row < scroll_row:
            self.scroll = sel_row * cols
        elif sel_row >= scroll_row + visible_rows:
            self.scroll = (sel_row - visible_rows + 1) * cols
        self.scroll = max(0, min(self.scroll,
                                 (rows - visible_rows) * cols if
                                 rows > visible_rows else 0))
        base_row = self.scroll // cols

        for i in range(n):
            row = i // cols
            col = i % cols
            x = 20 + col * (tile_w + 14)
            y = offset_y + (row - base_row) * (tile_h + gap)
            if y > start_y + height:
                break
            if y + tile_h < start_y:
                continue
            selected = (i == self.selected)
            key, icon, _src = CATEGORY_DEFS[i]
            count = ""
            if key == "favorites":
                count = str(len(self.favorites))
            label = self.category_title(key)
            if selected:
                self.draw_rect(x, y, tile_w, tile_h, self.C.CARD_SELECTED)
                self.draw_rect(x, y, 4, tile_h, self.C.YT_RED)
            else:
                self.draw_rect(x, y, tile_w, tile_h, self.C.CARD_BG)
            icon_color = self.C.YT_RED if selected else self.C.TEXT_TERTIARY
            self._draw_category_icon(x + 18, y + tile_h // 2 - 8, icon,
                                     icon_color)
            text_color = self.C.TEXT_PRIMARY if selected \
                else self.C.TEXT_SECONDARY
            self.draw_text(label[:18], x + 44, y + tile_h // 2 - 7,
                           text_color, self.font_small)
            if count:
                self.draw_text(count, x + tile_w - 26, y + tile_h // 2 - 7,
                               self.C.TEXT_TERTIARY, self.font_small)

    def _draw_category_icon(self, x, y, icon, color):
        """16x16 pixel icons for the category tiles (x,y = top-left)."""
        if icon == "cat_flame":
            self.draw_rect(x + 6, y, 3, 3, color)
            self.draw_rect(x + 4, y + 3, 7, 2, color)
            self.draw_rect(x + 3, y + 5, 9, 3, color)
            self.draw_rect(x + 2, y + 8, 11, 2, color)
            self.draw_rect(x + 4, y + 10, 7, 2, color)
            self.draw_rect(x + 6, y + 12, 3, 2, color)
        elif icon == "cat_note":
            self.draw_rect(x + 2, y + 10, 5, 5, color)
            self.draw_rect(x + 3, y + 5, 2, 6, color)
            self.draw_rect(x + 3, y + 4, 7, 2, color)
            self.draw_rect(x + 9, y + 5, 2, 6, color)
            self.draw_rect(x + 8, y + 11, 5, 4, color)
        elif icon == "cat_pad":
            self.draw_rect(x + 1, y + 4, 14, 7, color)
            self.draw_rect(x + 3, y + 1, 4, 4, color)
            self.draw_rect(x + 9, y + 1, 4, 4, color)
            self.draw_rect(x + 3, y + 6, 2, 2, (0, 0, 0))
            self.draw_rect(x + 11, y + 6, 2, 2, (0, 0, 0))
        elif icon == "cat_live":
            self.draw_rect(x + 5, y + 6, 6, 6, color)
            self.draw_rect(x + 7, y + 12, 2, 3, color)
            self.draw_rect(x + 1, y + 4, 2, 2, color)
            self.draw_rect(x + 13, y + 4, 2, 2, color)
            self.draw_rect(x + 2, y + 1, 2, 3, color)
            self.draw_rect(x + 12, y + 1, 2, 3, color)
        elif icon == "cat_film":
            self.draw_rect(x + 1, y + 2, 14, 12, color)
            for i in range(3):
                self.draw_rect(x + 3, y + 4 + i * 4, 4, 2, (0, 0, 0))
            self.draw_rect(x + 9, y + 4, 5, 8, (0, 0, 0))
        elif icon == "cat_news":
            self.draw_rect(x + 1, y + 3, 14, 10, color)
            self.draw_rect(x + 3, y + 5, 5, 3, (0, 0, 0))
            self.draw_rect(x + 9, y + 5, 4, 2, (0, 0, 0))
            self.draw_rect(x + 9, y + 8, 4, 1, (0, 0, 0))
            self.draw_rect(x + 3, y + 10, 10, 1, (0, 0, 0))
            self.draw_rect(x + 7, y, 2, 3, color)
        elif icon == "cat_ball":
            self.draw_rect(x + 4, y + 2, 8, 8, color)
            self.draw_rect(x + 2, y + 4, 12, 4, color)
            self.draw_rect(x + 4, y + 10, 8, 3, color)
            self.draw_rect(x + 6, y + 4, 4, 4, (0, 0, 0))
            self.draw_rect(x + 7, y + 9, 2, 2, color)
        elif icon == "cat_book":
            self.draw_rect(x + 1, y + 2, 6, 11, color)
            self.draw_rect(x + 9, y + 2, 6, 11, color)
            self.draw_rect(x + 7, y + 3, 2, 10, color)
            self.draw_rect(x + 2, y + 4, 4, 1, (0, 0, 0))
            self.draw_rect(x + 2, y + 7, 4, 1, (0, 0, 0))
            self.draw_rect(x + 10, y + 4, 4, 1, (0, 0, 0))
            self.draw_rect(x + 10, y + 7, 4, 1, (0, 0, 0))
        elif icon == "cat_mic":
            self.draw_rect(x + 5, y, 6, 8, color)
            self.draw_rect(x + 4, y + 3, 8, 4, color)
            self.draw_rect(x + 7, y + 8, 2, 4, color)
            self.draw_rect(x + 4, y + 11, 8, 2, color)
        elif icon == "cat_heart":
            self.draw_rect(x + 2, y + 2, 5, 4, color)
            self.draw_rect(x + 9, y + 2, 5, 4, color)
            self.draw_rect(x + 1, y + 4, 14, 4, color)
            self.draw_rect(x + 2, y + 8, 12, 3, color)
            self.draw_rect(x + 4, y + 11, 8, 2, color)
            self.draw_rect(x + 6, y + 13, 4, 2, color)

    # --------------------------------------------------------- video cards
    def render_video_list(self, videos, start_y, height):
        card_h = 80
        margin = 6
        thumb_w = 142
        thumb_h = 70

        base_visible = height // (card_h + margin)
        visible = base_visible

        if self.selected < self.scroll:
            self.scroll = self.selected
        elif self.selected >= self.scroll + visible:
            self.scroll = self.selected - visible + 1
        if self.scroll < 0:
            self.scroll = 0

        is_loading_more = (self.current_nav == NAV_HOME and self.home_batch_loading) or \
                          (self.current_nav == NAV_SEARCH and self.search_batch_loading)

        y = start_y
        for i in range(self.scroll, min(self.scroll + visible, len(videos))):
            video = videos[i]
            selected = i == self.selected

            if selected:
                self.draw_rect(10, y, SCREEN_WIDTH - 20, card_h, self.C.CARD_SELECTED)
                self.draw_rect(10, y, 4, card_h, self.C.YT_RED)
            else:
                self.draw_rect(10, y, SCREEN_WIDTH - 20, card_h, self.C.CARD_BG)

            # thumbnail + badges
            tx, ty = 18, y + 5
            self.draw_thumbnail(tx, ty, thumb_w, thumb_h, video.thumbnail)

            dur = video.format_duration()
            if dur:
                chip_w = len(dur) * 5 + 8
                self.draw_rect(tx + thumb_w - chip_w - 2, ty + thumb_h - 15,
                               chip_w, 13, (0, 0, 0), 190)
                self.draw_text(dur, tx + thumb_w - chip_w + 2, ty + thumb_h - 14,
                               self.C.TEXT_PRIMARY, self.font_tiny)
            if video.is_live:
                self.draw_rect(tx + 2, ty + thumb_h - 15, 30, 13,
                               self.C.BADGE_LIVE, 220)
                self.draw_text(self.t("time_live"), tx + 5, ty + thumb_h - 14,
                               (255, 255, 255), self.font_tiny)
            if self.current_nav == NAV_SUBS and self.subs.is_new(video.id):
                self.draw_rect(tx + 2, ty + 2, 30, 13, self.C.BADGE_NEW, 230)
                self.draw_text(self.t("badge_new"), tx + 6, ty + 3,
                               (0, 0, 0), self.font_tiny)
            is_fav = any(f.id == video.id for f in self.favorites)
            if is_fav:
                self.draw_rect(tx + thumb_w - 12, ty + 2, 10, 9, self.C.YT_RED, 220)
                self.draw_rect(tx + thumb_w - 10, ty + 4, 6, 2, (255, 255, 255))
                self.draw_rect(tx + thumb_w - 9, ty + 6, 2, 3, (255, 255, 255))

            # watch progress bar under thumbnail
            pos = self.get_position(video.id)
            if pos and pos[1]:
                try:
                    pct = max(0.0, min(1.0, pos[0] / float(pos[1])))
                except (TypeError, ValueError, ZeroDivisionError):
                    pct = 0.0
                if 0.02 < pct < 0.99:
                    self.draw_rect(tx, ty + thumb_h, thumb_w, 3, self.C.PROGRESS_BG)
                    self.draw_rect(tx, ty + thumb_h, int(thumb_w * pct), 3, self.C.YT_RED)

            # info
            info_x = tx + thumb_w + 14
            title = self.display_title(video)
            title = title[:32] + "..." if len(title) > 32 else title
            self.draw_text(title, info_x, y + 8,
                           self.C.TEXT_PRIMARY if selected else self.C.TEXT_SECONDARY,
                           self.font_small)
            channel = (video.channel or "")[:26]
            subbed = self.subs.is_subscribed(video.channel_id)
            if subbed and channel:
                channel = "* " + channel
            self.draw_text(channel[:27], info_x, y + 28, self.C.TEXT_TERTIARY,
                           self.font_tiny)
            meta = " - ".join([x for x in [video.format_views(),
                                           video.format_date()] if x])
            self.draw_text(meta[:34], info_x, y + 44, self.C.TEXT_TERTIARY,
                           self.font_tiny)
            y += card_h + margin

        # loading card at the end
        if is_loading_more and len(videos) >= self.scroll + visible - 1:
            displayed_count = min(len(videos) - self.scroll, visible)
            spinner_card_y = start_y + displayed_count * (card_h + margin)
            if spinner_card_y + card_h < start_y + height + 40:
                self.draw_rect(10, spinner_card_y, SCREEN_WIDTH - 20, card_h,
                               self.C.BG_SECONDARY)
                self.draw_spinner(SCREEN_WIDTH // 2, spinner_card_y + card_h // 2 - 5,
                                  radius=12, dot_size=3)
                self.draw_text_centered(self.t("msg_loading"),
                                        SCREEN_WIDTH // 2,
                                        spinner_card_y + card_h // 2 + 18,
                                        self.C.TEXT_TERTIARY, self.font_small)

        # scrollbar
        if len(videos) > base_visible:
            sb_h = height
            thumb = max(20, int(sb_h * visible / len(videos)))
            thumb_y = start_y + int((sb_h - thumb) * self.scroll /
                                    max(1, len(videos) - visible))
            self.draw_rect(SCREEN_WIDTH - 8, start_y, 4, sb_h, self.C.PROGRESS_BG)
            self.draw_rect(SCREEN_WIDTH - 8, thumb_y, 4, thumb, self.C.YT_RED)

    def render_settings(self, start_y, height):
        """v3.3 two-pane settings render. No scrolling, ever: 8 sections in
        the left column (36px each), up to 7 rows in the right column (42px
        each) - both fit the 352px content area of the 640x480 screen."""
        self.draw_text(self.t("settings_title"), 20, start_y + 8,
                       self.C.TEXT_PRIMARY, self.font_large)
        self.draw_text("r36swiki.com", SCREEN_WIDTH - 105, start_y + 12,
                       self.C.TEXT_PRIMARY, self.font_small)

        list_y = start_y + 42
        list_h = height - 48
        left_w = 188
        right_x = 212
        sec_h = 36
        row_h = 42

        sections = self.settings_sections or []

        # ---- left pane: section list ----
        for i in range(len(sections)):
            y = list_y + i * sec_h
            if y + sec_h > list_y + list_h:
                break
            skey, label, rows = sections[i]
            sel = (i == self.settings_section)
            focused = sel and self.settings_pane == "left" and \
                self.settings_picker is None
            if sel:
                self.draw_rect(14, y, left_w, sec_h - 4,
                               self.C.CARD_SELECTED if focused else self.C.CARD_BG)
                self.draw_rect(14, y, 4, sec_h - 4, self.C.YT_RED)
            else:
                self.draw_rect(14, y, left_w, sec_h - 4, self.C.CARD_BG)
            color = self.C.TEXT_PRIMARY if sel else self.C.TEXT_SECONDARY
            self.draw_text(label[:24], 30, y + 10, color, self.font_small)

        # pane divider
        self.draw_rect(left_w + 16, list_y, 1, list_h, self.C.DIVIDER)

        # ---- right pane: rows of the selected section ----
        rows = self._settings_rows()
        for j in range(len(rows)):
            y = list_y + j * row_h
            if y + row_h > list_y + list_h:
                break
            kind, label, key, options = rows[j]
            sel = (j == self.settings_row)
            focused = sel and self.settings_pane == "right" and \
                self.settings_picker is None
            w = SCREEN_WIDTH - right_x - 14
            self.draw_rect(right_x, y, w, row_h - 4,
                           self.C.CARD_SELECTED if sel else self.C.CARD_BG)
            if sel:
                self.draw_rect(right_x, y, 4, row_h - 4, self.C.YT_RED)
            label_color = self.C.TEXT_PRIMARY if sel else self.C.TEXT_SECONDARY
            self.draw_text(label[:30], right_x + 14, y + 6, label_color,
                           self.font_small)
            if kind == "choice":
                val = self._setting_value_display(key, options)
                vtxt = "< %s >" % val
                self.draw_text(vtxt[:22], SCREEN_WIDTH - 178, y + 22,
                               self.C.TEXT_PRIMARY if sel else self.C.TEXT_TERTIARY,
                               self.font_small)
            elif kind == "action":
                atxt = self.t("settings_edit") if key == "proxy" \
                    else self.t("settings_execute")
                self.draw_text(atxt, SCREEN_WIDTH - 178, y + 22, self.C.YT_RED,
                               self.font_small)
            elif kind == "info":
                if key in ("account_name", "account_none"):
                    self.draw_text("YouTube", SCREEN_WIDTH - 178, y + 22,
                                   self.C.TEXT_TERTIARY, self.font_small)
                else:
                    self.draw_text(self._setting_value_display(key, options),
                                   SCREEN_WIDTH - 178, y + 22,
                                   self.C.TEXT_TERTIARY, self.font_small)

        # ---- value picker overlay ----
        if self.settings_picker is not None:
            self._render_settings_picker()

    def _render_settings_picker(self):
        """Modal value picker (SmartTube-style): a box listing the options."""
        p = self.settings_picker
        options = p.get("options") or []
        n = len(options)
        if n == 0:
            return
        box_w = 300
        row_h = 34
        # 76px of chrome: 44px header gap + 32px for the hint line (the
        # hint must never overlap the last option - VLM-caught layout bug)
        box_h = 76 + n * row_h
        box_x = (SCREEN_WIDTH - box_w) // 2
        box_y = max(56, (SCREEN_HEIGHT - box_h) // 2 - 20)
        # scrim + box
        self.draw_rect(0, 0, SCREEN_WIDTH, SCREEN_HEIGHT, (0, 0, 0), 150)
        self.draw_rect(box_x, box_y, box_w, box_h, self.C.CARD_BG)
        self.draw_rect(box_x, box_y, box_w, 34, self.C.YT_RED)
        title = (p.get("label") or self.t("settings_pick"))[:26]
        self.draw_text(title, box_x + 12, box_y + 9, self.C.TEXT_PRIMARY,
                       self.font_small)
        for i, opt in enumerate(options):
            y = box_y + 44 + i * row_h
            sel = (i == p.get("selected", 0))
            if sel:
                self.draw_rect(box_x + 8, y, box_w - 16, row_h - 4,
                               self.C.CARD_SELECTED)
                self.draw_rect(box_x + 8, y, 3, row_h - 4, self.C.YT_RED)
            # v3.4: translate RAW On/Off values ONCE, at render time (the
            # old double-translation made both options read "Desligado")
            opt_text = opt
            if opt == "On":
                opt_text = self.t("settings_on")
            elif opt == "Off":
                opt_text = self.t("settings_off")
            self.draw_text(str(opt_text)[:24], box_x + 24, y + 8,
                           self.C.TEXT_PRIMARY if sel else self.C.TEXT_SECONDARY,
                           self.font_small)
        self.draw_text(self.t("settings_pick_hint"),
                       box_x + 12, box_y + box_h - 26,
                       self.C.TEXT_TERTIARY, self.font_tiny)

    # =====================================================================
    # KEYBOARD + SUGGESTIONS
    # =====================================================================
    def render_keyboard(self):
        kb_y = SCREEN_HEIGHT - 260
        self.draw_rect(0, kb_y - 45, SCREEN_WIDTH, SCREEN_HEIGHT - kb_y + 45,
                       (0, 0, 0), 240)

        input_y = kb_y - 38
        self.draw_rect(15, input_y, SCREEN_WIDTH - 30, 32, self.C.BG_TERTIARY)
        self.draw_rect(15, input_y, SCREEN_WIDTH - 30, 2, self.C.YT_RED)

        if self.keyboard_mode == "proxy":
            placeholder = self.t("kb_proxy_placeholder")
        else:
            placeholder = self.t("kb_search_placeholder")
        query = self.search_query or placeholder
        color = self.C.TEXT_PRIMARY if self.search_query else self.C.TEXT_TERTIARY

        display_query = query[:35]
        text_width = self.draw_text(display_query, 25, input_y + 7, color, self.font)

        if self.search_query and (self.frame_count // 15) % 2:
            cursor_x = 25 + text_width + 2
            self.draw_rect(cursor_x, input_y + 5, 2, 20, self.C.YT_RED)

        if self.sugg_visible and self.sugg_items:
            self.render_suggestions(input_y + 38, kb_y - input_y - 40)
            return

        key_w, key_h, gap = 52, 34, 4
        offsets = [15, 15, 35, 55]

        layout = self.symbol_layout if self.sym_page else self.keyboard_layout.copy()
        if self.caps_lock and not self.sym_page:
            layout = [layout[0]] + [[c.upper() for c in row] for row in layout[1:4]]

        for row_i, row in enumerate(layout):
            for col_i, char in enumerate(row):
                x = offsets[row_i] + col_i * (key_w + gap)
                y = kb_y + row_i * (key_h + gap)
                selected = self.keyboard_row == row_i and self.keyboard_col == col_i
                self.draw_rect(x, y, key_w, key_h,
                               self.C.YT_RED if selected else self.C.BG_TERTIARY)
                self.draw_text(char, x + key_w // 2 - 5, y + 7,
                               self.C.TEXT_PRIMARY, self.font)

        ctrl_y = kb_y + 4 * (key_h + gap)
        if self.sym_page:
            first_label = self.t("kb_abc")
        else:
            first_label = self.t("kb_sym")
        # v3.6: control row = [SYM/ABC, SPACE, backspace, SUG, GO].
        # SUG opens the suggestion panel ON DEMAND - suggestions no longer
        # pop up (and steal the dpad) while the user is typing.
        ctrls = [(first_label, 55), (self.t("kb_space"), 160), ("<-", 55),
                 (self.t("kb_sug"), 66), (self.t("kb_go"), 76)]
        ctrl_x = 15
        for i, (label, w) in enumerate(ctrls):
            selected = self.keyboard_row == 4 and self.keyboard_col == i
            bg = self.C.YT_RED if (selected or i == 4) else self.C.BG_TERTIARY
            if i == 3 and not selected:
                bg = (60, 60, 60)
            self.draw_rect(ctrl_x, ctrl_y, w, key_h, bg)
            self.draw_text(label, ctrl_x + w // 2 - len(label) * 4, ctrl_y + 7,
                           self.C.TEXT_PRIMARY, self.font_small)
            ctrl_x += w + gap

        self.draw_text(self.t("help_keyboard"), 140, ctrl_y + key_h + 8,
                       self.C.TEXT_TERTIARY, self.font_tiny)

    def render_suggestions(self, panel_y, panel_h):
        """Overlay panel with live suggestions or recent searches."""
        panel_h = max(panel_h, 110)
        self.draw_rect(15, panel_y, SCREEN_WIDTH - 30, panel_h,
                       (0, 0, 0), 250)
        self.draw_rect(15, panel_y, SCREEN_WIDTH - 30, 2, self.C.YT_RED)

        if self.sugg_loading:
            title = self.t("msg_loading")
        elif not self.search_query and self.search_history:
            title = self.t("sugg_hist")
        else:
            title = self.t("sugg_title")
        self.draw_text(title, 25, panel_y + 6, self.C.TEXT_TERTIARY, self.font_tiny)

        item_h = 24
        max_items = max(1, (panel_h - 34) // item_h)
        items = self.sugg_items[:max_items]
        for i, s in enumerate(items):
            y = panel_y + 26 + i * item_h
            selected = i == self.sugg_selected
            if selected:
                self.draw_rect(20, y - 2, SCREEN_WIDTH - 40, item_h, self.C.CARD_SELECTED)
                self.draw_rect(20, y - 2, 3, item_h, self.C.YT_RED)
            label = s[:44]
            self.draw_text(label, 30, y + 2,
                           self.C.TEXT_PRIMARY if selected else self.C.TEXT_SECONDARY,
                           self.font_small)

    def render_context_menu(self):
        n = len(self.ctx_items)
        if not n:
            return
        item_h = 32
        panel_w = 380
        panel_h = 46 + n * item_h
        px = (SCREEN_WIDTH - panel_w) // 2
        py = max(60, (SCREEN_HEIGHT - panel_h) // 2 - 20)

        # dim background
        self.draw_rect(0, 0, SCREEN_WIDTH, SCREEN_HEIGHT, (0, 0, 0), 160)
        self.draw_rect(px, py, panel_w, panel_h, self.C.BG_SECONDARY, 252)
        self.draw_rect(px, py, panel_w, 26, self.C.YT_RED, 252)
        self.draw_text(self.t("ctx_title"), px + 12, py + 6,
                       (255, 255, 255), self.font_small)

        for i, (label, action) in enumerate(self.ctx_items):
            y = py + 32 + i * item_h
            selected = i == self.ctx_selected
            if selected:
                self.draw_rect(px + 6, y, panel_w - 12, item_h - 2,
                               self.C.CARD_SELECTED)
                self.draw_rect(px + 6, y, 3, item_h - 2, self.C.YT_RED)
            self.draw_text(label[:36], px + 18, y + 7,
                           self.C.TEXT_PRIMARY if selected else self.C.TEXT_SECONDARY,
                           self.font_small)

    def render_video_info(self):
        v = self.info_video
        if not v:
            return
        self.draw_rect(0, 0, SCREEN_WIDTH, SCREEN_HEIGHT, (0, 0, 0), 200)
        panel_w, panel_h = 440, 240
        px = (SCREEN_WIDTH - panel_w) // 2
        py = (SCREEN_HEIGHT - panel_h) // 2
        self.draw_rect(px, py, panel_w, panel_h, self.C.BG_SECONDARY, 252)
        self.draw_rect(px, py, panel_w, 3, self.C.YT_RED, 252)

        title = self.display_title(v)
        line1 = title[:42]
        line2 = title[42:84]
        self.draw_text(line1, px + 16, py + 16, self.C.TEXT_PRIMARY, self.font)
        if line2:
            self.draw_text(line2 + "...", px + 16, py + 40, self.C.TEXT_PRIMARY,
                           self.font)

        rows = []
        rows.append((self.t("ctx_channel"), v.channel or "-"))
        rows.append(("Duration", v.format_duration() or "-"))
        rows.append(("Views", v.format_views() or "-"))
        rows.append(("Date", v.format_date() or v.upload_date or "-"))
        if self.info_ryd:
            rows.append(("Likes/Dislikes", self.info_ryd))
        pos = self.get_position(v.id)
        if pos:
            rows.append(("Position", "%s / %s" % (fmt_clock(pos[0]),
                                                  fmt_clock(pos[1]))))
        if v.is_live:
            rows.append(("Status", self.t("time_live")))
        y = py + 74
        for k, val in rows:
            self.draw_text(k, px + 16, y, self.C.TEXT_TERTIARY, self.font_small)
            self.draw_text(str(val)[:36], px + 160, y, self.C.TEXT_SECONDARY,
                           self.font_small)
            y += 22

    def render_wizard(self):
        self.draw_rect(0, 0, SCREEN_WIDTH, SCREEN_HEIGHT, self.C.BG_PRIMARY)
        # v2.2: WiFi indicator in the top-left corner, also during setup
        self.draw_wifi_icon(10, 8)
        # logo
        self.draw_logo(SCREEN_WIDTH // 2 - 20, 50, 40, 28)

        step_key = WIZARD_STEPS[min(self.wizard_step, len(WIZARD_STEPS) - 1)]
        if step_key == "language":
            title = self.t("wiz_welcome")
            subtitle = self.t("wiz_welcome_sub")
            question = self.t("wiz_language")
        elif step_key == "device":
            title = self.t("wiz_welcome")
            subtitle = self.t("wiz_welcome_sub")
            question = self.t("wiz_device")
        elif step_key == "quality":
            question = self.t("wiz_quality")
            title = subtitle = ""
        elif step_key == "hwdec":
            question = self.t("wiz_hwdec")
            title = subtitle = ""
        elif step_key == "sponsorblock":
            question = self.t("wiz_sb")
            title = subtitle = ""
        else:
            title = self.t("wiz_done")
            subtitle = self.t("wiz_done_sub")
            question = ""

        if title:
            self.draw_text_centered(title, SCREEN_WIDTH // 2, 110,
                                    self.C.TEXT_PRIMARY, self.font_large)
        if subtitle:
            self.draw_text_centered(subtitle, SCREEN_WIDTH // 2, 142,
                                    self.C.TEXT_SECONDARY, self.font_small)
        if question:
            self.draw_text_centered(question, SCREEN_WIDTH // 2, 190,
                                    self.C.TEXT_PRIMARY, self.font_large)

        # step indicator
        indicator = "%d / %d" % (self.wizard_step + 1, len(WIZARD_STEPS))
        self.draw_text(indicator, SCREEN_WIDTH - 70, 50, self.C.TEXT_TERTIARY,
                       self.font_tiny)

        opts = self.wizard_options(self.wizard_step)
        y = 240
        item_h = 38
        gap = 6
        if len(opts) >= 5:
            # v2.2 layout fix: the 6-language list used to overflow the
            # 480px screen and collide with the bottom hint - compact it
            item_h = 30
            gap = 5
            y = 232
        for i, opt in enumerate(opts):
            selected = i == self.wizard_choice
            bx = SCREEN_WIDTH // 2 - 160
            if selected:
                self.draw_rect(bx, y, 320, item_h, self.C.CARD_SELECTED)
                self.draw_rect(bx, y, 4, item_h, self.C.YT_RED)
            else:
                self.draw_rect(bx, y, 320, item_h, self.C.CARD_BG)
            self.draw_text_centered(opt, SCREEN_WIDTH // 2,
                                    y + (11 if item_h >= 38 else 8),
                                    self.C.TEXT_PRIMARY if selected
                                    else self.C.TEXT_SECONDARY, self.font_small)
            y += item_h + gap

        self.draw_text_centered(self.t("wiz_hint"), SCREEN_WIDTH // 2,
                                SCREEN_HEIGHT - 34, self.C.TEXT_TERTIARY,
                                self.font_tiny)
