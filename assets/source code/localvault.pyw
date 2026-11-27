# LocalVault - a fully local, offline password manager.
# Copyright (C) 2026  deathcipher
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU Affero General Public License as published
# by the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU Affero General Public License for more details.
#
# You should have received a copy of the GNU Affero General Public License
# along with this program.  If not, see <https://www.gnu.org/licenses/>.

"""LocalVault - a fully local, offline password manager.

Vault file: AES-256-GCM, key derived from the master password with scrypt.
Nothing is ever sent over the network.

Known limitation: Python cannot wipe secrets from RAM. "Locked" means inaccessible
through the UI, not zeroed in memory; a memory dump of the running process could
expose the key or decrypted entries.

Other known limits:
- Rollback: someone who can write to the vault file can swap in an older valid copy
  (or the .bak) without the password. A single file with no outside state can't detect it.
- Clipboard: the app wipes what it copied after 20 s and on lock, but OS clipboard history
  (e.g. Windows Win+V) and cloud clipboards may keep a copy. Turn them off for best results.
- Changing the master password deletes the .bak, which is still protected by the old one.

Tabs: every entry belongs to a tab (School, Private, Work, or your own). The tab list is
stored inside the encrypted vault together with the entries.
"""

import base64
import csv
import gc
import io
import json
import math
import os
import random
import secrets
import string
import sys
import tempfile
import threading
import time
import unicodedata
import uuid
import zlib  # noqa: F401  (kept for parity with earlier builds)
import tkinter as tk
from pathlib import Path
from urllib.parse import urlparse
from tkinter import filedialog, font as tkfont

from cryptography.exceptions import InvalidTag
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from cryptography.hazmat.primitives.kdf.scrypt import Scrypt
from zxcvbn import zxcvbn

APP_VERSION = "1.0.0"
COPYRIGHT = "Copyright (C) 2026  deathcipher"
SOURCE_URL = "https://github.com/deathcipher/Local-Vault"   # TODO: confirm this is your repo URL
LICENSE_URL = "https://www.gnu.org/licenses/agpl-3.0.html"
NOTICE = ("This program comes with ABSOLUTELY NO WARRANTY. It is free software, and you are "
          "welcome to redistribute it under the terms of the GNU Affero General Public License, "
          "version 3 or (at your option) any later version.")

VAULT_PATH = Path(os.environ.get("LOCALVAULT_PATH") or Path.home() / ".localvault" / "vault.json")
AAD_V1 = b"localvault-v1"
FORMAT_VERSION = 2
SCRYPT_N = 131072
SCRYPT_N_MAX = 262144
AUTO_LOCK_SECONDS = 300
CLIPBOARD_CLEAR_SECONDS = 20
MIN_MASTER_LEN = 12
MIN_ZXCVBN_SCORE = 4
MOTION = os.environ.get("LOCALVAULT_REDUCE_MOTION", "").lower() not in ("1", "true", "yes")

DEFAULT_TABS = ["Private", "Work", "School"]
TAB_ALL = "\0all"        # pseudo-tab: every entry
TAB_NONE = "\0none"      # pseudo-tab: entries without a tab
MAX_TAB_LEN = 24

b64e = lambda b: base64.b64encode(b).decode()
b64d = lambda s: base64.b64decode(s)


class WrongPassword(Exception):
    pass


class CorruptVault(Exception):
    pass


class VaultLocked(RuntimeError):
    pass


def check_master(pw):
    if len(pw) < MIN_MASTER_LEN:
        return f"Use at least {MIN_MASTER_LEN} characters."
    try:
        r = zxcvbn(pw[:72])
        if r["score"] < MIN_ZXCVBN_SCORE:
            fb = r["feedback"]
            tips = " ".join(filter(None, [fb.get("warning")] + fb.get("suggestions", [])))
            return "Too easy to guess. " + (tips or "Try a longer passphrase of unrelated words.")
        return None
    except ValueError:
        return "Couldn't evaluate that password's strength. Try a different one."


# --------------------------------------------------------------------------- vault


def clean_tabs(tabs, entries):
    """Unique, trimmed tab names; any tab used by an entry is guaranteed to exist."""
    out, seen = [], set()
    for t in list(tabs) + [e.get("category", "") for e in entries]:
        t = str(t or "").strip()[:MAX_TAB_LEN]
        if t and t.lower() not in seen:
            seen.add(t.lower())
            out.append(t)
    return out


class Vault:
    def __init__(self, path):
        self.path, self.entries, self._key, self._kdf = Path(path), [], None, None
        self.tabs = list(DEFAULT_TABS)

    @property
    def bak_path(self):
        return self.path.with_name(self.path.name + ".bak")

    def exists(self):
        return self.path.exists()

    @staticmethod
    def _aad(version, kdf):
        if version == 1:
            return AAD_V1
        return b"localvault|" + json.dumps({"v": version, "kdf": kdf}, sort_keys=True).encode()

    @staticmethod
    def _derive(password, kdf):
        n = kdf["n"]
        if kdf["r"] != 8 or kdf["p"] != 1 or not (16384 <= n <= SCRYPT_N_MAX) or (n & (n - 1)):
            raise CorruptVault()
        s = Scrypt(salt=b64d(kdf["salt"]), length=32, n=n, r=kdf["r"], p=kdf["p"])
        return s.derive(password.encode())

    @staticmethod
    def _norm(password):
        return unicodedata.normalize("NFKC", password)

    def _new_kdf(self):
        return {"n": SCRYPT_N, "r": 8, "p": 1, "salt": b64e(secrets.token_bytes(16))}

    def create(self, password):
        self._kdf = self._new_kdf()
        self._key = self._derive(self._norm(password), self._kdf)
        self.entries, self.tabs = [], list(DEFAULT_TABS)
        self.save()

    def _load_plain(self, plain):
        data = json.loads(plain)
        legacy = isinstance(data, list)          # older builds stored a bare list of entries
        entries = data if legacy else data.get("entries", [])
        tabs = list(DEFAULT_TABS) if legacy else data.get("tabs", list(DEFAULT_TABS))
        if not isinstance(entries, list) or not isinstance(tabs, list):
            raise CorruptVault()
        for e in entries:
            e.setdefault("category", "")
        self.entries = entries
        self.tabs = clean_tabs(tabs, entries)
        return legacy

    def unlock(self, password, upgrade=True):
        data = json.loads(self.path.read_text())
        v, kdf = data["v"], data["kdf"]
        if v not in (1, FORMAT_VERSION):
            raise CorruptVault()
        nonce, ct = b64d(data["nonce"]), b64d(data["ct"])
        aad = self._aad(v, kdf)
        norm = self._norm(password)
        forms = list(dict.fromkeys([norm, password,
                                    unicodedata.normalize("NFC", password),
                                    unicodedata.normalize("NFD", password)]))
        for form in forms:
            key = self._derive(form, kdf)
            try:
                plain = AESGCM(key).decrypt(nonce, ct, aad)
                break
            except InvalidTag:
                continue
        else:
            raise WrongPassword()
        self._kdf, self._key = kdf, key
        try:
            legacy = self._load_plain(plain)
        except (ValueError, TypeError, AttributeError):
            self._kdf = self._key = None
            raise CorruptVault()
        if upgrade and (v < FORMAT_VERSION or kdf["n"] < SCRYPT_N or form != norm or legacy):
            try:
                self._kdf = self._new_kdf()
                self._key = self._derive(norm, self._kdf)
                self.save()
            except OSError:
                self._kdf, self._key = kdf, key   # keep working with the old key

    @staticmethod
    def _sync_dir(path):
        if os.name == "nt":
            return
        fd = None
        try:
            fd = os.open(path, os.O_RDONLY)
            os.fsync(fd)
        except OSError:
            pass
        finally:
            if fd is not None:
                os.close(fd)

    def save(self):
        if self._key is None:
            raise VaultLocked("vault is locked")
        nonce = secrets.token_bytes(12)
        plain = json.dumps({"entries": self.entries, "tabs": self.tabs}).encode()
        ct = AESGCM(self._key).encrypt(nonce, plain, self._aad(FORMAT_VERSION, self._kdf))
        blob = json.dumps({"v": FORMAT_VERSION, "kdf": self._kdf,
                           "nonce": b64e(nonce), "ct": b64e(ct)})
        parent = self.path.parent
        if not parent.exists():
            parent.mkdir(parents=True, exist_ok=True, mode=0o700)
        try:
            os.chmod(parent, 0o700)
        except OSError:
            pass
        fd, tmp = tempfile.mkstemp(dir=parent)
        try:
            with os.fdopen(fd, "w") as f:
                f.write(blob)
                f.flush()
                os.fsync(f.fileno())
            if self.path.exists():
                fdb = os.open(self.bak_path, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
                with os.fdopen(fdb, "wb") as f:
                    f.write(self.path.read_bytes())
                    f.flush()
                    os.fsync(f.fileno())
            os.replace(tmp, self.path)
            self._sync_dir(parent)
        except BaseException:
            try:
                os.unlink(tmp)
            except OSError:
                pass
            raise

    def change_master(self, new_password):
        if self._key is None:
            raise VaultLocked("vault is locked")
        old = (self._kdf, self._key)
        try:
            self._kdf = self._new_kdf()
            self._key = self._derive(self._norm(new_password), self._kdf)
            self.save()
            try:
                self.bak_path.unlink()
            except OSError:
                pass
        except BaseException:
            self._kdf, self._key = old
            raise

    def lock(self):
        self._key = None
        self.entries = []
        self.tabs = list(DEFAULT_TABS)


# --------------------------------------------------------------------------- helpers


def generate_password(length=20, symbols=True):
    pools = [string.ascii_lowercase, string.ascii_uppercase, string.digits]
    if symbols:
        pools.append("!@#$%^&*()-_=+[]{}?")
    chars = [secrets.choice(p) for p in pools]
    alphabet = "".join(pools)
    chars += [secrets.choice(alphabet) for _ in range(max(length, len(pools)) - len(chars))]
    secrets.SystemRandom().shuffle(chars)
    return "".join(chars)


MAX_IMPORT_BYTES = 10 * 1024 * 1024
MAX_IMPORT_ROWS = 20000
CSV_ALIASES = {
    "title": ("name", "title", "account", "account name", "item", "entry"),
    "url": ("url", "login_uri", "website", "web site", "uri", "web address", "login url"),
    "username": ("username", "login_username", "user name", "user", "login", "login name",
                 "email", "e-mail"),
    "password": ("password", "login_password", "pass"),
    "notes": ("notes", "note", "extra", "comments", "comment"),
    "category": ("category", "tab", "folder", "group", "grouping"),
}


class ImportProblem(ValueError):
    pass


def write_private(path, data):
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
    with os.fdopen(fd, "wb") as f:
        f.write(data)


def write_csv(path, entries):
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_TRUNC, 0o600)
    with os.fdopen(fd, "w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow(("name", "url", "username", "password", "note", "category"))
        for e in entries:
            w.writerow((e.get("title", ""), e.get("url", ""), e.get("username", ""),
                        e.get("password", ""), e.get("notes", ""), e.get("category", "")))


def parse_csv(raw):
    try:
        text = raw.decode("utf-8-sig")
        reader = csv.DictReader(io.StringIO(text, newline=""))
        rows = list(reader)
        if len(rows) > MAX_IMPORT_ROWS:
            raise ImportProblem(f"That file has too many rows (limit {MAX_IMPORT_ROWS}).")
        header = {}
        for col in reader.fieldnames or []:
            if col is None:
                continue
            key = col.strip().lower()
            for field, names in CSV_ALIASES.items():
                if key in names and field not in header:
                    header[field] = col
        if "password" not in header:
            raise ImportProblem("Couldn't find a password column in that CSV.")
        out = []
        for r in rows:
            e = {f: (r.get(header[f]) or "").strip() for f in
                 ("title", "username", "url", "password", "notes", "category") if f in header}
            for f in ("title", "username", "url", "password", "notes", "category"):
                e.setdefault(f, "")
            if not (e["password"] or e["username"] or e["title"]):
                continue
            if not e["title"]:
                u = e["url"]
                host = urlparse(u if "//" in u else "//" + u).hostname if u else None
                e["title"] = host or e["username"] or "Untitled"
            out.append(e)
        if not out:
            raise ImportProblem("No entries found in that file.")
        return out
    except UnicodeDecodeError:
        raise ImportProblem("That doesn't look like a UTF-8 CSV file.")
    except csv.Error:
        raise ImportProblem("Couldn't read that CSV (a field may be malformed or too long).")


def analyze_import(path):
    if os.path.getsize(path) > MAX_IMPORT_BYTES:
        raise ImportProblem("That file is too large to import (limit 10 MB).")
    with open(path, "rb") as f:
        raw = f.read()
    if raw.lstrip()[:1] == b"{":
        try:
            d = json.loads(raw)
        except ValueError:
            raise ImportProblem("That file looks like JSON but couldn't be read.")
        if isinstance(d, dict) and {"kdf", "nonce", "ct"} <= set(d.keys()):
            return "backup", path
        raise ImportProblem("Only CSV files and LocalVault backups can be imported.")
    return "csv", parse_csv(raw)


def entry_key(e):
    return (e.get("title", "").lower(), e.get("username", "").lower(),
            e.get("url", "").lower(), e.get("password", ""))


def merge_plan(existing, incoming, skip_dupes=True):
    seen = {entry_key(e) for e in existing}
    now = time.strftime("%Y-%m-%d %H:%M")
    out = []
    for e in incoming:
        k = entry_key(e)
        if skip_dupes and k in seen:
            continue
        seen.add(k)
        n = {f: str(e.get(f, "")) for f in ("title", "username", "url", "password", "notes", "category")}
        n.update(id=uuid.uuid4().hex, updated=now)
        out.append(n)
    return out


def read_license_file():
    """Return the bundled LICENSE text if it sits next to the program, else None."""
    bases = [getattr(sys, "_MEIPASS", None), os.path.dirname(os.path.abspath(__file__))]
    for base in bases:
        if not base:
            continue
        for name in ("LICENSE", "LICENSE.txt", "COPYING"):
            try:
                return (Path(base) / name).read_text(encoding="utf-8")
            except OSError:
                continue
    return None


# --------------------------------------------------------------------------- look & feel

C = dict(bg="#0f1012", panel="#15171a", raised="#1d2025", field="#111316", line="#272a30",
         sel="#20242a", hover="#1a1d21", text="#ece9e2", muted="#8d919a", faint="#5c606a",
         accent="#e3a83c", accent_hi="#f0bd5c", accent_ink="#1a1405", ok="#6fc08f",
         warn="#e0a43a", bad="#e5645a")
SCORES = [("Very weak", "bad"), ("Weak", "bad"), ("Fair", "warn"), ("Strong", "ok"), ("Excellent", "ok")]
AVATARS = ["#c0705a", "#b08a45", "#6f9a66", "#5b9596", "#6c83b3", "#9677b2", "#b46c8c", "#848a94"]
F = {}


def init_fonts(root):
    have = set(tkfont.families(root))
    pick = lambda names, d: next((n for n in names if n in have), d)
    sans = pick(("Inter", "SF Pro Text", "Segoe UI Variable Text", "Segoe UI", "Helvetica Neue",
                 "Cantarell", "Noto Sans", "DejaVu Sans"), "Helvetica")
    mono = pick(("JetBrains Mono", "Cascadia Mono", "SF Mono", "Menlo", "Consolas",
                 "DejaVu Sans Mono"), "Courier")
    mk = lambda fam, size, w="normal": tkfont.Font(root=root, family=fam, size=size, weight=w)
    F.update(body=mk(sans, 11), small=mk(sans, 9), cap=mk(sans, 8, "bold"), bold=mk(sans, 11, "bold"),
             h1=mk(sans, 20, "bold"), h2=mk(sans, 15, "bold"), brand=mk(sans, 13, "bold"),
             avatar=mk(sans, 12, "bold"), mono=mk(mono, 11),
             title=mk(sans, 28, "bold"), lead=mk(sans, 13), dialnum=mk(sans, 12))


def _rgb(h):
    h = h.lstrip("#")
    return tuple(int(h[i:i + 2], 16) for i in (0, 2, 4))


def lerp(a, b, t):
    t = max(0.0, min(1.0, t))
    return "#%02x%02x%02x" % tuple(round(x + (y - x) * t) for x, y in zip(_rgb(a), _rgb(b)))


def ease(t):
    return 1 - (1 - t) ** 3


def animate(widget, ms, step, done=None):
    """Run step(t) for t in 0..1 over ms milliseconds."""
    if not MOTION:
        step(1.0)
        done and done()
        return
    t0 = time.monotonic()

    def tick():
        try:
            t = min(1.0, (time.monotonic() - t0) * 1000 / ms)
            step(ease(t))
            if t < 1.0:
                widget.after(16, tick)
            elif done:
                done()
        except tk.TclError:
            pass
    tick()


def rrect(cv, x1, y1, x2, y2, r, **kw):
    pts = [x1 + r, y1, x2 - r, y1, x2, y1, x2, y1 + r, x2, y2 - r, x2, y2, x2 - r, y2,
           x1 + r, y2, x1, y2, x1, y2 - r, x1, y1 + r, x1, y1]
    return cv.create_polygon(pts, smooth=True, **kw)


def draw_avatar(cv, cx, cy, r, title):
    col = AVATARS[zlib.crc32((title or "?").lower().encode()) % len(AVATARS)]
    cv.create_oval(cx - r, cy - r, cx + r, cy + r, fill=col, outline="")
    cv.create_text(cx, cy, text=(title or "?")[:1].upper(), font=F["avatar"], fill="#14110c")


def fit(text, font, width):
    if font.measure(text) <= width:
        return text
    while text and font.measure(text + "…") > width:
        text = text[:-1]
    return text + "…"


def label(parent, text, font="body", color="text", **kw):
    return tk.Label(parent, text=text, font=F[font], fg=C[color], bg=kw.pop("bg", parent.cget("bg")),
                    bd=0, **kw)


KINDS = {
    "primary": dict(bg=C["accent"], hov=C["accent_hi"], fg=C["accent_ink"], bd=None),
    "ghost": dict(bg=C["raised"], hov=C["sel"], fg=C["text"], bd=C["line"]),
    "quiet": dict(bg=C["panel"], hov=C["hover"], fg=C["muted"], bd=None),
    "danger": dict(bg=C["raised"], hov="#2a1c1c", fg=C["bad"], bd="#4a2a28"),
    "danger_fill": dict(bg=C["bad"], hov="#ee7a70", fg="#1a0a08", bd=None),
}


class Btn(tk.Canvas):
    def __init__(self, master, text, command=None, kind="ghost", padx=16, pady=8, font=None):
        super().__init__(master, bg=master.cget("bg"), highlightthickness=0, bd=0, cursor="hand2")
        self.k, self.cmd, self.text, self.h = KINDS[kind], command, text, 0.0
        self.font = font or F["bold"]
        self.px, self.py = padx, pady
        self._size()
        self.bind("<Enter>", lambda e: self._to(1.0))
        self.bind("<Leave>", lambda e: self._to(0.0))
        self.bind("<ButtonRelease-1>", self._release)
        self.bind("<Configure>", lambda e: self.draw())

    def _size(self):
        w = self.font.measure(self.text) + 2 * self.px
        h = self.font.metrics("linespace") + 2 * self.py
        self.configure(width=w, height=h)

    def configure(self, cnf=None, **kw):
        if "text" in kw:
            self.text = kw.pop("text")
            self._size()
            self.draw()
        if cnf or kw:
            super().configure(cnf, **kw)

    def _to(self, target):
        start = self.h
        animate(self, 120, lambda t: self._set(start + (target - start) * t))

    def _set(self, v):
        self.h = v
        self.draw()

    def _release(self, e):
        if 0 <= e.x <= self.winfo_width() and 0 <= e.y <= self.winfo_height() and self.cmd:
            self.cmd()

    def draw(self):
        self.delete("all")
        w, h = self.winfo_width() or int(self["width"]), self.winfo_height() or int(self["height"])
        k = self.k
        fill = lerp(k["bg"], k["hov"], self.h)
        rrect(self, 1, 1, w - 1, h - 1, 7, fill=fill, outline=k["bd"] or fill)
        self.create_text(w / 2, h / 2, text=self.text, font=self.font, fill=k["fg"])


class Field(tk.Frame):
    def __init__(self, master, secret=False, width=30, font=None, placeholder="", on_change=None):
        super().__init__(master, bg=C["field"], highlightthickness=1, highlightbackground=C["line"],
                         highlightcolor=C["accent"])
        self.var, self.secret, self.placeholder, self.on_change = tk.StringVar(), secret, placeholder, on_change
        self.e = tk.Entry(self, textvariable=self.var, width=width, font=font or F["body"], bd=0,
                          bg=C["field"], fg=C["text"], insertbackground=C["accent"],
                          highlightthickness=0, show="•" if secret else "", relief="flat")
        self.e.pack(side="left", fill="x", expand=True, padx=(10, 6), pady=8)
        if secret:
            self.eye = tk.Label(self, text="SHOW", font=F["cap"], fg=C["faint"], bg=C["field"], cursor="hand2")
            self.eye.pack(side="right", padx=(0, 10))
            self.eye.bind("<Button-1>", lambda e: self.reveal())
        self.ph = tk.Label(self, text=placeholder, font=F["body"], fg=C["faint"], bg=C["field"], bd=0)
        self.ph.bind("<Button-1>", lambda e: self.e.focus_set())
        self.var.trace_add("write", self._changed)
        self._placeholder()

    def reveal(self):
        shown = self.e.cget("show") == ""
        self.e.configure(show="•" if shown else "")
        self.eye.configure(text="SHOW" if shown else "HIDE")

    def _placeholder(self):
        if self.placeholder and not self.var.get():
            self.ph.place(x=10, rely=0.5, anchor="w")
        else:
            self.ph.place_forget()

    def _changed(self, *_):
        self._placeholder()
        if self.on_change:
            self.on_change()

    def get(self):
        return self.var.get()

    def set(self, v):
        self.var.set(v)

    def focus(self):
        self.e.focus_set()

    def on_return(self, fn):
        self.e.bind("<Return>", lambda e: fn())


class Meter(tk.Frame):
    def __init__(self, master):
        super().__init__(master, bg=master.cget("bg"))
        self.segs = []
        for _ in range(5):
            s = tk.Frame(self, bg=C["line"], height=4)
            s.pack(side="left", fill="x", expand=True, padx=(0, 4))
            self.segs.append(s)
        self.lbl = tk.Label(self, text="", font=F["small"], fg=C["faint"], bg=master.cget("bg"), width=10, anchor="e")
        self.lbl.pack(side="right")

    def update_for(self, pw):
        if not pw:
            for s in self.segs:
                s.configure(bg=C["line"])
            self.lbl.configure(text="")
            return
        try:
            score = zxcvbn(pw[:72])["score"]
        except ValueError:
            score = 0
        name, col = SCORES[score]
        for i, s in enumerate(self.segs):
            s.configure(bg=C[col] if i <= score else C["line"])
        self.lbl.configure(text=name, fg=C[col])


class Dial(tk.Canvas):
    """Combination-lock dial: a bezel with 96 notches and a number every 8, fixed marker on top,
    keyhole in the middle. The bezel always turns clockwise: it drifts slowly at a constant speed while idle
    (typing does not affect it), and spins up while the vault is being opened."""

    UNITS = 96
    STEP = 360 / UNITS
    IDLE_DPS = 14.0        # idle drift, degrees per second (clockwise)
    BUSY_DPS = 360.0       # extra speed while busy
    FRAME_MS = 20

    def __init__(self, master, size=360):
        super().__init__(master, width=size, height=size, bg=C["panel"], highlightthickness=0)
        self.size, self.rot, self.busy = size, 0.0, False
        self._pending = 0.0                 # degrees still to be turned by turn()
        self._tau = 0.05                    # easing time constant for turn()
        self._speed = 0.0                   # current extra speed (deg/s), eased toward its target
        self._last = time.monotonic()
        self._build()
        self._place()
        self._tick()

    def _build(self):
        c = self.size / 2
        R = c - 14                                  # outer edge of the ticks
        self._c, self._R = c, R
        # fixed parts: inner disc and keyhole
        r_in = R * 0.60
        self.create_oval(c - r_in, c - r_in, c + r_in, c + r_in, fill=C["raised"], outline=C["line"])
        self.create_oval(c - 14, c - 24, c + 14, c + 4, fill=C["accent"], outline="")
        self.create_polygon(c - 6, c, c + 6, c, c + 12, c + 28, c - 12, c + 28, fill=C["accent"], outline="")
        # turning bezel (items are created once and moved every frame)
        self._ticks, self._nums = [], []
        for u in range(self.UNITS):
            if u % 8 == 0:
                ln, col, w = 20, C["muted"], 2
            elif u % 4 == 0:
                ln, col, w = 12, C["faint"], 1
            else:
                ln, col, w = 6, C["line"], 1
            self._ticks.append((self.create_line(0, 0, 0, 0, fill=col, width=w), u, ln))
            if u % 8 == 0:
                self._nums.append((self.create_text(0, 0, text=f"{u:02d}", font=F["dialnum"],
                                                    fill=lerp(C["faint"], C["muted"], 0.45)), u))
        # fixed marker
        self.create_polygon(c - 9, c - R - 13, c + 9, c - R - 13, c, c - R + 1, fill=C["accent"], outline="")

    def _place(self):
        c, R = self._c, self._R
        base = self.rot - 80 * self.STEP            # value 80 sits at the top at rest
        for item, u, ln in self._ticks:
            a = math.radians(u * self.STEP + base)  # increasing angle = clockwise on screen
            sa, ca = math.sin(a), math.cos(a)
            self.coords(item, c + R * sa, c - R * ca, c + (R - ln) * sa, c - (R - ln) * ca)
        rr = R - 38
        for item, u in self._nums:
            a = math.radians(u * self.STEP + base)
            self.coords(item, c + rr * math.sin(a), c - rr * math.cos(a))

    def _tick(self):
        try:
            now = time.monotonic()
            dt = min(now - self._last, 0.1)
            self._last = now
            if MOTION:
                target = self.BUSY_DPS if self.busy else 0.0
                self._speed += (target - self._speed) * (1 - math.exp(-dt / 0.25))
                move = (self.IDLE_DPS + self._speed) * dt
                if self._pending > 0.01:
                    take = self._pending * (1 - math.exp(-dt / self._tau))
                    self._pending -= take
                    move += take
                self.rot = (self.rot + move) % 360
                self._place()
            self.after(self.FRAME_MS, self._tick)
        except tk.TclError:
            pass                                    # widget was destroyed; stop animating

    def turn(self, degrees, ms=120):
        """Turn the bezel clockwise by `degrees`."""
        if not MOTION:
            self.rot = (self.rot + degrees) % 360
            self._place()
            return
        self._tau = max(ms, 1) / 2500
        self._pending += degrees

    def set_busy(self, on):
        """Spin up (or settle back to the idle drift)."""
        self.busy = bool(on)
        if not MOTION:
            self.turn(360 + 10 * self.STEP) if on else None

    def spin(self, ms=900):
        self.set_busy(True)
        try:
            self.after(ms, lambda: self.set_busy(False))
        except tk.TclError:
            pass


ROW = 60


class EntryList(tk.Canvas):
    def __init__(self, master, on_select):
        super().__init__(master, bg=C["panel"], highlightthickness=0, bd=0)
        self.items, self.sel, self.hov, self.on_select, self.top = [], None, None, on_select, 0
        self.bind("<Configure>", lambda e: self.redraw())
        self.bind("<Motion>", self._hover)
        self.bind("<Leave>", lambda e: self._hover(None))
        self.bind("<Button-1>", self._click)
        self.bind("<MouseWheel>", self._scroll)
        self.bind("<Button-4>", lambda e: self._scroll(e, 1))
        self.bind("<Button-5>", lambda e: self._scroll(e, -1))

    def _scroll(self, e, d=None):
        d = d if d is not None else (1 if e.delta > 0 else -1)
        max_top = max(0, len(self.items) * ROW - self.winfo_height())
        self.top = max(0, min(max_top, self.top - d * 40))
        self.redraw()

    def _index(self, e):
        i = int((e.y + self.top) // ROW)
        return i if 0 <= i < len(self.items) else None

    def _hover(self, e):
        i = self._index(e) if e else None
        if i != self.hov:
            self.hov = i
            self.redraw()

    def _click(self, e):
        i = self._index(e)
        if i is not None:
            self.on_select(self.items[i]["id"])

    def set_items(self, items, sel=None):
        self.items, self.sel = items, sel
        max_top = max(0, len(items) * ROW - self.winfo_height())
        self.top = min(self.top, max_top)
        self.redraw()

    def redraw(self):
        self.delete("all")
        w = self.winfo_width()
        if not self.items:
            self.create_text(w / 2, 60, text="Nothing here yet", font=F["small"], fill=C["faint"])
            return
        for i, e in enumerate(self.items):
            y = i * ROW - self.top
            if y > self.winfo_height() or y + ROW < 0:
                continue
            sel = e["id"] == self.sel
            bg = C["sel"] if sel else C["hover"] if i == self.hov else C["panel"]
            self.create_rectangle(0, y, w, y + ROW, fill=bg, outline="")
            if sel:
                self.create_rectangle(0, y + 8, 3, y + ROW - 8, fill=C["accent"], outline="")
            draw_avatar(self, 34, y + ROW / 2, 15, e.get("title", ""))
            self.create_text(62, y + 21, anchor="w", font=F["bold"], fill=C["text"],
                             text=fit(e.get("title", ""), F["bold"], w - 78))
            sub = e.get("username") or e.get("url") or "—"
            self.create_text(62, y + 40, anchor="w", font=F["small"], fill=C["muted"],
                             text=fit(sub, F["small"], w - 78))


class TabStrip(tk.Canvas):
    """Pill-shaped tab bar. Wheel scrolls sideways; right-click / double-click edits a tab."""

    def __init__(self, master, on_pick, on_edit, on_add):
        super().__init__(master, bg=C["panel"], height=38, highlightthickness=0, bd=0)
        self.tabs, self.active, self.pills, self.off = [], TAB_ALL, [], 0
        self.on_pick, self.on_edit, self.on_add = on_pick, on_edit, on_add
        self.bind("<Configure>", lambda e: self.draw())
        self.bind("<Button-1>", self._click)
        self.bind("<Double-Button-1>", self._edit)
        self.bind("<Button-3>", self._edit)
        self.bind("<Button-2>", self._edit)
        self.bind("<MouseWheel>", lambda e: self._scroll(1 if e.delta > 0 else -1))
        self.bind("<Button-4>", lambda e: self._scroll(1))
        self.bind("<Button-5>", lambda e: self._scroll(-1))

    def set_tabs(self, tabs, active):
        moved = active != self.active
        self.tabs, self.active = tabs, active
        self.draw(reveal=moved)

    def _view_w(self):
        return max(60, self.winfo_width() - 52)

    def _scroll(self, d):
        total = self.pills[-1][2] + self.off + 14 if self.pills else 0
        self.off = max(0, min(max(0, total - self._view_w()), self.off - d * 50))
        self.draw()

    def draw(self, reveal=False):
        self.delete("all")
        self.pills = []
        W, vw = self.winfo_width(), self._view_w()
        x = 12
        for key, text, count in self.tabs:
            shown = text if count is None else f"{text} {count}"
            w = F["small"].measure(shown) + 18
            self.pills.append((key, x, x + w))
            x += w + 4
        total = x + 8
        if reveal:                       # keep the active tab in view
            for key, a, b in self.pills:
                if key == self.active:
                    if b - self.off > vw:
                        self.off = b - vw + 10
                    if a - self.off < 14:
                        self.off = max(0, a - 14)
        self.off = max(0, min(self.off, max(0, total - vw)))
        for (key, a, b), (_, text, count) in zip(self.pills, self.tabs):
            shown = text if count is None else f"{text} {count}"
            on = key == self.active
            x1, x2 = a - self.off, b - self.off
            rrect(self, x1, 6, x2, 32, 12, fill=C["accent"] if on else C["raised"],
                  outline=C["accent"] if on else C["line"])
            self.create_text((x1 + x2) / 2, 19, text=shown, font=F["small"],
                             fill=C["accent_ink"] if on else C["muted"])
        # fixed "+" button on the right, drawn over anything that scrolls underneath it
        self.create_rectangle(W - 50, 0, W, 38, fill=C["panel"], outline="")
        rrect(self, W - 42, 6, W - 14, 32, 12, fill=C["panel"], outline=C["line"])
        self.create_text(W - 28, 18, text="+", font=F["bold"], fill=C["muted"])
        if self.off > 0:
            self.create_text(5, 18, text="‹", font=F["bold"], fill=C["faint"])
        if total - self.off > vw:
            self.create_text(W - 56, 18, text="›", font=F["bold"], fill=C["faint"])

    def _hit(self, e):
        if e.x >= self.winfo_width() - 46:
            return "+"
        if e.x >= self._view_w():
            return None
        for key, a, b in self.pills:
            if a - self.off <= e.x <= b - self.off:
                return key
        return None

    def _click(self, e):
        key = self._hit(e)
        if key == "+":
            self.on_add()
        elif key is not None:
            self.on_pick(key)

    def _edit(self, e):
        key = self._hit(e)
        if key not in (None, "+", TAB_ALL, TAB_NONE):
            self.on_edit(key)


class Modal(tk.Toplevel):
    def __init__(self, app, title):
        super().__init__(app)
        self.app = app
        self.configure(bg=C["panel"])
        self.title(title)
        self.transient(app)
        self.resizable(False, False)
        self.withdraw()
        self.body = tk.Frame(self, bg=C["panel"], padx=30, pady=26)
        self.body.pack(fill="both", expand=True)
        self.protocol("WM_DELETE_WINDOW", self.close)
        self.bind("<Escape>", lambda e: self.close())
        app._modal = self

    def present(self):
        self.update_idletasks()
        a = self.app
        x = a.winfo_rootx() + (a.winfo_width() - self.winfo_reqwidth()) // 2
        y = a.winfo_rooty() + (a.winfo_height() - self.winfo_reqheight()) // 3
        self.geometry(f"+{max(0, x)}+{max(0, y)}")
        self.deiconify()
        try:
            self.wait_visibility()
            self.grab_set()
            self.focus_set()
        except tk.TclError:
            pass

    def close(self):
        try:
            self.grab_release()
        except tk.TclError:
            pass
        if self.app._modal is self:
            self.app._modal = None
        self.destroy()


# --------------------------------------------------------------------------- app


class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("LocalVault")
        self.configure(bg=C["bg"])
        try:
            base = getattr(sys, "_MEIPASS", os.path.dirname(os.path.abspath(__file__)))
            self.iconbitmap(os.path.join(base, "localvault.ico"))
        except Exception:
            pass
        w, h = 1060, 720
        self.geometry(f"{w}x{h}+{max(0, (self.winfo_screenwidth() - w) // 2)}+"
                      f"{max(0, (self.winfo_screenheight() - h) // 3)}")
        self.minsize(940, 680)
        init_fonts(self)
        self.vault = Vault(VAULT_PATH)
        self.mod, self.modname = ("Command", "⌘") if sys.platform == "darwin" else ("Control", "Ctrl")
        self.current_id = self.editing_id = None
        self.mode, self.tab = "locked", TAB_ALL
        self._copied = self._wipe_job = self._toast_job = self._modal = None
        self.status_lock = None
        self.last_activity = time.monotonic()
        for ev in ("<Key>", "<Motion>", "<Button>", "<MouseWheel>"):
            self.bind_all(ev, self._touch, add="+")
        for k, fn in (("n", self.new_entry), ("f", self.focus_search), ("l", self.lock), ("s", self.save_edit)):
            self.bind_all(f"<{self.mod}-{k}>", lambda e, fn=fn: self._shortcut(fn))
        self.bind_all("<Escape>", self.on_escape)
        self.protocol("WM_DELETE_WINDOW", self.on_close)
        self.after(1000, self.tick)
        self.show_unlock()

    # ----- plumbing
    def _touch(self, e=None):
        self.last_activity = time.monotonic()

    def clear(self):
        for c in self.winfo_children():
            if not isinstance(c, tk.Toplevel):
                c.destroy()

    def _shortcut(self, fn):
        if self.vault._key is not None and self._modal is None:
            fn()
        return "break"

    def tick(self):
        if self.vault._key is not None:
            left = AUTO_LOCK_SECONDS - (time.monotonic() - self.last_activity)
            if left <= 0:
                self.lock()
            elif self.status_lock is not None:
                try:
                    self.status_lock.configure(
                        text=f"Auto-lock in {int(left // 60)}:{int(left % 60):02d}",
                        fg=C["warn"] if left < 30 else C["faint"])
                except tk.TclError:
                    pass
        self.after(1000, self.tick)

    def on_close(self):
        self.wipe_clipboard()
        self.vault.lock()
        self.destroy()

    def lock(self):
        if self._modal:
            self._modal.close()
        self.wipe_clipboard()
        self.vault.lock()
        self.current_id = self.editing_id = None
        self.tab = TAB_ALL
        self.mode = "locked"
        self.show_unlock()
        gc.collect()

    def persist(self):
        try:
            self.vault.save()
            return True
        except VaultLocked:
            self.alert("Vault locked", "The vault was locked, so your change was not saved.")
        except OSError:
            self.alert("Save failed", "Couldn't write the vault file (disk full, or no permission?). "
                                      "Your change was not saved.")
        return False

    def copy(self, text, what):
        self.clipboard_clear()
        self.clipboard_append(text)
        self._copied = text
        if self._wipe_job:
            self.after_cancel(self._wipe_job)
        self._wipe_job = self.after(CLIPBOARD_CLEAR_SECONDS * 1000, self.wipe_clipboard)
        self.toast(f"{what} copied  ·  clears in {CLIPBOARD_CLEAR_SECONDS}s")

    def wipe_clipboard(self):
        if self._wipe_job:
            self.after_cancel(self._wipe_job)
            self._wipe_job = None
        if self._copied is not None:
            try:
                if self.clipboard_get() == self._copied:
                    self.clipboard_clear()
                    self.clipboard_append("")
            except tk.TclError:
                pass
            self._copied = None

    def toast(self, msg):
        lbl = getattr(self, "toast_lbl", None)
        if lbl is None:
            return
        try:
            lbl.configure(text=f"  {msg}  ")
            lbl.place(relx=1.0, rely=1.0, x=-24, y=-52, anchor="se")
            lbl.lift()
            if self._toast_job:
                self.after_cancel(self._toast_job)
            self._toast_job = self.after(2200, lbl.place_forget)
        except tk.TclError:
            pass

    def shake(self, widget):
        # The widget is centred with relx=0.5, so its x offset is relative to that
        # anchor (normally 0). Using winfo_x() here pushed the form far to the right.
        try:
            x0 = int(float(widget.place_info().get("x", 0) or 0))
        except (tk.TclError, ValueError):
            x0 = 0
        seq = [8, -8, 6, -6, 3, -3, 0]

        def step(i=0):
            try:
                if i < len(seq):
                    widget.place_configure(x=x0 + seq[i])
                    self.after(30, lambda: step(i + 1))
                else:
                    widget.place_configure(x=x0)
            except tk.TclError:
                pass
        step()

    def alert(self, title, msg):
        m = Modal(self, title)
        label(m.body, title, "h2").pack(anchor="w")
        label(m.body, msg, "body", "muted", wraplength=340, justify="left").pack(anchor="w", pady=(8, 18))
        Btn(m.body, "OK", m.close, "primary", padx=24).pack(anchor="e")
        m.present()

    def confirm(self, title, msg, yes, ok="OK", danger=False):
        m = Modal(self, title)
        label(m.body, title, "h2").pack(anchor="w")
        label(m.body, msg, "body", "muted", wraplength=340, justify="left").pack(anchor="w", pady=(8, 18))
        row = tk.Frame(m.body, bg=C["panel"])
        row.pack(anchor="e")
        Btn(row, "Cancel", m.close, "ghost").pack(side="left", padx=(0, 8))
        Btn(row, ok, lambda: (m.close(), yes()), "danger_fill" if danger else "primary").pack(side="left")
        m.present()

    def about_dialog(self):
        if self._modal:
            return
        m = Modal(self, "About LocalVault")
        label(m.body, "LocalVault", "h2").pack(anchor="w")
        label(m.body, f"Version {APP_VERSION}", "small", "faint").pack(anchor="w", pady=(2, 12))
        label(m.body, COPYRIGHT, "body").pack(anchor="w")
        label(m.body, NOTICE, "small", "muted", wraplength=380, justify="left").pack(anchor="w", pady=(8, 14))

        def url_row(caption, url):
            label(m.body, caption, "cap", "faint").pack(anchor="w", pady=(0, 4))
            e = tk.Entry(m.body, font=F["small"], bd=0, bg=C["field"], fg=C["text"],
                         readonlybackground=C["field"], highlightthickness=1,
                         highlightbackground=C["line"], highlightcolor=C["accent"])
            e.insert(0, url)
            e.configure(state="readonly")
            e.pack(fill="x", ipady=6, pady=(0, 12))

        url_row("SOURCE CODE", SOURCE_URL)
        url_row("LICENSE", LICENSE_URL)
        row = tk.Frame(m.body, bg=C["panel"])
        row.pack(anchor="e", pady=(2, 0))
        Btn(row, "View license", lambda: (m.close(), self.license_dialog()), "ghost").pack(side="left", padx=(0, 8))
        Btn(row, "Close", m.close, "primary", padx=24).pack(side="left")
        m.present()

    def license_dialog(self):
        m = Modal(self, "License")
        label(m.body, "GNU Affero General Public License v3", "h2").pack(anchor="w", pady=(0, 10))
        text = read_license_file()
        frame = tk.Frame(m.body, bg=C["field"], highlightthickness=1, highlightbackground=C["line"])
        frame.pack(fill="both", expand=True)
        box = tk.Text(frame, width=80, height=22, wrap="word", bd=0, padx=12, pady=10, font=F["mono"],
                      bg=C["field"], fg=C["text"], insertbackground=C["text"], highlightthickness=0)
        bar = tk.Scrollbar(frame, command=box.yview)
        box.configure(yscrollcommand=bar.set)
        bar.pack(side="right", fill="y")
        box.pack(side="left", fill="both", expand=True)
        box.insert("1.0", text if text else
                   NOTICE + "\n\nThe full license text is available at:\n" + LICENSE_URL +
                   "\n\nThe source code is available at:\n" + SOURCE_URL + "\n")
        box.configure(state="disabled")
        Btn(m.body, "Close", m.close, "primary", padx=24).pack(anchor="e", pady=(12, 0))
        m.present()

    # ----- unlock
    def show_unlock(self):
        self.clear()
        self.status_lock = None
        new = not self.vault.exists()
        left = tk.Frame(self, bg=C["panel"], width=450)
        left.pack(side="left", fill="y")
        left.pack_propagate(False)
        tk.Frame(self, bg=C["line"], width=1).pack(side="left", fill="y")
        right = tk.Frame(self, bg=C["bg"])
        right.pack(side="left", fill="both", expand=True)
        self.dial = Dial(left, 360)
        self.dial.place(relx=0.5, rely=0.4, anchor="center")
        label(left, "LocalVault", "title").place(relx=0.5, rely=0.73, anchor="center")
        label(left, "Your passwords. Your machine. Nothing else.", "lead", "muted").place(relx=0.5, rely=0.795, anchor="center")
        label(left, "AES-256-GCM   ·   scrypt   ·   zero network access", "small", "faint").place(relx=0.5, rely=0.94, anchor="center")

        form = tk.Frame(right, bg=C["bg"])
        form.place(relx=0.5, rely=0.5, anchor="center")
        label(form, "NEW VAULT" if new else "LOCKED", "cap", "accent").pack(anchor="w")
        label(form, "Set a master password" if new else "Welcome back", "h1").pack(anchor="w", pady=(6, 4))
        label(form, "It encrypts everything in your vault and can't be recovered if forgotten." if new
              else "Enter your master password to open the vault.", "body", "muted",
              wraplength=340, justify="left").pack(anchor="w", pady=(0, 22))
        meter = Meter(form) if new else None
        pw = Field(form, secret=True, width=34, on_change=(lambda: meter.update_for(pw.get())) if new else None)
        label(form, "MASTER PASSWORD", "cap", "faint").pack(anchor="w", pady=(0, 6))
        pw.pack(fill="x")
        conf = None
        if new:
            meter.pack(fill="x", pady=(8, 0))
            label(form, "CONFIRM", "cap", "faint").pack(anchor="w", pady=(14, 6))
            conf = Field(form, secret=True, width=34)
            conf.pack(fill="x")
        err = label(form, " ", "small", "bad", wraplength=340, justify="left", anchor="w")
        err.pack(fill="x", pady=(12, 12))

        def fail(msg):
            err.configure(text=msg)
            self.shake(form)

        working = [False]

        def finish(exc):
            if exc is None:
                self.after(600 if MOTION else 0, self.show_main_start)    # keep spinning a moment
                return
            working[0] = False
            self.dial.set_busy(False)
            if isinstance(exc, WrongPassword):
                fail("Wrong password.")
            elif isinstance(exc, CorruptVault):
                fail("The vault file is damaged or in an unknown format.")
            elif isinstance(exc, OSError):
                fail("Couldn't read or write the vault file.")
            elif isinstance(exc, (ValueError, KeyError, TypeError)):
                fail("The vault file is damaged.")
            else:
                raise exc

        def go():
            if working[0]:
                return
            p = pw.get()
            if new:
                msg = check_master(p)
                if msg:
                    return fail(msg)
                if p != conf.get():
                    return fail("The two passwords don't match.")
                err.configure(text="Creating…")
                work = lambda: self.vault.create(p)
            else:
                err.configure(text="Unlocking…")
                work = lambda: self.vault.unlock(p, upgrade=True)
            working[0] = True
            self.dial.set_busy(True)                  # dial spins while the key is being derived
            box = {}

            def run():
                try:
                    work()
                except Exception as e:                # handed back to the UI thread below
                    box["exc"] = e
                box["done"] = True
            threading.Thread(target=run, daemon=True).start()

            def poll():
                try:
                    if box.get("done"):
                        finish(box.get("exc"))
                    else:
                        self.after(30, poll)
                except tk.TclError:
                    pass
            poll()

        Btn(form, "Create vault" if new else "Unlock", go, "primary", pady=11).pack(fill="x")
        label(form, "Offline by design. Nothing here ever leaves this computer.", "small", "faint").pack(anchor="w", pady=(18, 0))
        about = label(form, "About  ·  Free software (AGPL-3.0)", "small", "faint", cursor="hand2")
        about.pack(anchor="w", pady=(6, 0))
        about.bind("<Button-1>", lambda e: self.about_dialog())
        about.bind("<Enter>", lambda e: about.configure(fg=C["accent"]))
        about.bind("<Leave>", lambda e: about.configure(fg=C["faint"]))
        pw.on_return(go)
        if conf:
            conf.on_return(go)
        pw.focus()

    def show_main_start(self):
        self.last_activity = time.monotonic()
        self.tab = TAB_ALL
        self.show_main()

    # ----- tabs
    def tab_counts(self):
        counts = {}
        for e in self.vault.entries:
            k = e.get("category", "")
            counts[k] = counts.get(k, 0) + 1
        return counts

    def tab_label(self, key):
        return {TAB_ALL: "All", TAB_NONE: "Unsorted"}.get(key, key)

    def refresh_tabs(self):
        counts = self.tab_counts()
        tabs = [(TAB_ALL, "All", len(self.vault.entries))]
        tabs += [(t, t, counts.get(t, 0)) for t in self.vault.tabs]
        if counts.get("", 0):
            tabs.append((TAB_NONE, "Unsorted", counts[""]))
        if self.tab not in [t[0] for t in tabs]:
            self.tab = TAB_ALL
        self.tabstrip.set_tabs(tabs, self.tab)

    def pick_tab(self, key):
        self.tab = key
        self.refresh()
        if self.mode == "edit":
            return
        cur = self.current()
        if cur is not None and not self.in_tab(cur):
            self.current_id = None
            self.show_empty()

    def in_tab(self, e):
        return self.tab == TAB_ALL or (self.tab == TAB_NONE and not e.get("category")) \
            or e.get("category") == self.tab

    def tab_dialog(self, old=None):
        m = Modal(self, "Rename tab" if old else "New tab")
        label(m.body, "Rename tab" if old else "New tab", "h2").pack(anchor="w", pady=(0, 4))
        label(m.body, "Tabs sort your logins, like School, Private or Work." if not old else
              "Entries in this tab move along with the new name.", "body", "muted",
              wraplength=320, justify="left").pack(anchor="w", pady=(0, 14))
        label(m.body, "NAME", "cap", "faint").pack(anchor="w", pady=(0, 6))
        f = Field(m.body, width=30)
        f.pack(fill="x")
        if old:
            f.set(old)
        err = label(m.body, " ", "small", "bad", wraplength=320, justify="left", anchor="w")
        err.pack(fill="x", pady=(10, 0))
        row = tk.Frame(m.body, bg=C["panel"])
        row.pack(fill="x", pady=(12, 0))

        def save():
            name = f.get().strip()
            if not name:
                return err.configure(text="Give the tab a name.")
            if len(name) > MAX_TAB_LEN:
                return err.configure(text=f"Keep it under {MAX_TAB_LEN} characters.")
            if name.lower() in ("all", "unsorted") or any(
                    t.lower() == name.lower() and t != old for t in self.vault.tabs):
                return err.configure(text="You already have a tab with that name.")
            if old:
                self.vault.tabs[self.vault.tabs.index(old)] = name
                for e in self.vault.entries:
                    if e.get("category") == old:
                        e["category"] = name
                if self.tab == old:
                    self.tab = name
            else:
                self.vault.tabs.append(name)
                self.tab = name
            m.close()
            if self.persist():
                self.refresh()
                if self.mode == "view":
                    self.show_view()

        def delete():
            n = self.tab_counts().get(old, 0)
            m.close()

            def do():
                self.vault.tabs.remove(old)
                for e in self.vault.entries:
                    if e.get("category") == old:
                        e["category"] = ""
                if self.tab == old:
                    self.tab = TAB_ALL
                if self.persist():
                    self.refresh()
                    if self.mode == "view":
                        self.show_view()
            self.confirm("Delete this tab?",
                         f"“{old}” will be removed. Its {n} entr{'y' if n == 1 else 'ies'} will not be deleted; "
                         "they move to Unsorted.", do, "Delete tab", True)

        if old:
            Btn(row, "Delete tab", delete, "danger").pack(side="left")
        Btn(row, "Save" if old else "Add tab", save, "primary").pack(side="right")
        Btn(row, "Cancel", m.close, "ghost").pack(side="right", padx=(0, 8))
        f.on_return(save)
        m.present()
        f.focus()

    # ----- main screen
    def show_main(self):
        self.clear()
        status = tk.Frame(self, bg=C["panel"], height=30)
        status.pack(side="bottom", fill="x")
        status.pack_propagate(False)
        tk.Frame(self, bg=C["line"], height=1).pack(side="bottom", fill="x")
        body = tk.Frame(self, bg=C["bg"])
        body.pack(fill="both", expand=True)
        side = tk.Frame(body, bg=C["panel"], width=340)
        side.pack(side="left", fill="y")
        side.pack_propagate(False)
        tk.Frame(body, bg=C["line"], width=1).pack(side="left", fill="y")
        self.detail = tk.Frame(body, bg=C["bg"])
        self.detail.pack(side="left", fill="both", expand=True)
        self.toast_lbl = tk.Label(self, bg=C["raised"], fg=C["text"], font=F["small"], padx=10, pady=8,
                                  highlightthickness=1, highlightbackground=C["line"])

        dot = tk.Canvas(status, width=10, height=10, bg=C["panel"], highlightthickness=0)
        dot.create_oval(1, 1, 9, 9, fill=C["ok"], outline="")
        dot.pack(side="left", padx=(16, 7))
        label(status, "Unlocked", "small", "muted").pack(side="left")
        self.status_lock = label(status, "", "small", "faint")
        self.status_lock.pack(side="left", padx=(14, 0))
        label(status, str(self.vault.path).replace(str(Path.home()), "~") + "   ·   AES-256-GCM",
              "small", "faint").pack(side="right", padx=16)

        head = tk.Frame(side, bg=C["panel"])
        head.pack(fill="x", padx=18, pady=(18, 12))
        logo = tk.Canvas(head, width=22, height=22, bg=C["panel"], highlightthickness=0)
        logo.create_oval(2, 2, 20, 20, outline=C["accent"], width=2)
        logo.create_oval(8, 8, 14, 14, fill=C["accent"], outline="")
        logo.pack(side="left")
        label(head, "LocalVault", "brand").pack(side="left", padx=(10, 0))
        self.count = label(head, "", "small", "faint")
        self.count.pack(side="right")

        bar = tk.Frame(side, bg=C["panel"])
        bar.pack(fill="x", padx=18, pady=(0, 10))
        Btn(bar, "+", self.new_entry, "primary", padx=14, pady=7).pack(side="right", padx=(8, 0))
        self.search = Field(bar, placeholder="Search entries", width=20, on_change=self.refresh)
        self.search.pack(side="left", fill="x", expand=True)

        self.tabstrip = TabStrip(side, self.pick_tab, lambda k: self.tab_dialog(k), lambda: self.tab_dialog())
        self.tabstrip.pack(fill="x", pady=(0, 6))
        tk.Frame(side, bg=C["line"], height=1).pack(fill="x")

        foot = tk.Frame(side, bg=C["panel"])
        foot.pack(side="bottom", fill="x", padx=18, pady=12)
        tk.Frame(side, bg=C["line"], height=1).pack(side="bottom", fill="x")
        r1 = tk.Frame(foot, bg=C["panel"])
        r1.pack(fill="x", pady=(0, 8))
        Btn(r1, "Import", self.import_dialog, "ghost").pack(side="left", fill="x", expand=True, padx=(0, 4))
        Btn(r1, "Export", self.export_dialog, "ghost").pack(side="left", fill="x", expand=True, padx=(4, 0))
        r2 = tk.Frame(foot, bg=C["panel"])
        r2.pack(fill="x")
        Btn(r2, "Lock", self.lock, "ghost").pack(side="left")
        Btn(r2, "About", self.about_dialog, "quiet").pack(side="left", padx=(6, 0))
        Btn(r2, "Master password", self.change_master_dialog, "quiet").pack(side="right")

        self.list = EntryList(side, self.select)
        self.list.pack(fill="both", expand=True)
        self.mode = "empty"
        self.refresh()
        self.show_empty()

    def current(self):
        return next((e for e in self.vault.entries if e["id"] == self.current_id), None)

    def refresh(self):
        self.refresh_tabs()
        q = self.search.get().strip().lower()
        items = [e for e in self.vault.entries if self.in_tab(e) and (not q or any(
            q in e.get(f, "").lower() for f in ("title", "username", "url")))]
        items = sorted(items, key=lambda e: e.get("title", "").lower())
        self.list.set_items(items, self.current_id)
        n = len(items)
        self.count.configure(text=f"{n} item{'s' if n != 1 else ''}")

    def select(self, eid):
        if self.mode == "edit":
            self.cancel_edit()
        self.current_id = eid
        self.refresh()
        self.show_view()

    def clear_detail(self):
        for c in self.detail.winfo_children():
            c.destroy()

    def focus_search(self):
        self.search.focus()

    def on_escape(self, e=None):
        if self._modal:
            return self._modal.close()
        if self.vault._key is None:
            return
        if self.mode == "edit":
            self.cancel_edit()
        elif self.search.get():
            self.search.set("")

    def stage(self):
        self.clear_detail()
        f = tk.Frame(self.detail, bg=C["bg"], padx=44, pady=36)
        f.pack(fill="both", expand=True)
        return f

    def show_empty(self):
        self.mode = "empty"
        s = self.stage()
        box = tk.Frame(s, bg=C["bg"])
        box.place(relx=0.5, rely=0.42, anchor="center")
        n = len(self.vault.entries)
        label(box, "Select an entry" if n else "Your vault is empty", "h2").pack()
        label(box, f"or press {self.modname}+N to add a new login." if n else
              f"Add your first login with + or {self.modname}+N, or import a CSV.", "body", "muted").pack(pady=(8, 0))

    def show_view(self):
        e = self.current()
        if not e:
            return self.show_empty()
        self.mode = "view"
        s = self.stage()
        top = tk.Frame(s, bg=C["bg"])
        top.pack(fill="x")
        av = tk.Canvas(top, width=48, height=48, bg=C["bg"], highlightthickness=0)
        draw_avatar(av, 24, 24, 22, e.get("title", ""))
        av.pack(side="left")
        label(top, e.get("title", ""), "h1").pack(side="left", padx=14)
        Btn(top, "Delete", self.delete_current, "danger").pack(side="right", padx=(8, 0))
        Btn(top, "Edit", self.show_edit, "ghost").pack(side="right")
        cat = e.get("category", "")
        chip = tk.Label(s, text=f"  {cat or 'Unsorted'}  ", font=F["small"], fg=C["accent"] if cat else C["faint"],
                        bg=C["raised"], bd=0, padx=4, pady=3, highlightthickness=1, highlightbackground=C["line"])
        chip.pack(anchor="w", pady=(12, 0))
        label(s, "Updated " + (e.get("updated") or "—"), "small", "faint").pack(side="bottom", anchor="w")

        def row(cap, key, what, secret=False, mono=False):
            val = e.get(key, "")
            label(s, cap, "cap", "faint").pack(anchor="w", pady=(20, 7))
            r = tk.Frame(s, bg=C["field"], highlightthickness=1, highlightbackground=C["line"])
            r.pack(fill="x")
            shown = {"on": False}
            v = tk.Label(r, text=("•" * 12) if secret and val else (val or "—"), font=F["mono"] if mono else F["body"],
                         fg=C["text"] if val else C["faint"], bg=C["field"], anchor="w", padx=12, pady=10)
            v.pack(side="left", fill="x", expand=True)
            if val:
                Btn(r, "Copy", lambda: self.copy(val, what), "quiet", padx=12, pady=4,
                    font=F["small"]).pack(side="right", padx=(0, 6))
                if secret:
                    def flip(b=None):
                        shown["on"] = not shown["on"]
                        v.configure(text=val if shown["on"] else "•" * 12)
                        eye.configure(text="Hide" if shown["on"] else "Show")
                    eye = Btn(r, "Show", flip, "quiet", padx=12, pady=4, font=F["small"])
                    eye.pack(side="right")
        row("USERNAME", "username", "Username")
        row("PASSWORD", "password", "Password", True, True)
        row("WEBSITE", "url", "Website")
        label(s, "NOTES", "cap", "faint").pack(anchor="w", pady=(20, 7))
        t = tk.Text(s, height=min(8, max(2, e.get("notes", "").count("\n") + 2)), wrap="word", font=F["body"],
                    bg=C["field"], fg=C["text"] if e.get("notes") else C["faint"], relief="flat", bd=0,
                    highlightthickness=1, highlightbackground=C["line"], padx=12, pady=10)
        t.insert("1.0", e.get("notes") or "No notes")
        t.configure(state="disabled")
        t.pack(fill="x")

    def new_entry(self):
        self.current_id = None
        self.refresh()
        self.show_edit()

    def show_edit(self):
        e = self.current() or {}
        self.mode, self.editing_id = "edit", e.get("id")
        if e.get("id"):
            self.edit_cat = e.get("category", "")
        elif self.tab in self.vault.tabs:
            self.edit_cat = self.tab
        else:
            self.edit_cat = self.vault.tabs[0] if self.vault.tabs else ""
        s = self.stage()
        foot = tk.Frame(s, bg=C["bg"])
        foot.pack(side="bottom", fill="x", pady=(12, 0))
        Btn(foot, "Save entry", self.save_edit, "primary", padx=22).pack(side="left")
        Btn(foot, "Cancel", self.cancel_edit, "ghost").pack(side="left", padx=(8, 0))
        self.edit_err = label(foot, "", "small", "bad")
        self.edit_err.pack(side="left", padx=14)
        label(s, "EDITING" if e.get("id") else "NEW ENTRY", "cap", "accent").pack(anchor="w")
        label(s, e.get("title") or "Add a login", "h1").pack(anchor="w", pady=(4, 6))

        # tab picker
        label(s, "TAB", "cap", "faint").pack(anchor="w", pady=(10, 6))
        chips = tk.Frame(s, bg=C["bg"])
        chips.pack(anchor="w", fill="x")
        self._chip_widgets = {}

        def paint():
            for key, w in self._chip_widgets.items():
                on = key == self.edit_cat
                w.configure(bg=C["accent"] if on else C["raised"], fg=C["accent_ink"] if on else C["muted"])

        def choose(key):
            self.edit_cat = key
            paint()
        opts = list(self.vault.tabs) + [""]
        for key in opts:
            w = tk.Label(chips, text=key or "Unsorted", font=F["small"], padx=12, pady=5, bd=0, cursor="hand2")
            w.pack(side="left", padx=(0, 6))
            w.bind("<Button-1>", lambda ev, k=key: choose(k))
            self._chip_widgets[key] = w
        paint()

        self.edit = {}
        for key, cap, secret in (("title", "TITLE", False), ("username", "USERNAME", False),
                                 ("url", "WEBSITE", False), ("password", "PASSWORD", True)):
            label(s, cap, "cap", "faint").pack(anchor="w", pady=(12, 6))
            meter = Meter(s) if key == "password" else None
            fld = Field(s, secret=secret, width=40, font=F["mono"] if secret else F["body"],
                        on_change=(lambda: meter.update_for(self.edit["password"].get())) if meter else None)
            fld.pack(fill="x")
            self.edit[key] = fld
            fld.set(e.get(key, ""))
            if meter:
                meter.pack(fill="x", pady=(8, 0))
                meter.update_for(fld.get())
        gen = tk.Frame(s, bg=C["bg"])
        gen.pack(fill="x", pady=(10, 0))
        length, symbols = tk.IntVar(value=20), tk.BooleanVar(value=True)
        Btn(gen, "Generate", lambda: self.edit["password"].set(generate_password(length.get(), symbols.get())),
            "ghost", padx=14, pady=5, font=F["small"]).pack(side="left")
        label(gen, "", "small", "muted")
        tk.Scale(gen, from_=12, to=48, orient="horizontal", variable=length, showvalue=True, length=160,
                 sliderlength=16, width=10, bd=0, highlightthickness=0, bg=C["bg"], fg=C["muted"],
                 troughcolor=C["line"], activebackground=C["accent"], relief="flat").pack(side="left", padx=(14, 4))
        tk.Checkbutton(gen, text="Symbols", variable=symbols, font=F["small"], bg=C["bg"], fg=C["muted"],
                       selectcolor=C["field"], activebackground=C["bg"], activeforeground=C["text"],
                       highlightthickness=0, bd=0).pack(side="left", padx=(14, 0))
        label(s, "NOTES", "cap", "faint").pack(anchor="w", pady=(14, 6))
        nb = tk.Frame(s, bg=C["line"], padx=1, pady=1)
        nb.pack(fill="x")
        self.notes = tk.Text(nb, height=4, wrap="word", font=F["body"], bg=C["field"], fg=C["text"],
                             insertbackground=C["accent"], relief="flat", bd=0, highlightthickness=0, padx=10, pady=8)
        self.notes.insert("1.0", e.get("notes", ""))
        self.notes.pack(fill="x")
        self.edit["title"].focus()

    def cancel_edit(self):
        self.editing_id = None
        if self.current():
            self.show_view()
        else:
            self.show_empty()

    def save_edit(self):
        if self.mode != "edit":
            return
        title = self.edit["title"].get().strip()
        if not title:
            return self.edit_err.configure(text="Give this entry a title.")
        data = dict(title=title, username=self.edit["username"].get().strip(),
                    url=self.edit["url"].get().strip(), password=self.edit["password"].get(),
                    notes=self.notes.get("1.0", "end").rstrip("\n"), category=self.edit_cat,
                    updated=time.strftime("%Y-%m-%d %H:%M"))
        ent = next((x for x in self.vault.entries if x["id"] == self.editing_id), None) if self.editing_id else None
        backup = dict(ent) if ent else None
        if ent:
            ent.update(data)
        else:
            ent = dict(data, id=uuid.uuid4().hex)
            self.vault.entries.append(ent)
        if not self.persist():
            if backup:
                ent.clear()
                ent.update(backup)
            else:
                self.vault.entries.remove(ent)
            return
        self.current_id = ent["id"]
        self.editing_id = None
        if self.tab not in (TAB_ALL,) and not self.in_tab(ent):
            self.tab = ent["category"] if ent["category"] else TAB_NONE
        self.refresh()
        self.show_view()

    def delete_current(self):
        e = self.current()
        if not e:
            return

        def do():
            self.vault.entries = [x for x in self.vault.entries if x["id"] != e["id"]]
            if not self.persist():
                self.vault.entries.append(e)
                return
            self.current_id = None
            self.refresh()
            self.show_empty()
        self.confirm("Delete this entry?", f"“{e.get('title', '')}” will be permanently removed from your vault.",
                     do, "Delete", True)

    # ----- master password
    def change_master_dialog(self):
        m = Modal(self, "Change master password")
        label(m.body, "Change master password", "h2").pack(anchor="w", pady=(0, 14))
        f = {}
        meter = Meter(m.body)
        for key, cap in (("cur", "CURRENT PASSWORD"), ("new", "NEW PASSWORD"), ("conf", "CONFIRM NEW PASSWORD")):
            label(m.body, cap, "cap", "faint").pack(anchor="w", pady=(10, 5))
            f[key] = Field(m.body, secret=True, width=34,
                           on_change=(lambda: meter.update_for(f["new"].get())) if key == "new" else None)
            f[key].pack(fill="x")
            if key == "new":
                meter.pack(fill="x", pady=(8, 0))
        err = label(m.body, " ", "small", "bad", wraplength=340, justify="left", anchor="w")
        err.pack(fill="x", pady=(10, 0))
        row = tk.Frame(m.body, bg=C["panel"])
        row.pack(anchor="e", pady=(12, 0))

        def submit():
            try:
                probe = Vault(self.vault.path)
                err.configure(text="Checking…")
                m.update_idletasks()
                probe.unlock(f["cur"].get(), upgrade=False)
            except WrongPassword:
                return err.configure(text="Current password is wrong.")
            except (CorruptVault, OSError, ValueError, KeyError):
                return err.configure(text="Couldn't read the vault file.")
            msg = check_master(f["new"].get())
            if msg:
                return err.configure(text=msg)
            if f["new"].get() != f["conf"].get():
                return err.configure(text="The new passwords don't match.")
            err.configure(text="Re-encrypting…")
            m.update_idletasks()
            try:
                self.vault.change_master(f["new"].get())
            except OSError:
                return err.configure(text="Couldn't write the vault file.")
            m.close()
            self.toast("Master password changed")
        Btn(row, "Cancel", m.close, "ghost").pack(side="left", padx=(0, 8))
        Btn(row, "Change password", submit, "primary").pack(side="left")
        m.present()
        f["cur"].focus()

    # ----- export / import
    def pick(self, mode, title, **kw):
        fn = filedialog.asksaveasfilename if mode == "save" else filedialog.askopenfilename
        return fn(parent=self, title=title, **kw)

    def export_dialog(self):
        if not self.vault.entries:
            return self.alert("Nothing to export", "Your vault has no entries yet.")
        m = Modal(self, "Export")
        label(m.body, "Export your vault", "h2").pack(anchor="w")
        label(m.body, "Choose how to take your data out.", "body", "muted").pack(anchor="w", pady=(6, 18))
        self.m_export = m

        def card(title, text, cmd, hover=None):
            c = tk.Frame(m.body, bg=C["raised"], highlightthickness=1, highlightbackground=C["line"], cursor="hand2")
            c.pack(fill="x", pady=(0, 10))
            t = label(c, title, "bold", bg=C["raised"])
            t.pack(anchor="w", padx=16, pady=(12, 2))
            d = label(c, text, "small", "muted", bg=C["raised"], wraplength=330, justify="left")
            d.pack(anchor="w", padx=16, pady=(0, 12))
            for w in (c, t, d):
                w.bind("<Button-1>", lambda e: cmd())
                w.bind("<Enter>", lambda e: c.configure(highlightbackground=hover or C["accent"]))
                w.bind("<Leave>", lambda e: c.configure(highlightbackground=C["line"]))
        card("Encrypted backup", "A copy of your vault, still locked with your master password. Safe to keep anywhere.",
             self.export_backup)
        card("Plain CSV", "Unencrypted, for moving to another password manager. Asks for your master password first.",
             self.export_csv_step, C["bad"])
        Btn(m.body, "Cancel", m.close, "quiet").pack(anchor="e", pady=(6, 0))
        m.present()

    def export_backup(self):
        self.export_dialog_close()
        dest = self.pick("save", "Save encrypted backup", defaultextension=".json",
                         initialfile="localvault-backup-" + time.strftime("%Y-%m-%d") + ".json",
                         filetypes=[("LocalVault backup", "*.json")])
        if not dest or self.vault._key is None:
            return
        if Path(dest).resolve() == self.vault.path.resolve():
            return self.alert("Choose another file", "That's your live vault file. Pick a different location for the backup.")
        try:
            write_private(dest, self.vault.path.read_bytes())
            self.toast("Encrypted backup saved")
        except OSError:
            self.alert("Export failed", "Couldn't write the file. Check the location and permissions.")

    def export_dialog_close(self):
        if self._modal:
            self._modal.close()

    def export_csv_step(self):
        m = self._modal
        for w in m.body.winfo_children():
            w.destroy()
        label(m.body, "Export plain CSV", "h2").pack(anchor="w")
        label(m.body, "This file will contain every password in plain text. Anyone who can read it can read them. "
                      "Delete it as soon as you've imported it.", "body", "warn", wraplength=340, justify="left").pack(anchor="w", pady=(8, 16))
        label(m.body, "MASTER PASSWORD", "cap", "faint").pack(anchor="w", pady=(0, 6))
        pw = Field(m.body, secret=True, width=34)
        pw.pack(fill="x")
        err = label(m.body, " ", "small", "bad", wraplength=340, justify="left", anchor="w")
        err.pack(fill="x", pady=(10, 0))
        row = tk.Frame(m.body, bg=C["panel"])
        row.pack(anchor="e", pady=(12, 0))

        def go():
            try:
                Vault(self.vault.path).unlock(pw.get(), upgrade=False)
            except WrongPassword:
                return err.configure(text="Wrong password.")
            except (CorruptVault, OSError, ValueError, KeyError):
                return err.configure(text="Couldn't read the vault file.")
            m.close()
            dest = self.pick("save", "Save CSV", defaultextension=".csv", initialfile="localvault-export.csv",
                             filetypes=[("CSV", "*.csv")])
            if not dest or self.vault._key is None:
                return
            try:
                write_csv(dest, self.vault.entries)
                self.toast("CSV saved")
            except OSError:
                self.alert("Export failed", "Couldn't write the file.")
        Btn(row, "Back", lambda: (m.close(), self.export_dialog()), "ghost").pack(side="left", padx=(0, 8))
        Btn(row, "Export CSV", go, "danger_fill").pack(side="left")
        pw.on_return(go)
        pw.focus()

    def import_dialog(self):
        m = Modal(self, "Import")
        state = {}

        def reset():
            for w in m.body.winfo_children():
                w.destroy()

        def start():
            reset()
            label(m.body, "Import entries", "h2").pack(anchor="w")
            label(m.body, "Bring in a CSV from another password manager (like Chrome or Bitwarden), or a LocalVault "
                          "backup. Columns are matched automatically; a “folder” or “category” column becomes a tab.",
                  "body", "muted", wraplength=340, justify="left").pack(anchor="w", pady=(8, 16))
            err = label(m.body, " ", "small", "bad", wraplength=340, justify="left", anchor="w")
            err.pack(fill="x")
            state["err"] = err
            row = tk.Frame(m.body, bg=C["panel"])
            row.pack(anchor="e", pady=(10, 0))
            Btn(row, "Cancel", m.close, "ghost").pack(side="left", padx=(0, 8))
            Btn(row, "Choose file…", choose, "primary").pack(side="left")

        def choose():
            path = self.pick("open", "Choose a file to import",
                             filetypes=[("Password exports", "*.csv *.json"), ("All files", "*")])
            if not path:
                return
            try:
                kind, payload = analyze_import(path)
            except ImportProblem as ex:
                return state["err"].configure(text=str(ex))
            except (OSError, ValueError):
                return state["err"].configure(text="Couldn't read that file.")
            if kind == "backup":
                state["name"] = os.path.basename(path)
                backup_step(payload)
            else:
                preview(payload, os.path.basename(path))

        def backup_step(path):
            reset()
            label(m.body, "Locked backup", "h2").pack(anchor="w")
            label(m.body, f"Enter the master password {state['name']} was made with.", "body", "muted",
                  wraplength=340, justify="left").pack(anchor="w", pady=(8, 16))
            pw = Field(m.body, secret=True, width=34)
            pw.pack(fill="x")
            err = label(m.body, " ", "small", "bad", wraplength=340, justify="left", anchor="w")
            err.pack(fill="x", pady=(10, 0))
            row = tk.Frame(m.body, bg=C["panel"])
            row.pack(anchor="e", pady=(12, 0))
            btn = Btn(row, "Open backup", lambda: go(), "primary")

            def go():
                err.configure(text="Opening…")
                m.update_idletasks()
                try:
                    v = Vault(path)
                    v.unlock(pw.get(), upgrade=False)
                    preview(v.entries, state["name"], v.tabs)
                except WrongPassword:
                    err.configure(text="Wrong password for this backup.")
                except (CorruptVault, KeyError, ValueError, TypeError):
                    err.configure(text="This backup is damaged.")
                except OSError:
                    err.configure(text="Couldn't read that file.")
            Btn(row, "Back", start, "ghost").pack(side="left", padx=(0, 8))
            btn.pack(side="left")
            pw.on_return(go)
            pw.focus()

        def preview(entries, name, tabs=()):
            reset()
            skip = tk.BooleanVar(value=True)
            label(m.body, "Ready to import", "h2").pack(anchor="w")
            label(m.body, f"{len(entries)} {'entry' if len(entries) == 1 else 'entries'} found in {name}",
                  "body", "muted").pack(anchor="w", pady=(6, 14))
            btn_holder = {}

            def count():
                return len(merge_plan(self.vault.entries, entries, skip.get()))

            def refresh_btn():
                n = count()
                btn_holder["b"].configure(text=f"Import {n} {'entry' if n == 1 else 'entries'}")
            tk.Checkbutton(m.body, text="Skip entries already in my vault", variable=skip, command=refresh_btn,
                           font=F["body"], bg=C["panel"], fg=C["text"], selectcolor=C["field"],
                           activebackground=C["panel"], activeforeground=C["text"],
                           highlightthickness=0, bd=0).pack(anchor="w")
            row = tk.Frame(m.body, bg=C["panel"])
            row.pack(anchor="e", pady=(20, 0))

            def go():
                new = merge_plan(self.vault.entries, entries, skip.get())
                before_e, before_t = list(self.vault.entries), list(self.vault.tabs)
                self.vault.entries = before_e + new
                self.vault.tabs = clean_tabs(list(before_t) + list(tabs), self.vault.entries)
                if not self.persist():
                    self.vault.entries, self.vault.tabs = before_e, before_t
                    return
                m.close()
                self.refresh()
                if self.mode == "empty":
                    self.show_empty()
                self.toast(f"Imported {len(new)} entries")
            Btn(row, "Cancel", m.close, "ghost").pack(side="left", padx=(0, 8))
            btn_holder["b"] = Btn(row, "Import", go, "primary")
            btn_holder["b"].pack(side="left")
            refresh_btn()

        start()
        m.present()


def main():
    if sys.platform == "win32":
        try:
            import ctypes
            ctypes.windll.shcore.SetProcessDpiAwareness(1)
        except Exception:
            pass
    App().mainloop()


if __name__ == "__main__":
    main()
