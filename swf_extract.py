#!/usr/bin/env python3
"""
swf_extract - extract every asset from SWF files using only the Python standard library.

    python swf_extract.py game.swf -o out
    python swf_extract.py *.swf --only sprites,scripts,fonts --frames
    python swf_extract.py game.swf --list
"""
import sys as _sys
import types as _types

_EMBEDDED = []
_EMBEDDED.append(('swf_extract_v2', r'''"""Core SWF parsing, shapes, morphs and SVG rendering."""
import argparse
import base64
import glob
import html as htmlmod
import io
import json
import lzma
import math
import os
import re
import struct
import sys
import wave
import zlib
from array import array

try:
    from PIL import Image
except ImportError:
    Image = None

__version__ = "2.0"

CATEGORIES = ["images", "sounds", "shapes", "morphs", "sprites", "fonts",
              "texts", "video", "binary", "scripts"]
RATES = [5512, 11025, 22050, 44100]
SND_EXT = {4: "nellymoser16.bin", 5: "nellymoser8.bin", 6: "nellymoser.bin",
           11: "speex.bin"}
IDENT = (1, 0, 0, 1, 0, 0)
BLEND = {3: "multiply", 4: "screen", 5: "lighten", 6: "darken", 7: "difference",
         13: "overlay", 14: "hard-light"}
RAW_TAGS = {7: "button", 34: "button2", 12: "action"}
TIMELINE = (1, 4, 5, 26, 28, 43, 70)
TAGNAMES = {
    0: "End", 1: "ShowFrame", 2: "DefineShape", 4: "PlaceObject", 5: "RemoveObject",
    6: "DefineBits", 7: "DefineButton", 8: "JPEGTables", 9: "SetBackgroundColor",
    10: "DefineFont", 11: "DefineText", 12: "DoAction", 13: "DefineFontInfo",
    14: "DefineSound", 15: "StartSound", 18: "SoundStreamHead", 19: "SoundStreamBlock",
    20: "DefineBitsLossless", 21: "DefineBitsJPEG2", 22: "DefineShape2",
    26: "PlaceObject2", 28: "RemoveObject2", 32: "DefineShape3", 33: "DefineText2",
    34: "DefineButton2", 35: "DefineBitsJPEG3", 36: "DefineBitsLossless2",
    37: "DefineEditText", 39: "DefineSprite", 43: "FrameLabel",
    45: "SoundStreamHead2", 46: "DefineMorphShape", 48: "DefineFont2",
    56: "ExportAssets", 59: "DoInitAction", 60: "DefineVideoStream", 61: "VideoFrame",
    62: "DefineFontInfo2", 69: "FileAttributes", 70: "PlaceObject3", 72: "DoABC1",
    75: "DefineFont3", 76: "SymbolClass", 77: "Metadata", 82: "DoABC",
    83: "DefineShape4", 84: "DefineMorphShape2", 87: "DefineBinaryData",
    88: "DefineFontName", 90: "DefineBitsJPEG4", 91: "DefineFont4",
    24: "Protect", 41: "ProductInfo", 57: "ImportAssets", 58: "EnableDebugger", 63: "DebugID",
    64: "EnableDebugger2", 65: "ScriptLimits", 66: "SetTabIndex", 71: "ImportAssets2",
    73: "DefineFontAlignZones", 74: "CSMTextSettings", 78: "DefineScalingGrid",
    86: "DefineSceneAndFrameLabelData", 89: "StartSound2", 92: "SignedData",
}


def warn(msg):
    print("  ! " + msg, file=sys.stderr)


def u16(d, o): return struct.unpack_from("<H", d, o)[0]
def u32(d, o): return struct.unpack_from("<I", d, o)[0]


def safe(s):
    return re.sub(r"[^\w.\-]+", "_", s)[:80]


def fmt(v):
    if isinstance(v, int):
        return str(v)
    if abs(v - round(v)) < 1e-9:
        return str(int(round(v)))
    return ("%.2f" % v).rstrip("0").rstrip(".")


def fm(v):
    s = ("%.5f" % v).rstrip("0").rstrip(".")
    return "0" if s in ("", "-0") else s


def mat_str(m):
    return "matrix(%s %s %s %s %s %s)" % (fm(m[0]), fm(m[1]), fm(m[2]), fm(m[3]),
                                          fmt(m[4]), fmt(m[5]))


def hx(c):
    return "#%02x%02x%02x" % (int(c[0]), int(c[1]), int(c[2]))


def lerp(a, b, t): return a + (b - a) * t
def lerp_col(c0, c1, t): return tuple(int(round(lerp(x, y, t))) for x, y in zip(c0, c1))
def lerp_mat(m0, m1, t): return tuple(lerp(x, y, t) for x, y in zip(m0, m1))


class Bits:
    def __init__(self, d, pos=0):
        self.d = d
        self.p = pos * 8

    def ub(self, n):
        if n <= 0:
            return 0
        p = self.p
        e = p + n
        if e > len(self.d) * 8:
            raise EOFError("unexpected end of data")
        b0, b1 = p >> 3, (e + 7) >> 3
        v = int.from_bytes(self.d[b0:b1], "big") >> (b1 * 8 - e)
        self.p = e
        return v & ((1 << n) - 1)

    def sb(self, n):
        v = self.ub(n)
        return v - (1 << n) if n and v >> (n - 1) else v

    def fb(self, n): return self.sb(n) / 65536.0
    def align(self): self.p = (self.p + 7) & ~7
    def pos(self): return (self.p + 7) >> 3
    def left(self): return len(self.d) - self.pos()

    def _take(self, n):
        self.align()
        o = self.p >> 3
        if o + n > len(self.d):
            raise EOFError("unexpected end of data")
        self.p += n * 8
        return self.d[o:o + n]

    def bytes(self, n): return bytes(self._take(n))
    def u8(self): return self._take(1)[0]
    def u16(self): return struct.unpack("<H", self._take(2))[0]
    def s16(self): return struct.unpack("<h", self._take(2))[0]
    def u32(self): return struct.unpack("<I", self._take(4))[0]

    def cstr(self):
        self.align()
        o = self.p >> 3
        e = self.d.find(b"\0", o)
        if e < 0:
            e = len(self.d)
        self.p = (e + 1) * 8
        return self.d[o:e].decode("utf-8", "replace")

    def rect(self):
        self.align()
        n = self.ub(5)
        r = (self.sb(n), self.sb(n), self.sb(n), self.sb(n))
        self.align()
        return r

    def matrix(self):
        self.align()
        sx = sy = 1.0
        r0 = r1 = 0.0
        if self.ub(1):
            n = self.ub(5)
            sx, sy = self.fb(n), self.fb(n)
        if self.ub(1):
            n = self.ub(5)
            r0, r1 = self.fb(n), self.fb(n)
        n = self.ub(5)
        tx, ty = self.sb(n), self.sb(n)
        self.align()
        return (sx, r0, r1, sy, tx, ty)

    def rgb(self):
        return tuple(self._take(3))

    def rgba(self):
        return tuple(self._take(4))

    def cxform(self, alpha):
        self.align()
        has_add, has_mul, n = self.ub(1), self.ub(1), self.ub(4)
        k = 4 if alpha else 3
        mul = [256] * 4
        add = [0] * 4
        if has_mul:
            for i in range(k):
                mul[i] = self.sb(n)
        if has_add:
            for i in range(k):
                add[i] = self.sb(n)
        self.align()
        return (mul[0] / 256.0, mul[1] / 256.0, mul[2] / 256.0, mul[3] / 256.0,
                add[0], add[1], add[2], add[3])


def load_swf(src):
    raw = open(src, "rb").read() if isinstance(src, str) else src
    sig, ver = raw[:3], raw[3]
    if sig == b"FWS":
        body = raw[8:]
    elif sig == b"CWS":
        body = zlib.decompressobj().decompress(raw[8:])
    elif sig == b"ZWS":
        props, stream = raw[12:17], raw[17:]
        body = lzma.LZMADecompressor(lzma.FORMAT_ALONE).decompress(
            props + b"\xff" * 8 + stream)
    else:
        raise ValueError("not an SWF file")
    b = Bits(body)
    rect = b.rect()
    fps = b.u16() / 256.0
    nframes = b.u16()
    return dict(version=ver, sig=sig.decode(), rect=rect, fps=fps or 12.0,
                nframes=nframes, body=body, pos=b.pos())


def iter_tags(buf, pos=0):
    n = len(buf)
    while pos + 2 <= n:
        h = u16(buf, pos)
        pos += 2
        code, ln = h >> 6, h & 0x3F
        if ln == 0x3F:
            ln = u32(buf, pos)
            pos += 4
        yield code, buf[pos:pos + ln]
        pos += ln
        if code == 0:
            break


def write_png(w, h, rgba):
    raw = bytearray()
    for y in range(h):
        raw.append(0)
        raw += rgba[y * w * 4:(y + 1) * w * 4]

    def chunk(t, dd):
        return (struct.pack(">I", len(dd)) + t + dd +
                struct.pack(">I", zlib.crc32(t + dd) & 0xFFFFFFFF))

    return (b"\x89PNG\r\n\x1a\n" +
            chunk(b"IHDR", struct.pack(">IIBBBBB", w, h, 8, 6, 0, 0, 0)) +
            chunk(b"IDAT", zlib.compress(bytes(raw), 9)) + chunk(b"IEND", b""))


def unpremul(r, g, b, a):
    if a == 255:
        return r, g, b, a
    if a == 0:
        return 0, 0, 0, 0
    return (min(255, r * 255 // a), min(255, g * 255 // a),
            min(255, b * 255 // a), a)


def decode_lossless(d, v2):
    cid, fmt_, w, h = struct.unpack_from("<HBHH", d, 0)
    p, ncol = 7, 0
    if fmt_ == 3:
        ncol = d[p] + 1
        p += 1
    data = zlib.decompress(d[p:])
    out = bytearray(w * h * 4)
    o = 0
    if fmt_ == 3:
        es = 4 if v2 else 3
        pal = []
        for i in range(ncol):
            e = data[i * es:(i + 1) * es]
            c = (e[0], e[1], e[2], e[3] if v2 else 255)
            pal.append(unpremul(*c) if v2 else c)
        pix, stride = data[ncol * es:], (w + 3) & ~3
        for y in range(h):
            for x in range(w):
                i = pix[y * stride + x]
                out[o:o + 4] = bytes(pal[i] if i < ncol else (0, 0, 0, 0))
                o += 4
    elif fmt_ == 4:
        stride = (w * 2 + 3) & ~3
        for y in range(h):
            for x in range(w):
                v = (data[y * stride + 2 * x] << 8) | data[y * stride + 2 * x + 1]
                r, g, b = (v >> 10) & 31, (v >> 5) & 31, v & 31
                out[o:o + 4] = bytes((r * 255 // 31, g * 255 // 31, b * 255 // 31, 255))
                o += 4
    elif fmt_ == 5:
        for i in range(w * h):
            a, r, g, b = data[i * 4:i * 4 + 4]
            out[o:o + 4] = bytes(unpremul(r, g, b, a) if v2 else (r, g, b, 255))
            o += 4
    else:
        raise ValueError("unknown lossless format: %d" % fmt_)
    return cid, write_png(w, h, out)


def sniff_image(d):
    if d[:8] == b"\x89PNG\r\n\x1a\n":
        return "png"
    if d[:3] == b"GIF":
        return "gif"
    return "jpg"


def fix_jpeg(d):
    return d[4:] if d[:4] == b"\xff\xd9\xff\xd8" else d


def merge_jpeg_tables(tables, d):
    d = fix_jpeg(d)
    if tables and len(tables) > 4:
        t = tables[:-2] if tables[-2:] == b"\xff\xd9" else tables
        return t + (d[2:] if d[:2] == b"\xff\xd8" else d)
    return d


def img_size(ext, d):
    try:
        if ext == "png":
            return struct.unpack(">II", d[16:24])
        if ext == "gif":
            return struct.unpack("<HH", d[6:10])
        p = 2
        while p + 9 < len(d):
            if d[p] != 0xFF:
                p += 1
                continue
            mk = d[p + 1]
            if 0xC0 <= mk <= 0xCF and mk not in (0xC4, 0xC8, 0xCC):
                h, w = struct.unpack(">HH", d[p + 5:p + 9])
                return w, h
            p += 2 + struct.unpack(">H", d[p + 2:p + 4])[0]
    except Exception:
        pass
    return 0, 0


STEP = [7, 8, 9, 10, 11, 12, 13, 14, 16, 17, 19, 21, 23, 25, 28, 31, 34, 37, 41, 45,
        50, 55, 60, 66, 73, 80, 88, 97, 107, 118, 130, 143, 157, 173, 190, 209, 230,
        253, 279, 307, 337, 371, 408, 449, 494, 544, 598, 658, 724, 796, 876, 963,
        1060, 1166, 1282, 1411, 1552, 1707, 1878, 2066, 2272, 2499, 2749, 3024, 3327,
        3660, 4026, 4428, 4871, 5358, 5894, 6484, 7132, 7845, 8630, 9493, 10442,
        11487, 12635, 13899, 15289, 16818, 18500, 20350, 22385, 24623, 27086, 29794,
        32767]
IDXTAB = {2: [-1, 2], 3: [-1, -1, 2, 4], 4: [-1, -1, -1, -1, 2, 4, 6, 8],
          5: [-1] * 8 + [1, 2, 4, 6, 8, 10, 13, 16]}


def adpcm_decode(data, ch, max_samples=None):
    b = Bits(data)
    bits = b.ub(2) + 2
    m = bits - 1
    tbl = IDXTAB[bits]
    sign = 1 << m
    mask = sign - 1
    out = array("h")
    total = len(data) * 8
    while total - b.p >= 22 * ch:
        pred = [0] * ch
        idx = [0] * ch
        for c in range(ch):
            pred[c] = b.sb(16)
            idx[c] = min(b.ub(6), 88)
            out.append(pred[c])
        for _ in range(4095):
            if total - b.p < bits * ch:
                break
            for c in range(ch):
                code = b.ub(bits)
                step = STEP[idx[c]]
                diff = step >> m
                for j in range(m):
                    if code & (1 << j):
                        diff += step >> (m - 1 - j)
                p = pred[c] - diff if code & sign else pred[c] + diff
                pred[c] = max(-32768, min(32767, p))
                idx[c] = max(0, min(88, idx[c] + tbl[code & mask]))
                out.append(pred[c])
    if max_samples:
        del out[max_samples * ch:]
    if sys.byteorder == "big":
        out.byteswap()
    return out


def make_wav(data, rate, bits, ch):
    buf = io.BytesIO()
    with wave.open(buf, "wb") as w:
        w.setnchannels(ch)
        w.setsampwidth(bits // 8)
        w.setframerate(rate)
        w.writeframes(data)
    return buf.getvalue()


def sound_payload(fmt_, rate, bits, ch, blocks, count=None):
    """blocks - list of data chunks. -> (ext, bytes)"""
    if fmt_ == 2:
        return "mp3", b"".join(blocks)
    if fmt_ in (0, 3):
        return "wav", make_wav(b"".join(blocks), rate, bits, ch)
    if fmt_ == 1:
        pcm = b"".join(adpcm_decode(bl, ch, count if len(blocks) == 1 else None).tobytes()
                       for bl in blocks)
        return "wav", make_wav(pcm, rate, 16, ch)
    return SND_EXT.get(fmt_, "fmt%d.bin" % fmt_), b"".join(blocks)


def read_gradient(b, ver, focal):
    b.align()
    spread, interp, n = b.ub(2), b.ub(2), b.ub(4)
    stops = []
    for _ in range(n):
        ratio = b.u8()
        col = b.rgba() if ver >= 3 else b.rgb() + (255,)
        stops.append((ratio, col))
    fp = b.s16() / 256.0 if focal else 0
    return dict(spread=spread, interp=interp, stops=stops, focal=fp)


def read_fill(b, ver):
    t = b.u8()
    st = {"t": t}
    if t == 0:
        st["c"] = b.rgba() if ver >= 3 else b.rgb() + (255,)
    elif t in (0x10, 0x12, 0x13):
        st["m"] = b.matrix()
        st["g"] = read_gradient(b, ver, t == 0x13)
    elif 0x40 <= t <= 0x43:
        st["bmp"] = b.u16()
        st["m"] = b.matrix()
    else:
        raise ValueError("unknown fill type 0x%x" % t)
    return st


def read_line(b, ver):
    if ver < 4:
        w = b.u16()
        c = b.rgba() if ver >= 3 else b.rgb() + (255,)
        return dict(w=w, c=c, cap=0, join=0, miter=3)
    w = b.u16()
    b.align()
    scap, join, hasfill = b.ub(2), b.ub(2), b.ub(1)
    b.ub(3)
    b.ub(5)
    b.ub(1)
    b.ub(2)
    miter = b.u16() / 256.0 if join == 2 else 3
    st = dict(w=w, cap=scap, join=join, miter=miter)
    if hasfill:
        st["fill"] = read_fill(b, ver)
    else:
        st["c"] = b.rgba()
    return st


def read_styles(b, ver):
    n = b.u8()
    if n == 0xFF and ver >= 2:
        n = b.u16()
    fills = [read_fill(b, ver) for _ in range(n)]
    n = b.u8()
    if n == 0xFF and ver >= 2:
        n = b.u16()
    lines = [read_line(b, ver) for _ in range(n)]
    return fills, lines


def read_records(b, nf, nl, ver):
    recs = []
    x = y = 0
    while True:
        if not b.ub(1):
            fl = b.ub(5)
            if fl == 0:
                break
            mv = f0 = f1 = ln = ns = None
            if fl & 1:
                n = b.ub(5)
                x, y = b.sb(n), b.sb(n)
                mv = (x, y)
            if fl & 2:
                f0 = b.ub(nf)
            if fl & 4:
                f1 = b.ub(nf)
            if fl & 8:
                ln = b.ub(nl)
            if fl & 16:
                fills, lines = read_styles(b, ver)
                nf, nl = b.ub(4), b.ub(4)
                ns = (fills, lines)
            recs.append(("s", mv, f0, f1, ln, ns))
        elif b.ub(1):
            n = b.ub(4) + 2
            if b.ub(1):
                dx, dy = b.sb(n), b.sb(n)
            elif b.ub(1):
                dx, dy = 0, b.sb(n)
            else:
                dx, dy = b.sb(n), 0
            recs.append(("l", x, y, x + dx, y + dy))
            x += dx
            y += dy
        else:
            n = b.ub(4) + 2
            cdx, cdy, adx, ady = b.sb(n), b.sb(n), b.sb(n), b.sb(n)
            cx, cy = x + cdx, y + cdy
            ax, ay = cx + adx, cy + ady
            recs.append(("q", x, y, cx, cy, ax, ay))
            x, y = ax, ay
    return recs


def parse_shape(code, d):
    ver = {2: 1, 22: 2, 32: 3, 83: 4}[code]
    b = Bits(d)
    sid = b.u16()
    bounds = b.rect()
    nonzero = False
    if ver == 4:
        b.rect()
        nonzero = bool(b.u8() & 4)
    fills, lines = read_styles(b, ver)
    nf, nl = b.ub(4), b.ub(4)
    recs = read_records(b, nf, nl, ver)
    return dict(id=sid, bounds=bounds, fills=fills, lines=lines, records=recs,
                nonzero=nonzero)


def read_morph_fill(b):
    t = b.u8()
    s, e = {"t": t}, {"t": t}
    if t == 0:
        s["c"], e["c"] = b.rgba(), b.rgba()
    elif t in (0x10, 0x12, 0x13):
        s["m"], e["m"] = b.matrix(), b.matrix()
        k = b.u8()
        ss, es = [], []
        for _ in range(k):
            rs, cs, re_, ce = b.u8(), b.rgba(), b.u8(), b.rgba()
            ss.append((rs, cs))
            es.append((re_, ce))
        fs = fe = 0
        if t == 0x13:
            fs, fe = b.s16() / 256.0, b.s16() / 256.0
        s["g"] = dict(spread=0, interp=0, stops=ss, focal=fs)
        e["g"] = dict(spread=0, interp=0, stops=es, focal=fe)
    elif 0x40 <= t <= 0x43:
        s["bmp"] = e["bmp"] = b.u16()
        s["m"], e["m"] = b.matrix(), b.matrix()
    else:
        raise ValueError("unknown morph fill 0x%x" % t)
    return s, e


def read_morph_styles(b, ver):
    n = b.u8()
    if n == 0xFF:
        n = b.u16()
    fills = [read_morph_fill(b) for _ in range(n)]
    n = b.u8()
    if n == 0xFF:
        n = b.u16()
    lines = []
    for _ in range(n):
        ws, we = b.u16(), b.u16()
        if ver == 1:
            cs, ce = b.rgba(), b.rgba()
            lines.append((dict(w=ws, c=cs, cap=0, join=0, miter=3),
                          dict(w=we, c=ce, cap=0, join=0, miter=3)))
        else:
            b.align()
            scap, join, hasfill = b.ub(2), b.ub(2), b.ub(1)
            b.ub(3)
            b.ub(5)
            b.ub(1)
            b.ub(2)
            miter = b.u16() / 256.0 if join == 2 else 3
            s = dict(w=ws, cap=scap, join=join, miter=miter)
            e = dict(w=we, cap=scap, join=join, miter=miter)
            if hasfill:
                s["fill"], e["fill"] = read_morph_fill(b)
            else:
                s["c"], e["c"] = b.rgba(), b.rgba()
            lines.append((s, e))
    return fills, lines


def parse_morph(code, d):
    ver = 1 if code == 46 else 2
    b = Bits(d)
    mid = b.u16()
    sb_, eb = b.rect(), b.rect()
    nonzero = False
    if ver == 2:
        b.rect()
        b.rect()
        nonzero = bool(b.u8() & 4)
    b.u32()
    fills, lines = read_morph_styles(b, ver)
    nf, nl = b.ub(4), b.ub(4)
    rs = read_records(b, nf, nl, 1)
    b.align()
    nf, nl = b.ub(4), b.ub(4)
    re_ = read_records(b, nf, nl, 1)
    recs = []
    j = 0
    for r in rs:
        if r[0] == "s":
            if r[1] is not None:
                while j < len(re_) and re_[j][0] != "s":
                    j += 1
                e = re_[j]
                j += 1
                recs.append(("s", r[1], e[1] or r[1], r[2], r[3], r[4], None))
            else:
                recs.append(("s", None, None, r[2], r[3], r[4], None))
        else:
            e = re_[j]
            j += 1
            recs.append(("e", r, e))
    return dict(id=mid, sb=sb_, eb=eb, fills=fills, lines=lines, recs=recs,
                nonzero=nonzero)


def to_q(r):
    if r[0] == "q":
        return r
    return ("q", r[1], r[2], (r[1] + r[3]) / 2.0, (r[2] + r[4]) / 2.0, r[3], r[4])


def lerp_fill(s, e, t):
    o = dict(s)
    if s["t"] == 0:
        o["c"] = lerp_col(s["c"], e["c"], t)
    if "m" in s:
        o["m"] = lerp_mat(s["m"], e["m"], t)
    if "g" in s:
        stops = [(int(round(lerp(a[0], b[0], t))), lerp_col(a[1], b[1], t))
                 for a, b in zip(s["g"]["stops"], e["g"]["stops"])]
        o["g"] = dict(s["g"], stops=stops, focal=lerp(s["g"]["focal"], e["g"]["focal"], t))
    return o


def lerp_line(s, e, t):
    o = dict(s)
    o["w"] = int(round(lerp(s["w"], e["w"], t)))
    if "c" in s:
        o["c"] = lerp_col(s["c"], e["c"], t)
    if "fill" in s:
        o["fill"] = lerp_fill(s["fill"], e["fill"], t)
    return o


def morph_geom(m, t):
    fills = [lerp_fill(s, e, t) for s, e in m["fills"]]
    lines = [lerp_line(s, e, t) for s, e in m["lines"]]
    recs = []
    for r in m["recs"]:
        if r[0] == "s":
            _, ms, me, f0, f1, ln, _ns = r
            mv = None
            if ms is not None:
                mv = (lerp(ms[0], me[0], t), lerp(ms[1], me[1], t))
            recs.append(("s", mv, f0, f1, ln, None))
        else:
            _, a, b = r
            if a[0] == "l" and b[0] == "l":
                recs.append(("l",) + tuple(lerp(x, y, t) for x, y in zip(a[1:], b[1:])))
            else:
                qa, qb = to_q(a), to_q(b)
                recs.append(("q",) + tuple(lerp(x, y, t) for x, y in zip(qa[1:], qb[1:])))
    bounds = tuple(lerp(x, y, t) for x, y in zip(m["sb"], m["eb"]))
    return (bounds, fills, lines, recs, m["nonzero"])


def _seg(e):
    if e[2] is None:
        return "L%s %s" % (fmt(e[4]), fmt(e[5]))
    return "Q%s %s %s %s" % (fmt(e[2]), fmt(e[3]), fmt(e[4]), fmt(e[5]))


def chain(edges, close):
    by = {}
    for e in edges:
        by.setdefault((e[0], e[1]), []).append(e)
    out = []
    for e in edges:
        if e[6]:
            continue
        e[6] = True
        sx, sy = e[0], e[1]
        parts = ["M%s %s" % (fmt(sx), fmt(sy))]
        cur = e
        while True:
            parts.append(_seg(cur))
            lst = by.get((cur[4], cur[5]))
            nxt = None
            while lst:
                c = lst.pop(0)
                if not c[6]:
                    nxt = c
                    break
            if nxt is None:
                break
            nxt[6] = True
            cur = nxt
        d = "".join(parts)
        if close or (cur[4], cur[5]) == (sx, sy):
            d += "Z"
        out.append(d)
    return "".join(out)


def paint(st, gid, ex):
    """-> (value, opacity, defs)"""
    t = st["t"]
    if t == 0:
        return hx(st["c"]), st["c"][3] / 255.0, ""
    tr = mat_str(st["m"])
    if t in (0x10, 0x12, 0x13):
        g = st["g"]
        stops = []
        for ratio, c in g["stops"]:
            op = ""
            if c[3] < 255:
                op = ' stop-opacity="%.3f"' % (c[3] / 255.0)
            stops.append('<stop offset="%.4f" stop-color="%s"%s/>' % (ratio / 255.0, hx(c), op))
        sp = ("pad", "reflect", "repeat")[min(g["spread"], 2)]
        common = 'id="%s" gradientUnits="userSpaceOnUse" gradientTransform="%s" spreadMethod="%s"' % (gid, tr, sp)
        if t == 0x10:
            d = '<linearGradient %s x1="-16384" y1="0" x2="16384" y2="0">%s</linearGradient>' % (common, "".join(stops))
        else:
            fx = ""
            if t == 0x13:
                fx = ' fx="%s" fy="0"' % fmt(g["focal"] * 16384)
            d = '<radialGradient %s cx="0" cy="0" r="16384"%s>%s</radialGradient>' % (common, fx, "".join(stops))
        return "url(#%s)" % gid, 1.0, d
    info = ex.image_uri(st["bmp"])
    if not info:
        return "#cccccc", 1.0, ""
    uri, w, h = info
    style = "" if t in (0x40, 0x41) else ' style="image-rendering:pixelated"'
    d = ('<pattern id="%s" patternUnits="userSpaceOnUse" width="%d" height="%d" patternTransform="%s">'
         '<image width="%d" height="%d" xlink:href="%s"%s/></pattern>') % (gid, w, h, tr, w, h, uri, style)
    return "url(#%s)" % gid, 1.0, d


def build_elems(geom, prefix, ex):
    _bounds, fills0, lines0, recs, _nz = geom
    groups = []

    def newg(fs, ls):
        g = dict(fs=fs, ls=ls, fe={}, le={})
        groups.append(g)
        return g

    cur = newg(fills0, lines0)
    f0 = f1 = ln = 0
    for r in recs:
        if r[0] == "s":
            _, _mv, nf0, nf1, nl, ns = r
            if ns is not None:
                cur = newg(*ns)
                f0 = f1 = ln = 0
            if nf0 is not None:
                f0 = nf0
            if nf1 is not None:
                f1 = nf1
            if nl is not None:
                ln = nl
            continue
        if r[0] == "l":
            if r[1] == r[3] and r[2] == r[4]:
                continue
            e = [r[1], r[2], None, None, r[3], r[4], False]
        else:
            e = [r[1], r[2], r[3], r[4], r[5], r[6], False]
        if f1:
            cur["fe"].setdefault(f1, []).append(list(e))
        if f0:
            cur["fe"].setdefault(f0, []).append([e[4], e[5], e[2], e[3], e[0], e[1], False])
        if ln:
            cur["le"].setdefault(ln, []).append(list(e))
    elems = []
    n = 0
    for g in groups:
        for idx in sorted(g["fe"]):
            if idx > len(g["fs"]):
                continue
            val, op, defs = paint(g["fs"][idx - 1], "%sf%d" % (prefix, n), ex)
            n += 1
            elems.append(dict(d=chain(g["fe"][idx], True), fill=(val, op), defs=defs, stroke=None))
        for idx in sorted(g["le"]):
            if idx > len(g["ls"]):
                continue
            st = g["ls"][idx - 1]
            if "fill" in st:
                val, op, defs = paint(st["fill"], "%sl%d" % (prefix, n), ex)
                n += 1
            else:
                val, op, defs = hx(st["c"]), st["c"][3] / 255.0, ""
            w = st["w"] or 20
            elems.append(dict(d=chain(g["le"][idx], False), fill=None, defs=defs,
                              stroke=(val, op, w, st["cap"], st["join"], st["miter"])))
    return elems


def elem_str(e, nonzero, anims=""):
    a = ['<path d="%s"' % e["d"]]
    if e["fill"]:
        val, op = e["fill"]
        a.append(' fill="%s"' % val)
        if op < 0.999:
            a.append(' fill-opacity="%.3f"' % op)
        if not nonzero:
            a.append(' fill-rule="evenodd"')
    else:
        a.append(' fill="none"')
    if e["stroke"]:
        val, op, w, cap, join, miter = e["stroke"]
        a.append(' stroke="%s" stroke-width="%s"' % (val, fmt(w)))
        a.append(' stroke-linecap="%s"' % ("round", "butt", "square")[min(cap, 2)])
        a.append(' stroke-linejoin="%s"' % ("round", "bevel", "miter")[min(join, 2)])
        if join == 2:
            a.append(' stroke-miterlimit="%s"' % fmt(miter))
        if op < 0.999:
            a.append(' stroke-opacity="%.3f"' % op)
    s = "".join(a)
    return e["defs"] + (s + ">" + anims + "</path>" if anims else s + "/>")


def skeleton(d):
    return re.sub(r"[-\d.]+", "", d)


def morph_animated(g0, g1, prefix, ex, dur):
    e0 = build_elems(g0, prefix, ex)
    e1 = build_elems(g1, prefix + "e", ex)
    if len(e0) != len(e1) or any(skeleton(a["d"]) != skeleton(b["d"]) for a, b in zip(e0, e1)):
        return None
    out = []
    for a, b in zip(e0, e1):
        an = ['<animate attributeName="d" values="%s;%s;%s" dur="%ss" repeatCount="indefinite"/>' % (a["d"], b["d"], a["d"], dur)]
        if a["fill"] and a["fill"][0][0] == "#" and a["fill"][0] != b["fill"][0]:
            an.append('<animate attributeName="fill" values="%s;%s;%s" dur="%ss" repeatCount="indefinite"/>' % (a["fill"][0], b["fill"][0], a["fill"][0], dur))
        if a["stroke"]:
            if a["stroke"][0][0] == "#" and a["stroke"][0] != b["stroke"][0]:
                an.append('<animate attributeName="stroke" values="%s;%s;%s" dur="%ss" repeatCount="indefinite"/>' % (a["stroke"][0], b["stroke"][0], a["stroke"][0], dur))
            if a["stroke"][2] != b["stroke"][2]:
                an.append('<animate attributeName="stroke-width" values="%s;%s;%s" dur="%ss" repeatCount="indefinite"/>' % (fmt(a["stroke"][2]), fmt(b["stroke"][2]), fmt(a["stroke"][2]), dur))
        out.append(elem_str(a, g0[4], "".join(an)))
    return "".join(out)


def contours(records):
    out = []
    cur = None
    pos = None
    for r in records:
        if r[0] == "s":
            if r[1] is not None:
                cur = [(r[1][0], r[1][1]), []]
                out.append(cur)
                pos = (r[1][0], r[1][1])
            continue
        if cur is None or pos != (r[1], r[2]):
            cur = [(r[1], r[2]), []]
            out.append(cur)
        if r[0] == "l":
            cur[1].append(("l", r[3], r[4]))
            pos = (r[3], r[4])
        else:
            cur[1].append(("q", r[3], r[4], r[5], r[6]))
            pos = (r[5], r[6])
    return out


def contours_d(records):
    parts = []
    for (sx, sy), segs in contours(records):
        if not segs:
            continue
        parts.append("M%s %s" % (fmt(sx), fmt(sy)))
        for s in segs:
            if s[0] == "l":
                parts.append("L%s %s" % (fmt(s[1]), fmt(s[2])))
            else:
                parts.append("Q%s %s %s %s" % (fmt(s[1]), fmt(s[2]), fmt(s[3]), fmt(s[4])))
        parts.append("Z")
    return "".join(parts)


def read_glyph(d, pos):
    b = Bits(d, pos)
    nf, nl = b.ub(4), b.ub(4)
    return read_records(b, nf, nl, 1)


def parse_font(code, d):
    b = Bits(d)
    fid = b.u16()
    f = dict(id=fid, code=code, name="", glyphs=[], codes=None, adv=None,
             ascent=None, descent=None, bold=False, italic=False, em=1024)
    if code == 10:
        start = b.pos()
        first = b.u16()
        n = first // 2
        offs = [first] + [b.u16() for _ in range(n - 1)]
        for o in offs:
            try:
                f["glyphs"].append(read_glyph(d, start + o))
            except Exception:
                f["glyphs"].append([])
        return f
    flags = b.u8()
    b.u8()
    nl = b.u8()
    f["name"] = b.bytes(nl).decode("utf-8", "replace").rstrip("\0")
    n = b.u16()
    wide_off = flags & 8
    wide_codes = flags & 4 or code == 75
    f["bold"], f["italic"] = bool(flags & 1), bool(flags & 2)
    if code == 75:
        f["em"] = 20480
    start = b.pos()
    offs = [b.u32() if wide_off else b.u16() for _ in range(n)]
    code_off = b.u32() if wide_off else b.u16()
    for o in offs:
        try:
            f["glyphs"].append(read_glyph(d, start + o))
        except Exception:
            f["glyphs"].append([])
    b.p = (start + code_off) * 8
    f["codes"] = [b.u16() if wide_codes else b.u8() for _ in range(n)]
    if flags & 0x80:
        f["ascent"], f["descent"] = b.s16(), b.s16()
        b.s16()
        f["adv"] = [b.s16() for _ in range(n)]
    return f


def parse_fontinfo(code, d):
    b = Bits(d)
    fid = b.u16()
    nl = b.u8()
    name = b.bytes(nl).decode("utf-8", "replace").rstrip("\0")
    flags = b.u8()
    if code == 62:
        b.u8()
    wide = flags & 1
    codes = []
    while b.left() >= (2 if wide else 1):
        codes.append(b.u16() if wide else b.u8())
    return fid, dict(name=name, codes=codes, bold=bool(flags & 1 and False))


def build_ttf(font):
    raise NotImplementedError("v2 build_ttf is not needed for tests")


def parse_text(d, v2):
    b = Bits(d)
    cid = b.u16()
    bounds = b.rect()
    mat = b.matrix()
    gb, ab = b.u8(), b.u8()
    recs = []
    font = None
    color = (0, 0, 0, 255)
    x = y = 0
    height = 240
    while True:
        flags = b.u8()
        if flags == 0:
            break
        if flags & 0x80:
            if flags & 8:
                font = b.u16()
            if flags & 4:
                color = b.rgba() if v2 else b.rgb() + (255,)
            if flags & 1:
                x = b.s16()
            if flags & 2:
                y = b.s16()
            if flags & 8:
                height = b.u16()
        else:
            glyphs = []
            for _ in range(flags & 0x7F):
                gi, adv = b.ub(gb), b.sb(ab)
                glyphs.append((gi, x))
                x += adv
            recs.append(dict(font=font, height=height, color=color, y=y, glyphs=glyphs))
    return dict(id=cid, bounds=bounds, matrix=mat, recs=recs)


def parse_edit(d):
    b = Bits(d)
    cid = b.u16()
    bounds = b.rect()
    f1, f2 = b.u8(), b.u8()
    o = dict(id=cid, bounds=bounds, html=bool(f2 & 2), text="", var="", font=None,
             fontclass="", height=240, color=(0, 0, 0, 255))
    if f1 & 1:
        o["font"] = b.u16()
    if f2 & 0x80:
        o["fontclass"] = b.cstr()
    if f1 & 1 or f2 & 0x80:
        o["height"] = b.u16()
    if f1 & 4:
        o["color"] = b.rgba()
    if f1 & 2:
        b.u16()
    if f2 & 0x20:
        b.bytes(9)
    o["var"] = b.cstr()
    if f1 & 0x80:
        o["text"] = b.cstr()
    if o["html"]:
        o["text"] = htmlmod.unescape(re.sub(r"<[^>]+>", "", o["text"]))
    return o


def skip_filters(b):
    n = b.u8()
    for _ in range(n):
        t = b.u8()
        if t == 0:
            b.bytes(23)
        elif t == 1:
            b.bytes(9)
        elif t == 2:
            b.bytes(15)
        elif t == 3:
            b.bytes(27)
        elif t in (4, 7):
            c = b.u8()
            b.bytes(5 * c + 19)
        elif t == 5:
            mx, my = b.u8(), b.u8()
            b.bytes(8 + 4 * mx * my + 5)
        elif t == 6:
            b.bytes(80)
        else:
            raise ValueError("unknown filter")


def do_place(code, d, disp, fidx):
    b = Bits(d)
    if code == 4:
        cid, depth = b.u16(), b.u16()
        m = b.matrix()
        cx = b.cxform(False) if b.left() > 0 else None
        disp[depth] = dict(id=cid, depth=depth, m=m, cx=cx, ratio=None, clip=0,
                           blend=None, vis=True, f0=fidx)
        return
    fl = b.u8()
    fl3 = b.u8() if code == 70 else 0
    depth = b.u16()
    if code == 70 and (fl3 & 8 or (fl3 & 0x10 and fl & 2)):
        b.cstr()
    cid = b.u16() if fl & 2 else None
    m = b.matrix() if fl & 4 else None
    cx = b.cxform(True) if fl & 8 else None
    ratio = b.u16() if fl & 16 else None
    if fl & 32:
        b.cstr()
    clip = b.u16() if fl & 64 else None
    blend = vis = None
    if code == 70:
        try:
            if fl3 & 1:
                skip_filters(b)
            if fl3 & 2:
                blend = b.u8()
            if fl3 & 4:
                b.u8()
            if fl3 & 32:
                vis = b.u8()
        except Exception:
            pass
    old = disp.get(depth)
    move = fl & 1
    if cid is not None and not move or (old is None and cid is not None):
        disp[depth] = dict(id=cid, depth=depth, m=m, cx=cx, ratio=ratio, clip=clip or 0,
                           blend=blend, vis=True if vis is None else bool(vis), f0=fidx)
        return
    if old is None:
        return
    o = dict(old)
    if cid is not None:
        o["id"], o["f0"] = cid, fidx
    if m is not None:
        o["m"] = m
    if cx is not None:
        o["cx"] = cx
    if ratio is not None:
        o["ratio"] = ratio
    if clip is not None:
        o["clip"] = clip
    if blend is not None:
        o["blend"] = blend
    if vis is not None:
        o["vis"] = bool(vis)
    disp[depth] = o


def build_timeline(tags):
    frames = []
    disp = {}
    labels = {}
    for code, d in tags:
        try:
            if code == 1:
                frames.append([dict(disp[k]) for k in sorted(disp)])
            elif code in (4, 26, 70):
                do_place(code, d, disp, len(frames))
            elif code == 5:
                disp.pop(u16(d, 2), None)
            elif code == 28:
                disp.pop(u16(d, 0), None)
            elif code == 43:
                labels[len(frames)] = Bits(d).cstr()
        except Exception as e:
            warn("timeline, tag %d: %s" % (code, e))
    if not frames and disp:
        frames.append([dict(disp[k]) for k in sorted(disp)])
    return frames, labels


def xf_box(b, m):
    pts = [(b[0], b[2]), (b[1], b[2]), (b[0], b[3]), (b[1], b[3])]
    xs = [m[0] * x + m[2] * y + m[4] for x, y in pts]
    ys = [m[1] * x + m[3] * y + m[5] for x, y in pts]
    return (min(xs), max(xs), min(ys), max(ys))


def union(a, b):
    if a is None:
        return b
    return (min(a[0], b[0]), max(a[1], b[1]), min(a[2], b[2]), max(a[3], b[3]))


def video_keyframe(codec, d):
    try:
        if codec == 2:
            return not ((int.from_bytes(d[:8], "big") >> (64 - 39)) & 1)
        if codec == 3:
            return (d[0] >> 4) == 1
        if codec == 4:
            return (d[1] & 0x80) == 0
        if codec == 5:
            return (d[4] & 0x80) == 0
    except Exception:
        pass
    return True


def build_flv(codec, frames, fps):
    out = bytearray(b"FLV\x01\x01\x00\x00\x00\x09\x00\x00\x00\x00")
    for num, data in sorted(frames, key=lambda f: f[0]):
        tag = bytes([(1 if video_keyframe(codec, data) else 2) << 4 | codec]) + data
        ts = int(num * 1000 / fps)
        out += (bytes([9]) + len(tag).to_bytes(3, "big") + (ts & 0xFFFFFF).to_bytes(3, "big") +
                bytes([(ts >> 24) & 0xFF]) + b"\0\0\0" + tag + (11 + len(tag)).to_bytes(4, "big"))
    return bytes(out)


def abc_strings(data):
    p = 4

    def u30():
        nonlocal p
        v = sh = 0
        while True:
            bt = data[p]
            p += 1
            v |= (bt & 0x7F) << sh
            sh += 7
            if not bt & 0x80:
                return v

    try:
        for _ in range(2):
            for _ in range(max(0, u30() - 1)):
                u30()
        for _ in range(max(0, u30() - 1)):
            p += 8
        out = []
        for _ in range(max(0, u30() - 1)):
            ln = u30()
            out.append(data[p:p + ln].decode("utf-8", "replace"))
            p += ln
        return out
    except Exception:
        return []


class Renderer:
    def __init__(self, ex):
        self.ex = ex
        self.defs = []
        self.have = set()
        self.n = 0
        self.cxc = {}

    def uid(self, p):
        self.n += 1
        return "%s%d" % (p, self.n)

    def shape(self, cid, q=None):
        did = "s%d" % cid + ("" if q is None else "_%d" % q)
        if did not in self.have:
            self.have.add(did)
            inner, _ = self.ex.shape_svg(cid, q)
            self.defs.append('<g id="%s">%s</g>' % (did, inner))
        return did

    def text(self, cid):
        did = "t%d" % cid
        if did not in self.have:
            self.have.add(did)
            self.defs.append('<g id="%s">%s</g>' % (did, self.ex.text_inner(cid)[0]))
        return did

    def sprite(self, cid, k, depth):
        did = "p%d_%d" % (cid, k)
        if did not in self.have:
            self.have.add(did)
            body = self.frame(cid, k, depth)
            self.defs.append('<g id="%s">%s</g>' % (did, body))
        return did

    def cx_attrs(self, cx):
        rm, gm, bm, am, ra, ga, ba, aa = cx
        if (rm, gm, bm, am) == (1, 1, 1, 1) and ra == ga == ba == aa == 0:
            return ""
        if (rm, gm, bm) == (1, 1, 1) and ra == ga == ba == aa == 0 and am <= 1:
            return ' opacity="%.3f"' % max(0.0, am)
        key = tuple(cx)
        if key not in self.cxc:
            fid = self.uid("cx")
            self.cxc[key] = fid
            vals = "%s 0 0 0 %s 0 %s 0 0 %s 0 0 %s 0 %s 0 0 0 %s %s" % (
                fm(rm), fm(ra / 255.0), fm(gm), fm(ga / 255.0), fm(bm), fm(ba / 255.0),
                fm(am), fm(aa / 255.0))
            self.defs.append('<filter id="%s" color-interpolation-filters="sRGB">'
                             '<feColorMatrix type="matrix" values="%s"/></filter>' % (fid, vals))
        return ' filter="url(#%s)"' % self.cxc[key]

    def item(self, it, f, depth):
        if depth > 12 or it.get("vis") is False:
            return ""
        cid = it["id"]
        kind = self.ex.kind(cid)
        attrs = ""
        m = it.get("m")
        if m and tuple(m) != IDENT:
            attrs += ' transform="%s"' % mat_str(m)
        if it.get("cx"):
            attrs += self.cx_attrs(it["cx"])
        bl = BLEND.get(it.get("blend"))
        if bl:
            attrs += ' style="mix-blend-mode:%s"' % bl
        if kind == "shape":
            return '<use xlink:href="#%s"%s/>' % (self.shape(cid), attrs)
        if kind == "morph":
            q = int(round((it.get("ratio") or 0) / 65535.0 * 16))
            return '<use xlink:href="#%s"%s/>' % (self.shape(cid, q), attrs)
        if kind == "text":
            return '<use xlink:href="#%s"%s/>' % (self.text(cid), attrs)
        if kind == "edit":
            return "<g%s>%s</g>" % (attrs, self.ex.edit_svg(cid))
        if kind == "sprite":
            n = len(self.ex.timeline(cid)[0])
            if n == 0:
                return ""
            k = (f - it.get("f0", 0)) % n if n > 1 else 0
            return '<use xlink:href="#%s"%s/>' % (self.sprite(cid, k, depth + 1), attrs)
        return ""

    def frame(self, tid, f, depth=0):
        frames = self.ex.timeline(tid)[0]
        if not frames:
            return ""
        items = frames[min(f, len(frames) - 1)]
        out = []
        i = 0
        while i < len(items):
            it = items[i]
            if it.get("clip"):
                cd = it["clip"]
                d = self.ex.clip_d(it["id"])
                j = i + 1
                inner = []
                while j < len(items) and items[j]["depth"] <= cd:
                    inner.append(self.item(items[j], f, depth))
                    j += 1
                body = "".join(inner)
                if d:
                    cid = self.uid("c")
                    tr = ""
                    if it.get("m") and tuple(it["m"]) != IDENT:
                        tr = ' transform="%s"' % mat_str(it["m"])
                    self.defs.append('<clipPath id="%s"><path d="%s"%s clip-rule="evenodd"/></clipPath>' % (cid, d, tr))
                    out.append('<g clip-path="url(#%s)">%s</g>' % (cid, body))
                else:
                    out.append(body)
                i = j
            else:
                out.append(self.item(it, f, depth))
                i += 1
        return "".join(out)

    def document(self, bbox, body, bg=None):
        x0, x1, y0, y1 = bbox
        if x1 - x0 < 1 or y1 - y0 < 1:
            x1, y1 = x0 + 20, y0 + 20
        w, h = (x1 - x0) / 20.0, (y1 - y0) / 20.0
        head = ('<?xml version="1.0" encoding="UTF-8"?>\n'
                '<svg xmlns="http://www.w3.org/2000/svg" xmlns:xlink="http://www.w3.org/1999/xlink" '
                'width="%s" height="%s" viewBox="%s %s %s %s">' %
                (fmt(w), fmt(h), fmt(x0 / 20.0), fmt(y0 / 20.0), fmt(w), fmt(h)))
        bgs = ""
        if bg:
            bgs = '<rect x="%s" y="%s" width="%s" height="%s" fill="%s"/>' % (
                fmt(x0 / 20.0), fmt(y0 / 20.0), fmt(w), fmt(h), hx(bg))
        return "%s<defs>%s</defs>%s<g transform=\"scale(0.05)\">%s</g></svg>\n" % (
            head, "".join(self.defs), bgs, body)


def anim_body(strs, fps):
    segs = []
    for i, s in enumerate(strs):
        if segs and segs[-1][0] == s:
            segs[-1][2] += 1
        else:
            segs.append([s, i, 1])
    n = len(strs)
    if len(segs) == 1:
        return "<g>%s</g>" % segs[0][0]
    dur = n / fps
    out = []
    for s, start, cnt in segs:
        a, b = start / n, (start + cnt) / n
        if start == 0:
            vals, kt = "visible;hidden", "0;%.5f" % b
        elif start + cnt >= n:
            vals, kt = "hidden;visible", "0;%.5f" % a
        else:
            vals, kt = "hidden;visible;hidden", "0;%.5f;%.5f" % (a, b)
        out.append('<g visibility="hidden">%s<animate attributeName="visibility" values="%s" '
                   'keyTimes="%s" dur="%.4fs" calcMode="discrete" repeatCount="indefinite"/></g>'
                   % (s, vals, kt, dur))
    return "".join(out)


class Extractor:
    def __init__(self, swf, raw=False):
        self.swf = swf
        self.raw = raw
        self.fps = swf["fps"]
        self.assets = []
        self.names = {}
        self.jpeg_tables = b""
        self.imgs = {}
        self.streams = []
        self.cur_stream = None
        self.shapes, self.morphs = {}, {}
        self.fontdefs, self.fontinfo, self.fontnames = {}, {}, {}
        self.texts, self.edits, self.sprites = {}, {}, {}
        self.videos, self.vframes = {}, {}
        self.main_tags = []
        self.bg = None
        self.meta = ""
        self.hist = {}
        self._ps, self._pm, self._fonts, self._tl = {}, {}, {}, {}
        self._svgc, self._uri, self._bb = {}, {}, {}

    def add(self, kind, cid, ext, data, tag, label=None):
        self.assets.append(dict(kind=kind, id=cid, ext=ext, data=data, tag=tag, label=label))
        if kind == "images" and cid is not None and ext in ("png", "jpg", "gif"):
            self.imgs[cid] = (ext, data)

    def feed(self):
        for code, d in iter_tags(self.swf["body"], self.swf["pos"]):
            nm = TAGNAMES.get(code, "Tag%d" % code)
            self.hist[nm] = self.hist.get(nm, 0) + 1
            if code in TIMELINE:
                self.main_tags.append((code, d))
            try:
                self.handle(code, d)
            except Exception as e:
                warn("tag %s: %s" % (nm, e))

    def handle(self, code, d):
        if code == 8:
            self.jpeg_tables = d
        elif code == 6:
            img = merge_jpeg_tables(self.jpeg_tables, d[2:])
            self.add("images", u16(d, 0), sniff_image(img), img, code)
        elif code == 21:
            img = fix_jpeg(d[2:])
            self.add("images", u16(d, 0), sniff_image(img), img, code)
        elif code in (35, 90):
            cid, off = u16(d, 0), u32(d, 2)
            start = 6 if code == 35 else 8
            img = fix_jpeg(d[start:start + off])
            alpha = d[start + off:]
            if alpha:
                try:
                    alpha = zlib.decompress(alpha)
                except zlib.error:
                    pass
            ext = sniff_image(img)
            if ext == "jpg" and alpha and Image:
                im = Image.open(io.BytesIO(img)).convert("RGB")
                if len(alpha) == im.width * im.height:
                    im.putalpha(Image.frombytes("L", im.size, bytes(alpha)))
                    buf = io.BytesIO()
                    im.save(buf, "PNG")
                    self.add("images", cid, "png", buf.getvalue(), code)
                    return
            self.add("images", cid, ext, img, code)
            if ext == "jpg" and alpha:
                self.add("images", cid, "alpha.bin", bytes(alpha), code)
        elif code in (20, 36):
            cid, png = decode_lossless(d, code == 36)
            self.add("images", cid, "png", png, code)
        elif code == 14:
            cid, fl = u16(d, 0), d[2]
            fmt_, rate = fl >> 4, RATES[(fl >> 2) & 3]
            bits, ch = (16 if fl & 2 else 8), (2 if fl & 1 else 1)
            count = u32(d, 3)
            data = d[7:]
            if fmt_ == 2:
                data = data[2:]
            ext, payload = sound_payload(fmt_, rate, bits, ch, [data], count)
            self.add("sounds", cid, ext, payload, code)
        elif code in (18, 45):
            fl = d[1]
            self.cur_stream = dict(fmt=fl >> 4, rate=RATES[(fl >> 2) & 3],
                                   bits=16 if fl & 2 else 8, ch=2 if fl & 1 else 1, blocks=[])
            self.streams.append(self.cur_stream)
        elif code == 19 and self.cur_stream is not None:
            s = self.cur_stream
            s["blocks"].append(d[4:] if s["fmt"] == 2 else d)
        elif code == 87:
            cid, data = u16(d, 0), d[6:]
            ext = "swf" if data[:3] in (b"FWS", b"CWS", b"ZWS") else None
            if not ext:
                if data[:4] == b"\x89PNG":
                    ext = "png"
                elif data[:2] == b"\xff\xd8":
                    ext = "jpg"
                elif data[:5] == b"<?xml":
                    ext = "xml"
                elif data[:4] == b"OggS":
                    ext = "ogg"
                else:
                    ext = "bin"
            self.add("binary", cid, ext, data, code)
        elif code in (82, 72):
            label = None
            data = d
            if code == 82:
                label, p = Bits(d, 4).cstr(), 0
                data = d[4 + len(label.encode("utf-8")) + 1:]
            self.add("scripts", None, "abc", data, code, label)
            st = abc_strings(data)
            if st:
                self.add("scripts", None, "strings.txt",
                         "\n".join(s.replace("\n", "\\n") for s in st).encode("utf-8"), code, label)
        elif code == 12 or (self.raw and code in RAW_TAGS):
            self.add("scripts" if code == 12 else "raw", None if code == 12 else u16(d, 0),
                     "action.bin" if code == 12 else RAW_TAGS[code] + ".bin", d, code)
        elif code in (76, 56):
            n, p = u16(d, 0), 2
            b = Bits(d, 2)
            for _ in range(n):
                cid = b.u16()
                name = b.cstr()
                if cid or code == 56:
                    self.names.setdefault(cid, name)
        elif code == 9:
            self.bg = tuple(d[:3])
        elif code == 77:
            self.meta = d.split(b"\0")[0].decode("utf-8", "replace")
        elif code in (2, 22, 32, 83):
            self.shapes[u16(d, 0)] = (code, d)
        elif code in (46, 84):
            self.morphs[u16(d, 0)] = (code, d)
        elif code in (10, 48, 75, 91):
            self.fontdefs[u16(d, 0)] = (code, d)
        elif code in (13, 62):
            fid, info = parse_fontinfo(code, d)
            self.fontinfo[fid] = info
        elif code == 88:
            self.fontnames[u16(d, 0)] = Bits(d, 2).cstr()
        elif code in (11, 33):
            self.texts[u16(d, 0)] = (code, d)
        elif code == 37:
            self.edits[u16(d, 0)] = d
        elif code == 39:
            sid, nfr = u16(d, 0), u16(d, 2)
            tags = list(iter_tags(d, 4))
            self.sprites[sid] = dict(frames=nfr, tags=tags)
            for c, dd in tags:
                if c in (18, 45, 19):
                    self.handle(c, dd)
        elif code == 60:
            self.videos[u16(d, 0)] = dict(n=u16(d, 2), w=u16(d, 4), h=u16(d, 6), codec=d[9])
        elif code == 61:
            self.vframes.setdefault(u16(d, 0), []).append((u16(d, 2), d[4:]))
        if self.raw and code in (2, 22, 32, 83, 46, 84, 10, 48, 75, 91, 11, 33, 37):
            self.add("raw", u16(d, 0), "%s.bin" % TAGNAMES.get(code, code), d, code)

    def kind(self, cid):
        if cid in self.shapes:
            return "shape"
        if cid in self.morphs:
            return "morph"
        if cid in self.sprites:
            return "sprite"
        if cid in self.texts:
            return "text"
        if cid in self.edits:
            return "edit"
        return None

    def image_uri(self, cid):
        if cid in self._uri:
            return self._uri[cid]
        r = None
        if cid in self.imgs:
            ext, data = self.imgs[cid]
            w, h = img_size(ext, data)
            if w and h:
                mime = {"png": "image/png", "jpg": "image/jpeg", "gif": "image/gif"}[ext]
                r = ("data:%s;base64,%s" % (mime, base64.b64encode(data).decode()), w, h)
        self._uri[cid] = r
        return r

    def parsed_shape(self, sid):
        if sid not in self._ps:
            self._ps[sid] = parse_shape(*self.shapes[sid])
        return self._ps[sid]

    def morph(self, sid):
        if sid not in self._pm:
            self._pm[sid] = parse_morph(*self.morphs[sid])
        return self._pm[sid]

    def shape_geom(self, sid, q=None):
        if sid in self.shapes:
            p = self.parsed_shape(sid)
            return (p["bounds"], p["fills"], p["lines"], p["records"], p["nonzero"])
        return morph_geom(self.morph(sid), (q or 0) / 16.0)

    def shape_svg(self, sid, q=None):
        key = (sid, q)
        if key not in self._svgc:
            geom = self.shape_geom(sid, q)
            prefix = "g%d%s_" % (sid, "" if q is None else "q%d" % q)
            elems = build_elems(geom, prefix, self)
            inner = "".join(elem_str(e, geom[4]) for e in elems)
            clip = "".join(e["d"] for e in elems if e["fill"])
            self._svgc[key] = (inner, clip)
        return self._svgc[key]

    def clip_d(self, cid):
        if self.kind(cid) in ("shape", "morph"):
            return self.shape_svg(cid, None if cid in self.shapes else 0)[1]
        return None

    def font(self, fid):
        if fid in self._fonts:
            return self._fonts[fid]
        f = None
        if fid in self.fontdefs and self.fontdefs[fid][0] != 91:
            try:
                f = parse_font(*self.fontdefs[fid])
                info = self.fontinfo.get(fid)
                if info:
                    if not f["codes"]:
                        f["codes"] = info["codes"]
                    if not f["name"]:
                        f["name"] = info["name"]
                if not f["name"]:
                    f["name"] = self.fontnames.get(fid, "")
            except Exception as e:
                warn("font %s: %s" % (fid, e))
        self._fonts[fid] = f
        return f

    def timeline(self, tid):
        if tid not in self._tl:
            tags = self.main_tags if tid is None else self.sprites[tid]["tags"]
            self._tl[tid] = build_timeline(tags)
        return self._tl[tid]

    def char_bounds(self, cid, seen):
        k = self.kind(cid)
        if k == "shape":
            return self.parsed_shape(cid)["bounds"]
        if k == "morph":
            m = self.morph(cid)
            return union(m["sb"], m["eb"])
        if k == "text":
            return parse_text(self.texts[cid][1], self.texts[cid][0] == 33)["bounds"]
        if k == "edit":
            return parse_edit(self.edits[cid])["bounds"]
        if k == "sprite" and cid not in seen:
            return self.bbox(cid, seen)
        return None

    def bbox(self, tid, seen=()):
        if tid in self._bb:
            return self._bb[tid]
        box = None
        done = set()
        for items in self.timeline(tid)[0]:
            for it in items:
                key = (it["id"], tuple(it["m"]) if it.get("m") else None)
                if key in done:
                    continue
                done.add(key)
                try:
                    b = self.char_bounds(it["id"], seen + (tid,))
                except Exception:
                    b = None
                if b is None:
                    continue
                box = union(box, xf_box(b, it.get("m") or IDENT))
        self._bb[tid] = box
        return box

    def text_inner(self, cid):
        code, d = self.texts[cid]
        t = parse_text(d, code == 33)
        parts = []
        for rec in t["recs"]:
            f = self.font(rec["font"])
            if not f:
                continue
            sc = rec["height"] / float(f["em"])
            col = rec["color"]
            op = ""
            if col[3] < 255:
                op = ' fill-opacity="%.3f"' % (col[3] / 255.0)
            for gi, gx in rec["glyphs"]:
                if gi >= len(f["glyphs"]):
                    continue
                dd = contours_d(f["glyphs"][gi])
                if dd:
                    parts.append('<path transform="translate(%s %s) scale(%.6f)" d="%s" fill="%s"%s/>' % (
                        fmt(gx), fmt(rec["y"]), sc, dd, hx(col), op))
        return '<g transform="%s">%s</g>' % (mat_str(t["matrix"]), "".join(parts)), t

    def text_strings(self, cid):
        code, d = self.texts[cid]
        t = parse_text(d, code == 33)
        lines = []
        for rec in t["recs"]:
            f = self.font(rec["font"])
            s = ""
            for gi, _ in rec["glyphs"]:
                c = f["codes"][gi] if f and f["codes"] and gi < len(f["codes"]) else 0
                s += chr(c) if c else "?"
            lines.append(s)
        return lines

    def edit_svg(self, cid):
        o = parse_edit(self.edits[cid])
        if not o["text"]:
            return ""
        x0, _, y0, _ = o["bounds"]
        return '<text x="%d" y="%d" font-size="%d" font-family="sans-serif" fill="%s">%s</text>' % (
            x0 + 40, y0 + 40 + int(o["height"] * 0.85), o["height"], hx(o["color"]),
            htmlmod.escape(o["text"]))

    def save(self, outdir, only, want_frames, max_frames):
        os.makedirs(outdir, exist_ok=True)
        manifest = []
        taken = set()
        counters = {}

        def out(kind, cid, ext, data, label=None, tag=None):
            if isinstance(data, str):
                data = data.encode("utf-8")
            if cid is None:
                counters[kind] = counters.get(kind, 0) + 1
                base = "%03d" % counters[kind]
            else:
                base = str(cid)
            if label is None and isinstance(cid, int):
                label = self.names.get(cid)
            name = "%s_%s" % (base, safe(label)) if label else base
            d = os.path.join(outdir, kind)
            os.makedirs(d, exist_ok=True)
            fn, k = "%s.%s" % (name, ext), 1
            while (kind, fn) in taken:
                k += 1
                fn = "%s_%d.%s" % (name, k, ext)
            taken.add((kind, fn))
            with open(os.path.join(d, fn), "wb") as fh:
                fh.write(data)
            manifest.append(dict(file="%s/%s" % (kind, fn), kind=kind, id=cid,
                                 symbol=label, tag=tag, size=len(data)))

        for i, s in enumerate(self.streams):
            if s["blocks"] and "sounds" in only:
                try:
                    ext, payload = sound_payload(s["fmt"], s["rate"], s["bits"], s["ch"], s["blocks"])
                    self.add("sounds", "stream%d" % i, ext, payload, 19)
                except Exception as e:
                    warn("stream %d: %s" % (i, e))
        for a in self.assets:
            if a["kind"] in only or a["kind"] == "raw":
                out(a["kind"], a["id"], a["ext"], a["data"], a.get("label"), a["tag"])

        def guard(what, fn):
            try:
                fn()
            except Exception as e:
                warn("%s: %s" % (what, e))

        if "shapes" in only:
            for sid in sorted(self.shapes):
                def f(sid=sid):
                    r = Renderer(self)
                    inner, _ = self.shape_svg(sid)
                    out("shapes", sid, "svg", r.document(self.parsed_shape(sid)["bounds"], inner), tag=self.shapes[sid][0])
                guard("shape %d" % sid, f)

        if "morphs" in only:
            for sid in sorted(self.morphs):
                def f(sid=sid):
                    m = self.morph(sid)
                    g0, g1 = morph_geom(m, 0.0), morph_geom(m, 1.0)
                    bb = union(m["sb"], m["eb"])
                    r = Renderer(self)
                    body = morph_animated(g0, g1, "m%d_" % sid, self, 2)
                    if body is None:
                        for tag, g in (("start", g0), ("end", g1)):
                            inner = "".join(elem_str(e, g[4]) for e in build_elems(g, "m%d%s_" % (sid, tag), self))
                            out("morphs", "%d_%s" % (sid, tag), "svg", Renderer(self).document(bb, inner), label=self.names.get(sid))
                    else:
                        out("morphs", sid, "svg", r.document(bb, body), tag=self.morphs[sid][0])
                guard("morph %d" % sid, f)

        if "fonts" in only:
            for fid in sorted(self.fontdefs):
                def f(fid=fid):
                    code, d = self.fontdefs[fid]
                    if code == 91:
                        b = Bits(d, 2)
                        fl = b.u8()
                        name = b.cstr()
                        if fl & 4:
                            out("fonts", fid, "cff", d[b.pos():], label=name, tag=code)
                        return
                    ft = self.font(fid)
                    if ft and ft["glyphs"]:
                        out("fonts", fid, "ttf", build_ttf(ft), label=ft["name"] or None, tag=code)
                guard("font %d" % fid, f)

        if "texts" in only:
            for tid in sorted(self.texts):
                def f(tid=tid):
                    inner, t = self.text_inner(tid)
                    out("texts", tid, "svg", Renderer(self).document(t["bounds"], inner), tag=self.texts[tid][0])
                    out("texts", tid, "txt", "\n".join(self.text_strings(tid)), tag=self.texts[tid][0])
                guard("text %d" % tid, f)
            for tid in sorted(self.edits):
                def f(tid=tid):
                    o = parse_edit(self.edits[tid])
                    lines = ["variable: %s" % o["var"], "font: %s" % (o["fontclass"] or o["font"]),
                             "size: %s" % (o["height"] / 20.0), "", o["text"]]
                    out("texts", tid, "txt", "\n".join(lines), tag=37)
                guard("edittext %d" % tid, f)

        if "video" in only:
            for vid, frames in sorted(self.vframes.items()):
                v = self.videos.get(vid)
                if v and frames:
                    guard("video %d" % vid, lambda v=v, vid=vid, frames=frames: out(
                        "video", vid, "flv", build_flv(v["codec"], frames, self.fps), tag=61))

        if "sprites" in only or want_frames:
            targets = [(sid, False) for sid in sorted(self.sprites)] + [(None, True)]
            for sid, is_main in targets:
                def f(sid=sid, is_main=is_main):
                    frames = self.timeline(sid)[0]
                    if not frames:
                        return
                    box = self.swf["rect"] if is_main else self.bbox(sid)
                    if box is None:
                        return
                    n = min(len(frames), max_frames)
                    r = Renderer(self)
                    strs = [r.frame(sid, i) for i in range(n)]
                    if not any(strs):
                        return
                    bg = self.bg if is_main else None
                    cid = "main" if is_main else sid
                    if "sprites" in only:
                        out("sprites", cid, "svg", r.document(box, anim_body(strs, self.fps), bg),
                            tag=39)
                    if want_frames and n > 1:
                        for i, s in enumerate(strs):
                            out("frames", "%s_%04d" % (cid, i + 1), "svg", r.document(box, "<g>%s</g>" % s, bg))
                guard("sprite %s" % ("main" if is_main else sid), f)

        r = self.swf["rect"]
        info = dict(tool="swf_extract %s" % __version__, version=self.swf["version"],
                    compression=self.swf["sig"], stage_px=[(r[1] - r[0]) / 20.0, (r[3] - r[2]) / 20.0],
                    fps=self.fps, frames=self.swf["nframes"], tags=self.hist,
                    symbols={str(k): v for k, v in self.names.items()},
                    frame_labels={str(k): v for k, v in self.timeline(None)[1].items()},
                    metadata=self.meta)
        with open(os.path.join(outdir, "info.json"), "w", encoding="utf-8") as fh:
            json.dump(info, fh, ensure_ascii=False, indent=2)
        with open(os.path.join(outdir, "manifest.json"), "w", encoding="utf-8") as fh:
            json.dump(manifest, fh, ensure_ascii=False, indent=2)
        return manifest


def collect(inputs):
    files = []
    for p in inputs:
        if os.path.isdir(p):
            for root, _, names in os.walk(p):
                files += [os.path.join(root, n) for n in sorted(names) if n.lower().endswith(".swf")]
        elif os.path.exists(p):
            files.append(p)
        else:
            files += sorted(glob.glob(p))
    return files
'''))
_EMBEDDED.append(('swf_decomp', r'''"""
swf_decomp - shared control-flow structurer and ActionScript 1/2 decompiler.

The Structurer works for both AS2 and AS3: it recovers
if / else / while / do-while / for-in / break / continue / try / ternary / && / ||
from a flat list of instructions. Anything that cannot be recovered is left as a comment
`// goto` - code is never lost.
"""
import bisect
import json
import re
import struct

IDENT = re.compile(r"^[A-Za-z_$][\w$]*(\.[A-Za-z_$][\w$]*)*$")


class E:
    __slots__ = ("s", "prec", "neg", "lit", "call", "scope", "hn", "ext")

    def __init__(self, s, prec=99, neg=None, lit=None, call=False, scope=False):
        self.s, self.prec, self.neg, self.lit = s, prec, neg, lit
        self.call, self.scope, self.hn, self.ext = call, scope, None, None

    def __repr__(self):
        return self.s


def wrap(e, p):
    return "(%s)" % e.s if e.prec < p else e.s


def qstr(s):
    return json.dumps(s, ensure_ascii=False)


def negate(e):
    if e.neg is not None:
        return e.neg
    return E("!" + wrap(e, 13), 13, neg=e)


def binop(a, op, b, prec):
    return E("%s %s %s" % (wrap(a, prec), op, wrap(b, prec + 1)), prec)


def cmp_e(a, op, b, prec, inv=None):
    e = binop(a, op, b, prec)
    if inv:
        i = binop(a, inv, b, prec)
        e.neg, i.neg = i, e
    return e


def and_e(a, b):
    return E("%s && %s" % (wrap(a, 4), wrap(b, 5)), 4)


def or_e(a, b):
    return E("%s || %s" % (wrap(a, 3), wrap(b, 4)), 3)


def strip_par(s):
    if s.startswith("(") and s.endswith(")"):
        d = 0
        for i, c in enumerate(s):
            d += c == "("
            d -= c == ")"
            if d == 0 and i < len(s) - 1:
                return s
        return s[1:-1]
    return s


def indent(lines, n=1):
    pad = "    " * n
    out = []
    for l in lines:
        for sub in l.split("\n"):
            out.append(pad + sub if sub else sub)
    return out


class Ins:
    __slots__ = ("addr", "nxt", "op", "name", "args", "kind", "target", "targets", "body", "ext")

    def __init__(self, addr, nxt, op, name, args=None, kind="op", target=None):
        self.addr, self.nxt, self.op, self.name = addr, nxt, op, name
        self.args = args if args is not None else []
        self.kind, self.target = kind, target
        self.targets = self.body = self.ext = None


class Structurer:
    """sim: object with .stack, .out, .exec(ins), .take_cond(ins), .snapshot(), .restore(s),
    .loop_hook(cond, body_lines) -> lines or None, .begin_catch(info)."""

    def __init__(self, ins, sim, tries=None):
        self.ins, self.sim, self.n = ins, sim, len(ins)
        self.addrs = [x.addr for x in ins]
        self.endaddr = ins[-1].nxt if ins else 0
        self.tries = tries or []
        self.tstart = {}
        for t in self.tries:
            self.tstart.setdefault(t["from"], []).append(t)
        self.done_try = set()
        self.active = set()
        self.loops = {}
        for j, x in enumerate(ins):
            if x.kind in ("jmp", "cjmp") and x.target is not None and x.target <= x.addr:
                h = self.idx(x.target)
                if h not in self.loops or self.loops[h][0] < j:
                    self.loops[h] = (j, "while" if x.kind == "jmp" else "do")

    def idx(self, addr):
        if addr >= self.endaddr:
            return self.n
        return bisect.bisect_left(self.addrs, addr)

    def addr_of(self, i):
        return self.ins[i].addr if i < self.n else self.endaddr

    def read_cond(self, i):
        """-> (loop body entry condition, last cjmp index, skip target index)"""
        ins, sim = self.ins, self.sim
        T = self.idx(ins[i].target)
        taken = sim.take_cond(ins[i])
        enter, last = negate(taken), i
        nxt = self.peek_cjmp(i + 1)
        if nxt is not None and self.idx(ins[i].target) == nxt[0] + 1 and nxt[0] > i:
            k, snap = nxt
            self.commit(i + 1, k)
            t2 = sim.take_cond(ins[k])
            return or_e(taken, negate(t2)), k, self.idx(ins[k].target)
        while True:
            nxt = self.peek_cjmp(last + 1)
            if nxt is None or self.idx(ins[nxt[0]].target) != T or ins[nxt[0]].target <= ins[nxt[0]].addr:
                break
            k = nxt[0]
            self.commit(last + 1, k)
            enter = and_e(enter, negate(sim.take_cond(ins[k])))
            last = k
        return enter, last, T

    def peek_cjmp(self, start):
        """Looks for a cjmp past "pure" instructions (no statements). -> (k, None) or None."""
        ins, sim = self.ins, self.sim
        k = start
        snap = sim.snapshot()
        try:
            while k < self.n and ins[k].kind == "op":
                before = len(sim.out)
                sim.exec(ins[k])
                if len(sim.out) != before:
                    return None
                k += 1
            if k < self.n and ins[k].kind == "cjmp":
                return (k, None)
            return None
        finally:
            sim.restore(snap)

    def commit(self, a, b):
        for k in range(a, b):
            self.sim.exec(self.ins[k])

    def block(self, i, end, ctx):
        sim = self.sim
        saved = sim.out
        sim.out = []
        try:
            self._block(i, end, ctx)
            return sim.out
        finally:
            sim.out = saved

    def sub(self, i, end, ctx):
        return self.block(i, end, ctx)

    def try_switch_as2(self, i, end, ctx):
        """AS2 switch (Flash CS3+): StoreRegister r; (Push c; StrictEquals; If Lk)+; Jump Ldefault/Lend.
        -> index of the instruction after the switch, or None if the pattern did not match."""
        ins, sim, n = self.ins, self.sim, self.n
        if not sim.stack:
            return None
        reg = ins[i].args[0]
        k, cases, first = i + 1, [], True
        while k + 2 < n:
            p, eq, cj = ins[k], ins[k + 1], ins[k + 2]
            if p.op != 0x96 or eq.op != 0x66 or cj.kind != "cjmp" or cj.target is None or cj.target <= cj.addr:
                break
            a = p.args
            if first:
                if len(a) != 1 or a[0][0] == "reg":
                    break
            elif len(a) != 2 or a[0] != ("reg", reg):
                break
            cases.append((k, cj.target))
            k += 3
            first = False
        if len(cases) < 2 or k >= n or ins[k].kind != "jmp" or ins[k].target is None or ins[k].target <= ins[k].addr:
            return None
        tgts = [self.idx(t) for _, t in cases]
        dflt = self.idx(ins[k].target)
        if tgts != sorted(tgts) or tgts[0] <= k or dflt <= k or dflt > end or tgts[-1] > end:
            return None
        starts = sorted(set(tgts + [dflt]))
        cands = {}
        for b in starts[1:]:
            j = ins[b - 1]
            if j.kind == "jmp" and j.target is not None and j.target > j.addr and self.idx(j.target) >= dflt:
                c = self.idx(j.target)
                cands[c] = cands.get(c, 0) + 1
        lend = max(cands, key=lambda c: (cands[c], -c)) if cands else dflt
        if lend > end or lend < starts[-1] and lend != dflt:
            return None
        # case values: execute Push on a copy of the stack
        vals = []
        for kk, _ in cases:
            snap = sim.snapshot()
            try:
                sim.exec(ins[kk])
                vals.append(strip_par(sim.stack[-1].s))
            finally:
                sim.restore(snap)
        subj = strip_par(sim.stack[-1].s)
        sim.stack.pop()
        base = list(sim.stack)
        bounds = [b for b in starts if b < lend] + [lend]
        c = {"break": self.addr_of(lend), "cont": None}
        text = ["switch (%s) {" % subj]
        for si in range(len(bounds) - 1):
            a, b = bounds[si], bounds[si + 1]
            labels = ["case %s:" % vals[ci] for ci, t in enumerate(tgts) if t == a]
            if a == dflt and lend != dflt:
                labels.append("default:")
            sim.stack = list(base)
            body = self.sub(a, b, ctx + [c])
            if si == len(bounds) - 2 and body and body[-1] == "break;":
                body = body[:-1]
            text += indent(labels) + indent(body, 2)
        text.append("}")
        sim.stack = list(base)
        sim.out.append("\n".join(text))
        return lend

    def _block(self, i, end, ctx):
        ins, sim = self.ins, self.sim
        while i < end:
            if i in self.tstart:
                grp = [t for t in self.tstart[i] if id(t) not in self.done_try]
                if grp:
                    i = self.do_try(i, end, ctx, grp)
                    continue
            x = ins[i]
            if x.kind == "op" and x.op == 0x87 and getattr(sim, "is_as2", False):
                r = self.try_switch_as2(i, end, ctx)
                if r is not None:
                    i = r
                    continue
            if x.kind == "jmp" and x.target > x.addr and (i + 1) in self.loops \
                    and self.loops[i + 1][1] == "do" and (i + 1) not in self.active:
                t = self.idx(x.target)
                j = self.loops[i + 1][0]
                if i + 1 < t <= j:
                    i = self.while_bottom(i, t, j, ctx)
                    continue
            if i in self.loops and i not in self.active:
                i = self.do_loop(i, end, ctx)
                continue
            if x.kind == "op" or x.kind == "ret":
                sim.exec(x)
                i += 1
            elif x.kind == "jmp":
                i = self.do_jmp(i, end, ctx)
            elif x.kind == "cjmp":
                i = self.do_if(i, end, ctx)
            elif x.kind == "sw":
                i = self.do_switch(i, end, ctx)
            else:
                sim.exec(x)
                i += 1
        return i

    def do_jmp(self, i, end, ctx):
        x = self.ins[i]
        t = x.target
        for c in reversed(ctx):
            if t == c["break"]:
                self.sim.out.append("break;")
                return i + 1
            if t == c["cont"]:
                self.sim.out.append("continue;")
                return i + 1
        if t == x.nxt:
            return i + 1
        if t != self.addr_of(end):
            self.sim.out.append("// goto L%d;" % t)
        return i + 1

    def do_if(self, i, end, ctx):
        ins, sim = self.ins, self.sim
        x = ins[i]
        for c in reversed(ctx):
            if x.target in (c["break"], c["cont"]):
                taken = sim.take_cond(x)
                sim.out.append("if (%s) {\n    %s\n}" % (strip_par(taken.s),
                               "break;" if x.target == c["break"] else "continue;"))
                return i + 1
        if x.target <= x.addr:
            sim.exec(x)
            return i + 1
        cond, last, T = self.read_cond(i)
        if T > end or T <= last:
            sim.out.append("if (%s) { /* jump outside the block L%d */ }" % (strip_par(cond.s), ins[last].target))
            return last + 1
        base = list(sim.stack)
        e_idx = None
        jl = ins[T - 1] if T - 1 > last else None
        if jl is not None and jl.kind == "jmp" and jl.target > jl.addr:
            brk = any(jl.target in (c["break"], c["cont"]) for c in ctx)
            ei = self.idx(jl.target)
            if not brk and T < ei <= end:
                e_idx = ei
        if e_idx is None:
            then = self.sub(last + 1, T, ctx)
            st_then = sim.stack
            sim.stack = list(st_then)
            if base and not then and len(st_then) == len(base) and st_then[-1] is not base[-1]:
                a = base[-1]
                if cond.s == a.s:
                    sim.stack = base[:-1] + [and_e(a, st_then[-1])]
                    return T
                if negate(cond).s == a.s:
                    sim.stack = base[:-1] + [or_e(a, st_then[-1])]
                    return T
            if then:
                sim.out.append("if (%s) {\n%s\n}" % (strip_par(cond.s), "\n".join(indent(then))))
            return T
        sim.stack = list(base)
        then = self.sub(last + 1, T - 1, ctx)
        st_t = sim.stack
        sim.stack = list(base)
        els = self.sub(T, e_idx, ctx)
        st_e = sim.stack
        if not then and not els and len(st_t) == len(base) + 1 and len(st_e) == len(base) + 1:
            sim.stack = base + [E("%s ? %s : %s" % (wrap(cond, 3), wrap(st_t[-1], 3), wrap(st_e[-1], 3)), 2)]
            return e_idx
        sim.stack = st_t if len(st_t) >= len(st_e) else st_e
        txt = "if (%s) {\n%s\n}" % (strip_par(cond.s), "\n".join(indent(then)))
        if els:
            if len(els) == 1 and els[0].startswith("if ("):
                txt += " else " + els[0]
            else:
                txt += " else {\n%s\n}" % "\n".join(indent(els))
        sim.out.append(txt)
        return e_idx

    def loop_text(self, cond, body, kind="while"):
        sim = self.sim
        hook = getattr(sim, "loop_hook", None)
        if hook:
            r = hook(cond, body)
            if r is not None:
                return r
        return "while (%s) {\n%s\n}" % (strip_par(cond.s), "\n".join(indent(body)))

    def while_bottom(self, i, t, j, ctx):
        ins, sim = self.ins, self.sim
        h = i + 1
        self.active.add(h)
        c = {"break": self.addr_of(j + 1), "cont": ins[t].addr}
        body = self.sub(h, t, ctx + [c])
        saved_out = sim.out
        sim.out = []
        cond = None
        k = t
        while k <= j:
            while k < j and ins[k].kind == "op":
                sim.exec(ins[k])
                k += 1
            if k == j:
                fin = sim.take_cond(ins[k])
                cond = fin if cond is None else and_e(cond, fin)
                break
            if ins[k].kind == "cjmp" and self.idx(ins[k].target) == j + 1:
                cc = negate(sim.take_cond(ins[k]))
                cond = cc if cond is None else and_e(cond, cc)
                k += 1
            else:
                sim.exec(ins[k])
                k += 1
        sim.out = saved_out
        self.active.discard(h)
        if cond is None:
            cond = E("true")
        sim.out.append(self.loop_text(cond, body))
        return j + 1

    def do_loop(self, i, end, ctx):
        ins, sim = self.ins, self.sim
        j, kind = self.loops[i]
        if j >= end + 0 and j > end:
            sim.exec(ins[i]) if ins[i].kind == "op" else None
            self.active.add(i)
            return i + 1 if ins[i].kind == "op" else i + 1
        self.active.add(i)
        try:
            c = {"break": self.addr_of(j + 1), "cont": ins[i].addr}
            if kind == "do":
                body = self.sub(i, j, ctx + [c])
                cond = sim.take_cond(ins[j])
                sim.out.append("do {\n%s\n} while (%s);" % ("\n".join(indent(body)), strip_par(cond.s)))
                return j + 1
            snap = sim.snapshot()
            n0 = len(sim.out)
            k = i
            while k < j and ins[k].kind == "op":
                sim.exec(ins[k])
                k += 1
            ok = (k < j and ins[k].kind == "cjmp" and ins[k].target > ins[j].addr and len(sim.out) == n0)
            if ok:
                cond, last, T = self.read_cond(k)
                body = self.sub(last + 1, j, ctx + [c])
                sim.out.append(self.loop_text(cond, body))
                return j + 1
            sim.restore(snap)
            del sim.out[n0:]
            body = self.sub(i, j, ctx + [c])
            sim.out.append("while (true) {\n%s\n}" % "\n".join(indent(body)))
            return j + 1
        finally:
            self.active.discard(i)

    def do_switch(self, i, end, ctx):
        x = self.ins[i]
        v = self.sim.stack.pop() if self.sim.stack else E("?")
        self.sim.out.append("// lookupswitch (%s): default -> L%d, cases -> %s" % (
            strip_par(v.s), x.target, ", ".join("L%d" % t for t in (x.targets or []))))
        return i + 1

    def do_try(self, i, end, ctx, grp):
        ins, sim = self.ins, self.sim
        to = max(g["to"] for g in grp)
        for g in grp:
            self.done_try.add(id(g))
        to_i = min(self.idx(to), end)
        fin_i, body_end = to_i, to_i
        for k in (to_i, to_i - 1):
            if i <= k < self.n and ins[k].kind == "jmp" and ins[k].target > ins[k].addr:
                fin_i = min(self.idx(ins[k].target), end)
                body_end = k
                break
        body = self.sub(i, body_end, ctx)
        hs = sorted(grp, key=lambda g: g["target"])
        txt = "try {\n%s\n}" % "\n".join(indent(body))
        for n, g in enumerate(hs):
            h0 = self.idx(g["target"])
            h1 = self.idx(hs[n + 1]["target"]) if n + 1 < len(hs) else fin_i
            h1 = min(max(h1, h0), end)
            sim.begin_catch(g)
            cb = self.sub(h0, h1, ctx)
            if g.get("type") in (None, "", "*") and g is hs[-1] and not g.get("var"):
                txt += " finally {\n%s\n}" % "\n".join(indent(cb))
            else:
                txt += " catch (%s%s) {\n%s\n}" % (g.get("var") or "e",
                                                    (":" + g["type"]) if g.get("type") else "",
                                                    "\n".join(indent(cb)))
        sim.out.append(txt)
        return max(fin_i, to_i)


AS2_NAMES = {
    0x04: "NextFrame", 0x05: "PreviousFrame", 0x06: "Play", 0x07: "Stop", 0x08: "ToggleQuality",
    0x09: "StopSounds", 0x0A: "Add", 0x0B: "Subtract", 0x0C: "Multiply", 0x0D: "Divide",
    0x0E: "Equals", 0x0F: "Less", 0x10: "And", 0x11: "Or", 0x12: "Not", 0x13: "StringEquals",
    0x14: "StringLength", 0x15: "StringExtract", 0x17: "Pop", 0x18: "ToInteger",
    0x1C: "GetVariable", 0x1D: "SetVariable", 0x20: "SetTarget2", 0x21: "StringAdd",
    0x22: "GetProperty", 0x23: "SetProperty", 0x24: "CloneSprite", 0x25: "RemoveSprite",
    0x26: "Trace", 0x27: "StartDrag", 0x28: "EndDrag", 0x29: "StringLess", 0x2A: "Throw",
    0x2B: "CastOp", 0x2C: "ImplementsOp", 0x30: "RandomNumber", 0x31: "MBStringLength",
    0x32: "CharToAscii", 0x33: "AsciiToChar", 0x34: "GetTime", 0x35: "MBStringExtract",
    0x36: "MBCharToAscii", 0x37: "MBAsciiToChar", 0x3A: "Delete", 0x3B: "Delete2",
    0x3C: "DefineLocal", 0x3D: "CallFunction", 0x3E: "Return", 0x3F: "Modulo",
    0x40: "NewObject", 0x41: "DefineLocal2", 0x42: "InitArray", 0x43: "InitObject",
    0x44: "TypeOf", 0x45: "TargetPath", 0x46: "Enumerate", 0x47: "Add2", 0x48: "Less2",
    0x49: "Equals2", 0x4A: "ToNumber", 0x4B: "ToString", 0x4C: "PushDuplicate",
    0x4D: "StackSwap", 0x4E: "GetMember", 0x4F: "SetMember", 0x50: "Increment",
    0x51: "Decrement", 0x52: "CallMethod", 0x53: "NewMethod", 0x54: "InstanceOf",
    0x55: "Enumerate2", 0x60: "BitAnd", 0x61: "BitOr", 0x62: "BitXor", 0x63: "BitLShift",
    0x64: "BitRShift", 0x65: "BitURShift", 0x66: "StrictEquals", 0x67: "Greater",
    0x68: "StringGreater", 0x69: "Extends",
    0x81: "GotoFrame", 0x83: "GetURL", 0x87: "StoreRegister", 0x88: "ConstantPool",
    0x8A: "WaitForFrame", 0x8B: "SetTarget", 0x8C: "GotoLabel", 0x8D: "WaitForFrame2",
    0x8E: "DefineFunction2", 0x8F: "Try", 0x94: "With", 0x96: "Push", 0x99: "Jump",
    0x9A: "GetURL2", 0x9B: "DefineFunction", 0x9D: "If", 0x9E: "Call", 0x9F: "GotoFrame2",
}
PROPS = ["_x", "_y", "_xscale", "_yscale", "_currentframe", "_totalframes", "_alpha", "_visible",
         "_width", "_height", "_rotation", "_target", "_framesloaded", "_name", "_droptarget",
         "_url", "_highquality", "_focusrect", "_soundbuftime", "_quality", "_xmouse", "_ymouse"]


def _cstr(d, p):
    e = d.find(b"\0", p)
    if e < 0:
        e = len(d)
    return d[p:e].decode("utf-8", "replace"), e + 1


def parse_actions(data, start=0, end=None):
    end = len(data) if end is None else end
    p, res = start, []
    while p < end:
        a, op = p, data[p]
        p += 1
        if op == 0:
            break
        name = AS2_NAMES.get(op, "Unknown_%02X" % op)
        args, kind, target = [], "op", None
        ins = Ins(a, 0, op, name)
        if op >= 0x80:
            if p + 2 > end:
                break
            ln = struct.unpack_from("<H", data, p)[0]
            p += 2
            pl = data[p:p + ln]
            p += ln
            if op == 0x96:
                q = 0
                while q < len(pl):
                    t = pl[q]
                    q += 1
                    if t == 0:
                        s, q = _cstr(pl, q)
                        args.append(("str", s))
                    elif t == 1:
                        args.append(("float", struct.unpack_from("<f", pl, q)[0]))
                        q += 4
                    elif t == 2:
                        args.append(("null", None))
                    elif t == 3:
                        args.append(("undef", None))
                    elif t == 4:
                        args.append(("reg", pl[q]))
                        q += 1
                    elif t == 5:
                        args.append(("bool", bool(pl[q])))
                        q += 1
                    elif t == 6:
                        hi, lo = struct.unpack_from("<II", pl, q)
                        args.append(("float", struct.unpack("<d", struct.pack("<II", lo, hi))[0]))
                        q += 8
                    elif t == 7:
                        args.append(("int", struct.unpack_from("<i", pl, q)[0]))
                        q += 4
                    elif t == 8:
                        args.append(("const", pl[q]))
                        q += 1
                    elif t == 9:
                        args.append(("const", struct.unpack_from("<H", pl, q)[0]))
                        q += 2
                    else:
                        break
            elif op == 0x88:
                n = struct.unpack_from("<H", pl, 0)[0]
                q, pool = 2, []
                for _ in range(n):
                    s, q = _cstr(pl, q)
                    pool.append(s)
                args = pool
            elif op in (0x99, 0x9D):
                off = struct.unpack_from("<h", pl, 0)[0]
                target, kind = p + off, ("jmp" if op == 0x99 else "cjmp")
            elif op == 0x9B:
                nm, q = _cstr(pl, 0)
                n = struct.unpack_from("<H", pl, q)[0]
                q += 2
                params = []
                for _ in range(n):
                    s, q = _cstr(pl, q)
                    params.append(s)
                size = struct.unpack_from("<H", pl, q)[0]
                ins.body = data[p:p + size]
                p += size
                args = [nm, params, None, 0]
            elif op == 0x8E:
                nm, q = _cstr(pl, 0)
                n, regs, flags = struct.unpack_from("<HBH", pl, q)
                q += 5
                params = []
                for _ in range(n):
                    r = pl[q]
                    s, q = _cstr(pl, q + 1)
                    params.append((r, s))
                size = struct.unpack_from("<H", pl, q)[0]
                ins.body = data[p:p + size]
                p += size
                args = [nm, params, regs, flags]
            elif op == 0x8F:
                fl = pl[0]
                ts, cs, fs = struct.unpack_from("<HHH", pl, 1)
                q = 7
                cname = None
                if fl & 4:
                    cname = ("reg", pl[q])
                else:
                    cname, q = _cstr(pl, q)
                ins.body = (data[p:p + ts], data[p + ts:p + ts + cs], data[p + ts + cs:p + ts + cs + fs])
                p += ts + cs + fs
                args = [fl, cname]
            elif op == 0x94:
                size = struct.unpack_from("<H", pl, 0)[0]
                ins.body = data[p:p + size]
                p += size
            elif op == 0x81:
                args = [struct.unpack_from("<H", pl, 0)[0]]
            elif op == 0x83:
                u, q = _cstr(pl, 0)
                t, q = _cstr(pl, q)
                args = [u, t]
            elif op == 0x8A:
                args = [struct.unpack_from("<H", pl, 0)[0], pl[2]]
            elif op in (0x8B, 0x8C):
                args = [_cstr(pl, 0)[0]]
            elif op in (0x8D, 0x9A):
                args = [pl[0]]
            elif op == 0x87:
                args = [pl[0]]
            elif op == 0x9F:
                fl = pl[0]
                args = [fl, struct.unpack_from("<H", pl, 1)[0] if fl & 2 else 0]
        ins.nxt, ins.kind, ins.target, ins.args = p, kind, target, args
        res.append(ins)
    return res


def _fmt_push(a, pool):
    t, v = a
    if t == "str":
        return qstr(v)
    if t == "const":
        return qstr(pool[v]) if v < len(pool) else "const%d" % v
    if t == "reg":
        return "reg%d" % v
    return {"null": "null", "undef": "undefined"}.get(t) or (str(v).lower() if t == "bool" else repr(v))


def disasm_as2(data, pool=None, ind=0):
    pool = list(pool or [])
    out = []
    for x in parse_actions(data):
        a = ""
        if x.op == 0x96:
            a = ", ".join(_fmt_push(v, pool) for v in x.args)
        elif x.op == 0x88:
            pool = x.args
            a = ", ".join(qstr(s) for s in x.args)
        elif x.kind in ("jmp", "cjmp"):
            a = "L%d" % x.target
        elif x.op in (0x9B, 0x8E):
            a = "%s(%s)" % (x.args[0], ", ".join(p if isinstance(p, str) else "%s=r%d" % (p[1], p[0]) for p in x.args[1]))
        elif x.args:
            a = ", ".join(repr(v) for v in x.args)
        out.append("%s%04X: %s %s" % ("    " * ind, x.addr, x.name, a))
        if x.body is not None:
            bodies = x.body if isinstance(x.body, tuple) else (x.body,)
            for b in bodies:
                out.append("    " * ind + "  {")
                out += disasm_as2(b, pool, ind + 2)
                out.append("    " * ind + "  }")
    return out


def _var(e):
    if e.lit is not None and IDENT.match(e.lit):
        return e.lit
    return "eval(%s)" % e.s


class AS2Sim:
    is_as2 = True
    def __init__(self, pool=None, regs=None):
        self.pool = list(pool or [])
        self.regs = dict(regs or {})
        self.stack, self.out = [], []
        self.declared = set()

    def snapshot(self):
        return (list(self.stack), len(self.out))

    def restore(self, s):
        self.stack = list(s[0])
        del self.out[s[1]:]

    def begin_catch(self, g):
        pass

    def pop(self):
        return self.stack.pop() if self.stack else E("undefined /*stack*/")

    def push(self, e):
        self.stack.append(e)

    def reg(self, n):
        return self.regs.get(n) or "_reg%d" % n

    def take_cond(self, ins):
        return self.pop()

    def call(self, fn, args):
        return E("%s(%s)" % (fn, ", ".join(strip_par(a.s) for a in args)), 14, call=True)

    def stmt(self, s):
        self.out.append(s + ";")

    def func(self, ins):
        nm, params, regs, flags = ins.args
        sub_regs = {}
        pnames = []
        if ins.op == 0x8E:
            r = 1
            for bit, nme in ((0x01, "this"), (0x04, "arguments"), (0x10, "super"), (0x40, "_root"),
                             (0x80, "_parent"), (0x100, "_global")):
                if flags & bit:
                    sub_regs[r] = nme
                    r += 1
            for rg, pn in params:
                pnames.append(pn)
                if rg:
                    sub_regs[rg] = pn
        else:
            pnames = list(params)
        body = decompile_as2(ins.body, self.pool, sub_regs)
        txt = "function %s(%s) {\n%s\n}" % (nm, ", ".join(pnames), "\n".join(indent(body)))
        return nm, txt

    def exec(self, x):
        op, n = x.op, x.name
        P = self.pop
        if op == 0x96:
            for t, v in x.args:
                if t == "str":
                    self.push(E(qstr(v), lit=v))
                elif t == "const":
                    s = self.pool[v] if v < len(self.pool) else "const%d" % v
                    self.push(E(qstr(s), lit=s))
                elif t == "reg":
                    self.push(E(self.reg(v)))
                elif t == "null":
                    self.push(E("null"))
                elif t == "undef":
                    self.push(E("undefined"))
                elif t == "bool":
                    self.push(E("true" if v else "false"))
                else:
                    s = repr(v)
                    if t == "float" and v == int(v) and abs(v) < 1e15:
                        s = str(int(v))
                    self.push(E(s, 13 if s.startswith("-") else 99))
        elif op == 0x88:
            self.pool = x.args
        elif op == 0x17:
            e = P()
            if e.call:
                self.stmt(strip_par(e.s))
        elif op in (0x0A, 0x47):
            b, a = P(), P()
            self.push(binop(a, "+", b, 11))
        elif op == 0x0B:
            b, a = P(), P()
            self.push(binop(a, "-", b, 11))
        elif op == 0x0C:
            b, a = P(), P()
            self.push(binop(a, "*", b, 12))
        elif op == 0x0D:
            b, a = P(), P()
            self.push(binop(a, "/", b, 12))
        elif op == 0x3F:
            b, a = P(), P()
            self.push(binop(a, "%", b, 12))
        elif op in (0x0E, 0x49):
            b, a = P(), P()
            self.push(cmp_e(a, "==", b, 8, "!="))
        elif op == 0x66:
            b, a = P(), P()
            self.push(cmp_e(a, "===", b, 8, "!=="))
        elif op == 0x13:
            b, a = P(), P()
            self.push(cmp_e(a, "eq", b, 8, "ne"))
        elif op in (0x0F, 0x48, 0x29):
            b, a = P(), P()
            self.push(binop(a, "<", b, 9))
        elif op in (0x67, 0x68):
            b, a = P(), P()
            self.push(binop(a, ">", b, 9))
        elif op == 0x10:
            b, a = P(), P()
            self.push(and_e(a, b))
        elif op == 0x11:
            b, a = P(), P()
            self.push(or_e(a, b))
        elif op == 0x12:
            self.push(negate(P()))
        elif op == 0x60:
            b, a = P(), P(); self.push(binop(a, "&", b, 7))
        elif op == 0x61:
            b, a = P(), P(); self.push(binop(a, "|", b, 5))
        elif op == 0x62:
            b, a = P(), P(); self.push(binop(a, "^", b, 6))
        elif op == 0x63:
            b, a = P(), P(); self.push(binop(a, "<<", b, 10))
        elif op == 0x64:
            b, a = P(), P(); self.push(binop(a, ">>", b, 10))
        elif op == 0x65:
            b, a = P(), P(); self.push(binop(a, ">>>", b, 10))
        elif op == 0x54:
            b, a = P(), P(); self.push(binop(a, "instanceof", b, 9))
        elif op == 0x2B:
            b, a = P(), P(); self.push(E("%s(%s)" % (_var(b), strip_par(a.s)), 14))
        elif op == 0x21:
            b, a = P(), P(); self.push(binop(a, "+", b, 11))
        elif op == 0x14 or op == 0x31:
            self.push(E("%s.length" % wrap(P(), 14), 14))
        elif op == 0x15 or op == 0x35:
            c, i, s = P(), P(), P()
            self.push(self.call("%s.substr" % wrap(s, 14), [i, c]))
        elif op == 0x18:
            self.push(self.call("int", [P()]))
        elif op == 0x4A:
            self.push(self.call("Number", [P()]))
        elif op == 0x4B:
            self.push(self.call("String", [P()]))
        elif op == 0x44:
            self.push(E("typeof " + wrap(P(), 13), 13))
        elif op == 0x45:
            self.push(self.call("targetPath", [P()]))
        elif op == 0x50:
            self.push(binop(P(), "+", E("1"), 11))
        elif op == 0x51:
            self.push(binop(P(), "-", E("1"), 11))
        elif op == 0x4C:
            e = self.stack[-1] if self.stack else E("undefined")
            self.push(e)
        elif op == 0x4D:
            if len(self.stack) >= 2:
                self.stack[-1], self.stack[-2] = self.stack[-2], self.stack[-1]
        elif op == 0x1C:
            self.push(E(_var(P())))
        elif op == 0x1D:
            v, nme = P(), P()
            self.stmt("%s = %s" % (_var(nme), strip_par(v.s)))
        elif op == 0x3C:
            v, nme = P(), P()
            self.stmt("var %s = %s" % (nme.lit or _var(nme), strip_par(v.s)))
        elif op == 0x41:
            nme = P()
            self.stmt("var %s" % (nme.lit or _var(nme)))
        elif op == 0x4E:
            nme, o = P(), P()
            self.push(self.member(o, nme))
        elif op == 0x4F:
            v, nme, o = P(), P(), P()
            self.stmt("%s = %s" % (self.member(o, nme).s, strip_par(v.s)))
        elif op == 0x3A:
            nme, o = P(), P()
            self.push(E("delete " + self.member(o, nme).s, 13, call=True))
        elif op == 0x3B:
            nme = P()
            self.push(E("delete " + _var(nme), 13, call=True))
        elif op == 0x22:
            i, t = P(), P()
            idx = int(float(i.s)) if re.match(r"^-?[\d.]+$", i.s) else None
            pn = PROPS[idx] if idx is not None and 0 <= idx < len(PROPS) else "prop(%s)" % i.s
            self.push(E(pn if t.lit == "" else "%s.%s" % (_var(t), pn), 14))
        elif op == 0x23:
            v, i, t = P(), P(), P()
            idx = int(float(i.s)) if re.match(r"^-?[\d.]+$", i.s) else None
            pn = PROPS[idx] if idx is not None and 0 <= idx < len(PROPS) else "prop(%s)" % i.s
            self.stmt("%s%s = %s" % ("" if t.lit == "" else _var(t) + ".", pn, strip_par(v.s)))
        elif op == 0x3D:
            nme, c = P(), P()
            args = [P() for _ in range(self.cnt(c))]
            self.push(self.call(_var(nme), args))
        elif op == 0x52:
            nme, o, c = P(), P(), P()
            args = [P() for _ in range(self.cnt(c))]
            if nme.s in ("undefined", '""'):
                self.push(self.call(wrap(o, 14), args))
            else:
                self.push(self.call(self.member(o, nme).s, args))
        elif op == 0x40:
            nme, c = P(), P()
            args = [P() for _ in range(self.cnt(c))]
            self.push(E("new %s(%s)" % (_var(nme), ", ".join(strip_par(a.s) for a in args)), 14, call=True))
        elif op == 0x53:
            nme, o, c = P(), P(), P()
            args = [P() for _ in range(self.cnt(c))]
            f = _var(o) if nme.s in ("undefined", '""') else self.member(o, nme).s
            self.push(E("new %s(%s)" % (f, ", ".join(strip_par(a.s) for a in args)), 14, call=True))
        elif op == 0x42:
            c = P()
            items = [P() for _ in range(self.cnt(c))]
            self.push(E("[%s]" % ", ".join(strip_par(a.s) for a in items)))
        elif op == 0x43:
            c = P()
            kv = []
            for _ in range(self.cnt(c)):
                v, k = P(), P()
                kv.append("%s: %s" % (k.lit if k.lit and IDENT.match(k.lit) else k.s, strip_par(v.s)))
            self.push(E("{%s}" % ", ".join(kv)))
        elif op == 0x87:
            v = P()
            nm = self.reg(x.args[0])
            if v.s == "__next__":
                self.push(E(nm))
            else:
                self.push(E("%s = %s" % (nm, strip_par(v.s)), 1, call=True))
        elif op == 0x3E:
            self.stmt("return " + strip_par(P().s))
        elif op == 0x2A:
            self.stmt("throw " + strip_par(P().s))
        elif op in (0x9B, 0x8E):
            nm, txt = self.func(x)
            if nm:
                self.out.append(txt)
            else:
                self.push(E(txt, 99, call=False))
        elif op == 0x94:
            tgt = P()
            body = decompile_as2(x.body, self.pool, self.regs)
            self.out.append("with (%s) {\n%s\n}" % (strip_par(tgt.s), "\n".join(indent(body))))
        elif op == 0x8F:
            fl, cname = x.args
            tb, cb, fb = x.body
            txt = "try {\n%s\n}" % "\n".join(indent(decompile_as2(tb, self.pool, self.regs)))
            if fl & 1:
                cn = self.reg(cname[1]) if isinstance(cname, tuple) else cname
                txt += " catch (%s) {\n%s\n}" % (cn, "\n".join(indent(decompile_as2(cb, self.pool, self.regs))))
            if fl & 2:
                txt += " finally {\n%s\n}" % "\n".join(indent(decompile_as2(fb, self.pool, self.regs)))
            self.out.append(txt)
        elif op in (0x46, 0x55):
            o = P()
            self.push(E("null"))
            self.enum_obj = _var(o) if op == 0x46 else strip_par(o.s)
            self.push(E("__next__"))
        elif op in (0x4, 0x5, 0x6, 0x7, 0x8, 0x9):
            self.stmt({4: "nextFrame()", 5: "prevFrame()", 6: "play()", 7: "stop()",
                       8: "toggleHighQuality()", 9: "stopAllSounds()"}[op])
        elif op == 0x81:
            self.stmt("gotoAndStop(%d)" % (x.args[0] + 1))
        elif op == 0x8C:
            self.stmt("gotoAndStop(%s)" % qstr(x.args[0]))
        elif op == 0x9F:
            f = P()
            play = x.args[0] & 1
            self.stmt("%s(%s)" % ("gotoAndPlay" if play else "gotoAndStop", strip_par(f.s)))
        elif op == 0x83:
            self.stmt("getURL(%s, %s)" % (qstr(x.args[0]), qstr(x.args[1])))
        elif op == 0x9A:
            t, u = P(), P()
            self.stmt("getURL(%s, %s /*flags %d*/)" % (strip_par(u.s), strip_par(t.s), x.args[0]))
        elif op == 0x8B:
            self.stmt("tellTarget(%s) /* setTarget */" % qstr(x.args[0]))
        elif op == 0x20:
            self.stmt("tellTarget(%s) /* setTarget2 */" % strip_par(P().s))
        elif op == 0x26:
            self.stmt("trace(%s)" % strip_par(P().s))
        elif op == 0x9E:
            self.stmt("call(%s)" % strip_par(P().s))
        elif op == 0x24:
            d, tg, s = P(), P(), P()
            self.stmt("duplicateMovieClip(%s, %s, %s)" % tuple(strip_par(v.s) for v in (s, tg, d)))
        elif op == 0x25:
            self.stmt("removeMovieClip(%s)" % strip_par(P().s))
        elif op == 0x27:
            c = P()
            lock, tg = P(), P()
            args = [tg, lock]
            if c.s not in ("0", "false"):
                args += [P() for _ in range(4)][::-1]
            self.stmt("startDrag(%s)" % ", ".join(strip_par(a.s) for a in args))
        elif op == 0x28:
            self.stmt("stopDrag()")
        elif op == 0x30:
            self.push(self.call("random", [P()]))
        elif op in (0x32, 0x36):
            self.push(E("%s.charCodeAt(0)" % wrap(P(), 14), 14))
        elif op in (0x33, 0x37):
            self.push(self.call("String.fromCharCode", [P()]))
        elif op == 0x34:
            self.push(self.call("getTimer", []))
        elif op == 0x69:
            b, a = P(), P()
            self.stmt("%s extends %s" % (strip_par(a.s), strip_par(b.s)))
        elif op == 0x2C:
            c = P()
            items = [P() for _ in range(self.cnt(c))]
            self.stmt("implements %s" % ", ".join(strip_par(a.s) for a in items))
        elif op in (0x8A, 0x8D, 0x8, 0x9):
            if op == 0x8D:
                P()
            self.out.append("// %s %s" % (x.name, x.args))
        else:
            self.out.append("// %s %s" % (x.name, x.args or ""))

    def cnt(self, c):
        try:
            return int(float(c.s))
        except Exception:
            return 0

    def member(self, o, nme):
        if nme.lit is not None and IDENT.match(nme.lit) and "." not in nme.lit:
            return E("%s.%s" % (wrap(o, 14), nme.lit), 14)
        return E("%s[%s]" % (wrap(o, 14), strip_par(nme.s)), 14)

    def loop_hook(self, cond, body):
        m = re.match(r"^(\S+) != null$", strip_par(cond.s))
        if not m or not body:
            return None
        mm = re.match(r"^(.+?) = %s;$" % re.escape(m.group(1)), body[0])
        if not mm:
            return None
        obj = getattr(self, "enum_obj", "?")
        return "for (%s in %s) {\n%s\n}" % (mm.group(1), obj, "\n".join(indent(body[1:])))


def decompile_as2(data, pool=None, regs=None):
    """-> list of lines"""
    ins = parse_actions(data)
    if not ins:
        return []
    sim = AS2Sim(pool, regs)
    fixed = []
    i = 0
    while i < len(ins):
        x = ins[i]
        if x.op == 0x87 and i + 1 < len(ins) and ins[i + 1].op == 0x17:
            x.ext = "store_pop"
        fixed.append(x)
        i += 1
    orig_exec = sim.exec

    def exec_(x):
        if x.ext == "store_pop":
            v = sim.pop()
            nm = sim.reg(x.args[0])
            sim.stmt("%s = %s" % (nm, strip_par(v.s)))
            sim.skip_pop = True
            return
        if x.op == 0x17 and getattr(sim, "skip_pop", False):
            sim.skip_pop = False
            return
        orig_exec(x)
    sim.exec = exec_
    try:
        st = Structurer(fixed, sim)
        lines = st.block(0, len(fixed), [])
        for e in sim.stack:
            if e.call:
                lines.append(strip_par(e.s) + ";")
        return lines
    except Exception as ex:
        return ["// could not structure (%s); disassembly:" % ex] + ["// " + l for l in disasm_as2(data, pool)]
'''))
_EMBEDDED.append(('swf_extra', r'''"""swf_extra - helper modules with no dependency on swf_extract_v2:
SWF filters -> SVG, SMIL helpers, matrix decomposition, TTF/OTF building, FLV audio, HTML in TextField."""
import html as htmlmod
import io
import math
import re
import struct
from html.parser import HTMLParser


def fnum(v):
    s = ("%.5f" % v).rstrip("0").rstrip(".")
    return "0" if s in ("", "-0") else s


def parse_filters(d, p):
    """FILTERLIST from PlaceObject3 / buttons. -> (list of dicts, new position)"""
    n = d[p]
    p += 1
    res = []
    rgba = lambda q: tuple(d[q:q + 4])
    fx = lambda q: struct.unpack_from("<i", d, q)[0] / 65536.0
    for _ in range(n):
        t = d[p]
        p += 1
        if t == 0:
            col = rgba(p)
            bx, by, ang, dist = fx(p + 4), fx(p + 8), fx(p + 12), fx(p + 16)
            st = struct.unpack_from("<h", d, p + 20)[0] / 256.0
            fl = d[p + 22]
            res.append(dict(t="shadow", color=col, bx=bx, by=by, angle=ang, dist=dist, strength=st,
                            inner=bool(fl & 0x80), knockout=bool(fl & 0x40), composite=bool(fl & 0x20),
                            passes=fl & 0x1F))
            p += 23
        elif t == 1:
            res.append(dict(t="blur", bx=fx(p), by=fx(p + 4), passes=d[p + 8] >> 3))
            p += 9
        elif t == 2:
            col = rgba(p)
            st = struct.unpack_from("<h", d, p + 12)[0] / 256.0
            fl = d[p + 14]
            res.append(dict(t="glow", color=col, bx=fx(p + 4), by=fx(p + 8), strength=st,
                            inner=bool(fl & 0x80), knockout=bool(fl & 0x40), composite=bool(fl & 0x20),
                            passes=fl & 0x1F))
            p += 15
        elif t == 3:
            sh, hi = rgba(p), rgba(p + 4)
            bx, by, ang, dist = fx(p + 8), fx(p + 12), fx(p + 16), fx(p + 20)
            st = struct.unpack_from("<h", d, p + 24)[0] / 256.0
            fl = d[p + 26]
            res.append(dict(t="bevel", shadow=sh, highlight=hi, bx=bx, by=by, angle=ang, dist=dist,
                            strength=st, inner=bool(fl & 0x80), knockout=bool(fl & 0x40),
                            composite=bool(fl & 0x20), ontop=bool(fl & 0x10), passes=fl & 0xF))
            p += 27
        elif t in (4, 7):
            c = d[p]
            p += 1
            cols = [rgba(p + 4 * i) for i in range(c)]
            p += 4 * c
            ratios = list(d[p:p + c])
            p += c
            bx, by, ang, dist = fx(p), fx(p + 4), fx(p + 8), fx(p + 12)
            st = struct.unpack_from("<h", d, p + 16)[0] / 256.0
            fl = d[p + 18]
            res.append(dict(t="gglow" if t == 4 else "gbevel", colors=cols, ratios=ratios, bx=bx, by=by,
                            angle=ang, dist=dist, strength=st, inner=bool(fl & 0x80),
                            knockout=bool(fl & 0x40), composite=bool(fl & 0x20), ontop=bool(fl & 0x10),
                            passes=fl & 0xF))
            p += 19
        elif t == 5:
            mx, my = d[p], d[p + 1]
            div, bias = struct.unpack_from("<ff", d, p + 2)
            mat = list(struct.unpack_from("<%df" % (mx * my), d, p + 10))
            q = p + 10 + 4 * mx * my
            col = rgba(q)
            fl = d[q + 4]
            res.append(dict(t="conv", mx=mx, my=my, divisor=div or 1.0, bias=bias, matrix=mat, color=col,
                            clamp=bool(fl & 2), preserve=bool(fl & 1)))
            p = q + 5
        elif t == 6:
            res.append(dict(t="cmatrix", m=list(struct.unpack_from("<20f", d, p))))
            p += 80
        else:
            raise ValueError("unknown filter %d" % t)
    return res, p


_ALPHA = "0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0"
_A2GRAY = "0 0 0 1 0 0 0 0 1 0 0 0 0 1 0 0 0 0 1 0"


def _col(c):
    return 'flood-color="#%02x%02x%02x" flood-opacity="%s"' % (c[0], c[1], c[2], fnum(c[3] / 255.0))


def _ramp(colors, ratios, steps=32):
    stops = sorted(zip(ratios, colors), key=lambda z: z[0])
    chans = [[], [], [], []]
    for i in range(steps):
        r = i * 255.0 / (steps - 1)
        a = stops[0]
        b = stops[-1]
        for k in range(len(stops) - 1):
            if stops[k][0] <= r <= stops[k + 1][0]:
                a, b = stops[k], stops[k + 1]
                break
        if r <= stops[0][0]:
            v = stops[0][1]
        elif r >= stops[-1][0]:
            v = stops[-1][1]
        else:
            t = (r - a[0]) / float(max(1, b[0] - a[0]))
            v = [a[1][j] + (b[1][j] - a[1][j]) * t for j in range(4)]
        for j in range(4):
            chans[j].append(fnum(v[j] / 255.0))
    return chans


def filter_svg(fid, flist):
    """Builds a <filter> for a chain of Flash filters. Units are twips (the SVG group is scaled by 0.05)."""
    P = []
    cnt = [0]
    cur = "SourceGraphic"

    def nm():
        cnt[0] += 1
        return "r%d" % cnt[0]

    def alpha(src):
        r = nm()
        P.append('<feColorMatrix in="%s" type="matrix" values="%s" result="%s"/>' % (src, _ALPHA, r))
        return r

    def blur(src, bx, by, passes):
        r = nm()
        k = 0.2887 * 20 * math.sqrt(max(1, passes))
        sx, sy = max(0.0, bx * k), max(0.0, by * k)
        P.append('<feGaussianBlur in="%s" stdDeviation="%s %s" result="%s"/>' % (src, fnum(sx), fnum(sy), r))
        return r

    def offset(src, dx, dy):
        if abs(dx) < 1e-6 and abs(dy) < 1e-6:
            return src
        r = nm()
        P.append('<feOffset in="%s" dx="%s" dy="%s" result="%s"/>' % (src, fnum(dx), fnum(dy), r))
        return r

    def flood(c):
        r = nm()
        P.append('<feFlood %s result="%s"/>' % (_col(c), r))
        return r

    def comp(a, b, op):
        r = nm()
        P.append('<feComposite in="%s" in2="%s" operator="%s" result="%s"/>' % (a, b, op, r))
        return r

    def gain(src, k):
        if abs(k - 1) < 1e-6:
            return src
        r = nm()
        P.append('<feComponentTransfer in="%s" result="%s"><feFuncA type="linear" slope="%s"/></feComponentTransfer>' % (src, r, fnum(k)))
        return r

    def merge(*names):
        r = nm()
        P.append('<feMerge result="%s">%s</feMerge>' % (r, "".join('<feMergeNode in="%s"/>' % n for n in names)))
        return r

    def ramp_map(src, colors, ratios):
        g = nm()
        P.append('<feColorMatrix in="%s" type="matrix" values="%s" result="%s"/>' % (src, _A2GRAY, g))
        ch = _ramp(colors, ratios)
        r = nm()
        P.append('<feComponentTransfer in="%s" result="%s">%s</feComponentTransfer>' % (
            g, r, "".join('<feFunc%s type="table" tableValues="%s"/>' % (c, " ".join(v)) for c, v in zip("RGBA", ch))))
        return r

    for f in flist:
        t = f["t"]
        a = alpha(cur) if t not in ("cmatrix", "conv", "blur") else None
        if t == "blur":
            cur = blur(cur, f["bx"], f["by"], f["passes"])
        elif t in ("shadow", "glow"):
            ang = f.get("angle", 0.0)
            dist = f.get("dist", 0.0) * 20
            dx, dy = math.cos(ang) * dist, math.sin(ang) * dist
            if f["inner"]:
                inv = nm()
                P.append('<feComponentTransfer in="%s" result="%s"><feFuncA type="table" tableValues="1 0"/></feComponentTransfer>' % (a, inv))
                b = offset(blur(inv, f["bx"], f["by"], f["passes"]), dx, dy)
                s = comp(flood(f["color"]), b, "in")
                s = comp(s, a, "in")
                s = gain(s, f["strength"])
                cur = s if f["knockout"] else merge(cur, s)
            else:
                b = offset(blur(a, f["bx"], f["by"], f["passes"]), dx, dy)
                s = gain(comp(flood(f["color"]), b, "in"), f["strength"])
                if f["knockout"]:
                    s = comp(s, a, "out")
                cur = merge(s, cur) if f["composite"] else s
        elif t == "bevel":
            ang = f["angle"]
            dist = f["dist"] * 20
            dx, dy = math.cos(ang) * dist, math.sin(ang) * dist
            if f["inner"] or f["ontop"]:
                hi = comp(a, offset(a, dx, dy), "out")
                sh = comp(a, offset(a, -dx, -dy), "out")
            else:
                hi = comp(offset(a, -dx, -dy), a, "out")
                sh = comp(offset(a, dx, dy), a, "out")
            hi = gain(comp(flood(f["highlight"]), blur(hi, f["bx"], f["by"], f["passes"]), "in"), f["strength"])
            sh = gain(comp(flood(f["shadow"]), blur(sh, f["bx"], f["by"], f["passes"]), "in"), f["strength"])
            if f["inner"] or f["ontop"]:
                hi, sh = comp(hi, a, "in"), comp(sh, a, "in")
            lay = merge(sh, hi)
            if f["knockout"]:
                cur = lay
            else:
                cur = merge(cur, lay) if (f["inner"] or f["ontop"]) else merge(lay, cur)
        elif t == "gglow":
            dist = f["dist"] * 20
            dx, dy = math.cos(f["angle"]) * dist, math.sin(f["angle"]) * dist
            if f["inner"]:
                inv = nm()
                P.append('<feComponentTransfer in="%s" result="%s"><feFuncA type="table" tableValues="1 0"/></feComponentTransfer>' % (a, inv))
                b = offset(blur(inv, f["bx"], f["by"], f["passes"]), dx, dy)
            else:
                b = offset(blur(a, f["bx"], f["by"], f["passes"]), dx, dy)
            g = gain(ramp_map(b, f["colors"], f["ratios"]), f["strength"])
            if f["inner"]:
                g = comp(g, a, "in")
            elif not f["ontop"]:
                g = comp(g, a, "out")
            cur = g if f["knockout"] else (merge(cur, g) if f["inner"] else merge(g, cur))
        elif t == "gbevel":
            dist = f["dist"] * 20
            dx, dy = math.cos(f["angle"]) * dist, math.sin(f["angle"]) * dist
            hi = blur(comp(a, offset(a, dx, dy), "out"), f["bx"], f["by"], f["passes"])
            sh = blur(comp(a, offset(a, -dx, -dy), "out"), f["bx"], f["by"], f["passes"])
            hg, sg = nm(), nm()
            P.append('<feColorMatrix in="%s" type="matrix" values="%s" result="%s"/>' % (hi, _A2GRAY, hg))
            P.append('<feColorMatrix in="%s" type="matrix" values="%s" result="%s"/>' % (sh, _A2GRAY, sg))
            e = nm()
            P.append('<feComposite in="%s" in2="%s" operator="arithmetic" k1="0" k2="0.5" k3="-0.5" k4="0.5" result="%s"/>' % (hg, sg, e))
            ea = nm()
            P.append('<feColorMatrix in="%s" type="matrix" values="%s" result="%s"/>' % (e, "0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 1 0 0 0 0", ea))
            g = ramp_map(ea, f["colors"], f["ratios"])
            g = comp(g, a, "in") if (f["inner"] or f["ontop"]) else g
            cur = g if f["knockout"] else merge(cur, g)
        elif t == "conv":
            r = nm()
            P.append('<feConvolveMatrix in="%s" order="%d %d" kernelMatrix="%s" divisor="%s" bias="%s" '
                     'edgeMode="%s" preserveAlpha="%s" result="%s"/>' % (
                         cur, f["mx"], f["my"], " ".join(fnum(v) for v in f["matrix"]), fnum(f["divisor"]),
                         fnum(f["bias"]), "duplicate" if f["clamp"] else "none",
                         "true" if f["preserve"] else "false", r))
            cur = r
        elif t == "cmatrix":
            m = list(f["m"])
            for i in (4, 9, 14, 19):
                m[i] = m[i] / 255.0
            r = nm()
            P.append('<feColorMatrix in="%s" type="matrix" values="%s" result="%s"/>' % (cur, " ".join(fnum(v) for v in m), r))
            cur = r
    return ('<filter id="%s" x="-50%%" y="-50%%" width="200%%" height="200%%" '
            'color-interpolation-filters="sRGB">%s</filter>') % (fid, "".join(P))


def cx_filter(fid, cx):
    """ColorTransform (mul/add) -> <filter>."""
    rm, gm, bm, am, ra, ga, ba, aa = cx
    vals = "%s 0 0 0 %s 0 %s 0 0 %s 0 0 %s 0 %s 0 0 0 %s %s" % (
        fnum(rm), fnum(ra / 255.0), fnum(gm), fnum(ga / 255.0), fnum(bm), fnum(ba / 255.0),
        fnum(am), fnum(aa / 255.0))
    return ('<filter id="%s" color-interpolation-filters="sRGB" x="-5%%" y="-5%%" width="110%%" height="110%%">'
            '<feColorMatrix type="matrix" values="%s"/></filter>') % (fid, vals)


def decompose(m):
    """SWF matrix (a b c d tx ty) -> (tx, ty, rot°, skewX°, sx, sy) or None."""
    a, b, c, d, tx, ty = m
    sx = math.hypot(a, b)
    if sx < 1e-9:
        return None
    ux, uy = a / sx, b / sx
    k = ux * c + uy * d
    cx_, cy_ = c - k * ux, d - k * uy
    sy = math.hypot(cx_, cy_)
    if sy < 1e-9:
        return None
    if ux * cy_ - uy * cx_ < 0:
        sy = -sy
    rot = math.degrees(math.atan2(b, a))
    skew = math.degrees(math.atan(k / sy))
    return (tx, ty, rot, skew, sx, sy)


def runs(vals):
    out = []
    for i, v in enumerate(vals):
        if not out or out[-1][1] != v:
            out.append((i, v))
    return out


def smil(attr, vals, n, dur, begin, kind=None, fill_freeze=True):
    """Discrete per-frame attribute animation. vals - list of strings (length n).
    -> (static value, '') if the values do not change, otherwise (None, <animate…>)."""
    r = runs(vals)
    if len(r) == 1:
        return vals[0], ""
    kt = ";".join(fnum(i / float(n)) if i else "0" for i, _ in r)
    vs = ";".join(v for _, v in r)
    tag = "animateTransform" if kind else "animate"
    typ = ' type="%s"' % kind if kind else ""
    s = '<%s attributeName="%s"%s values="%s" keyTimes="%s" dur="%.6fs" begin="%s" calcMode="discrete"%s/>' % (
        tag, attr, typ, vs, kt, dur, begin, ' fill="freeze"' if fill_freeze else "")
    return None, s


class _H(HTMLParser):
    def __init__(self, dc, ds):
        super().__init__(convert_charrefs=True)
        self.runs, self.st = [], [dict(color=dc, size=ds, b=False, i=False)]

    def handle_starttag(self, tag, at):
        cur = dict(self.st[-1])
        at = dict(at)
        if tag == "font":
            if "color" in at:
                cur["color"] = at["color"]
            if "size" in at:
                try:
                    cur["size"] = float(at["size"])
                except ValueError:
                    pass
        elif tag == "b":
            cur["b"] = True
        elif tag == "i":
            cur["i"] = True
        elif tag in ("br",):
            self.runs.append(("\n", cur))
        elif tag == "p" and self.runs:
            self.runs.append(("\n", cur))
        self.st.append(cur)

    def handle_endtag(self, tag):
        if len(self.st) > 1:
            self.st.pop()

    def handle_data(self, data):
        self.runs.append((data, self.st[-1]))


def html_runs(text, color="#000000", size=12.0):
    p = _H(color, size)
    p.feed(text)
    return p.runs


def flv_audio(fmt, rate_idx, bits16, stereo, blocks):
    """Nellymoser (4,5,6) and Speex (11) -> FLV (container, no re-encoding)."""
    hdr = (fmt << 4) | ((3 if fmt == 11 else rate_idx) << 2) | (2 if (bits16 or fmt == 11) else 0) | (1 if stereo and fmt != 11 else 0)
    out = bytearray(b"FLV\x01\x04\x00\x00\x00\x09\x00\x00\x00\x00")
    ts = 0
    for b in blocks:
        tag = bytes([hdr]) + b
        out += bytes([8]) + len(tag).to_bytes(3, "big") + (ts & 0xFFFFFF).to_bytes(3, "big") + bytes([(ts >> 24) & 255]) + b"\0\0\0" + tag
        out += (11 + len(tag)).to_bytes(4, "big")
        ts += 23 if fmt in (4, 5, 6) else 20
    return bytes(out)


def _idx(d, p):
    cnt = struct.unpack_from(">H", d, p)[0]
    if cnt == 0:
        return [], p + 2
    osz = d[p + 2]
    offs = [int.from_bytes(d[p + 3 + i * osz:p + 3 + (i + 1) * osz], "big") for i in range(cnt + 1)]
    base = p + 3 + (cnt + 1) * osz - 1
    return [d[base + offs[i]:base + offs[i + 1]] for i in range(cnt)], base + offs[-1]


def _dict(b):
    res, st, i = {}, [], 0
    while i < len(b):
        c = b[i]
        i += 1
        if c <= 21:
            if c == 12:
                c = 1200 + b[i]
                i += 1
            res[c] = st
            st = []
        elif c == 28:
            st.append(struct.unpack_from(">h", b, i)[0]); i += 2
        elif c == 29:
            st.append(struct.unpack_from(">i", b, i)[0]); i += 4
        elif c == 30:
            s = ""
            while True:
                x = b[i]; i += 1
                for nib in (x >> 4, x & 15):
                    if nib == 15:
                        break
                    s += "0123456789.EE?-"[nib] if nib < 15 else ""
                else:
                    continue
                break
            try:
                st.append(float(s))
            except ValueError:
                st.append(0.0)
        elif 32 <= c <= 246:
            st.append(c - 139)
        elif 247 <= c <= 250:
            st.append((c - 247) * 256 + b[i] + 108); i += 1
        elif 251 <= c <= 254:
            st.append(-(c - 251) * 256 - b[i] - 108); i += 1
    return res


def _cs_width(cs, default, nominal):
    st, i = [], 0
    while i < len(cs):
        c = cs[i]
        i += 1
        if c >= 32 and c <= 246:
            st.append(c - 139)
        elif 247 <= c <= 250:
            st.append((c - 247) * 256 + cs[i] + 108); i += 1
        elif 251 <= c <= 254:
            st.append(-(c - 251) * 256 - cs[i] - 108); i += 1
        elif c == 28:
            st.append(struct.unpack_from(">h", cs, i)[0]); i += 2
        elif c == 255:
            st.append(struct.unpack_from(">i", cs, i)[0] / 65536.0); i += 4
        else:
            n = len(st)
            if c in (1, 3, 18, 23, 19, 20):
                has = n % 2 == 1
            elif c == 21:
                has = n > 2
            elif c in (22, 4):
                has = n > 1
            elif c == 14:
                has = n in (1, 5)
            else:
                return default
            return nominal + st[0] if has else default
    return default


def parse_cff(data):
    """-> dict(n, widths, names)  names[gid] = string or None"""
    hs, osz = data[2], data[3]
    _, p = _idx(data, hs)
    tops, p = _idx(data, p)
    strs, p = _idx(data, p)
    top = _dict(tops[0])
    cs, _ = _idx(data, top[17][0])
    n = len(cs)
    dw = nw = 0
    if 18 in top:
        size, off = top[18]
        pr = _dict(data[off:off + size])
        dw = pr.get(20, [0])[0]
        nw = pr.get(21, [0])[0]
    widths = [int(_cs_width(c, dw, nw)) for c in cs]
    sids = [0]
    cso = top.get(15, [0])[0]
    if cso > 2:
        fmt = data[cso]
        q = cso + 1
        if fmt == 0:
            sids += [struct.unpack_from(">H", data, q + 2 * i)[0] for i in range(n - 1)]
        else:
            while len(sids) < n:
                first = struct.unpack_from(">H", data, q)[0]
                if fmt == 1:
                    left = data[q + 2]; q += 3
                else:
                    left = struct.unpack_from(">H", data, q + 2)[0]; q += 4
                sids += [first + k for k in range(left + 1)]
    names = []
    for sid in sids[:n]:
        if sid == 0:
            names.append(None)
        elif sid <= 95:
            names.append(chr(31 + sid))
        elif sid >= 391 and sid - 391 < len(strs):
            names.append(strs[sid - 391].decode("latin-1"))
        else:
            names.append(None)
    return dict(n=n, widths=widths, names=names + [None] * (n - len(names)))


def name_to_code(nm):
    if not nm:
        return 0
    if len(nm) == 1:
        return ord(nm)
    m = re.match(r"^uni([0-9A-Fa-f]{4})$", nm) or re.match(r"^u([0-9A-Fa-f]{4,5})$", nm)
    if m:
        return int(m.group(1), 16)
    try:
        import unicodedata
        return ord(unicodedata.lookup(re.sub(r"([a-z])([A-Z])", r"\1 \2", nm)))
    except Exception:
        return 0


def _csum(b):
    b = b + b"\0" * (-len(b) % 4)
    return sum(struct.unpack(">%dI" % (len(b) // 4), b)) & 0xFFFFFFFF


def _area(c):
    return sum(c[i][0] * c[(i + 1) % len(c)][1] - c[(i + 1) % len(c)][0] * c[i][1] for i in range(len(c))) / 2.0


def _inside(pt, poly):
    x, y = pt
    ins = False
    j = len(poly) - 1
    for i in range(len(poly)):
        xi, yi, xj, yj = poly[i][0], poly[i][1], poly[j][0], poly[j][1]
        if (yi > y) != (yj > y) and x < (xj - xi) * (y - yi) / float(yj - yi or 1) + xi:
            ins = not ins
        j = i
    return ins


def fix_winding(contours):
    """Outer contours are clockwise (y up), holes are counter-clockwise."""
    res = []
    for i, c in enumerate(contours):
        depth = sum(1 for j, o in enumerate(contours) if j != i and _inside(c[0][:2], o))
        a = _area(c)
        want_cw = depth % 2 == 0
        if (a > 0) == want_cw:
            c = c[::-1]
        res.append(c)
    return res


def _cmap(codes_to_gid):
    items = sorted((c, g) for c, g in codes_to_gid.items() if 0 < c < 0xFFFF)
    cm = []
    for c, g in items:
        if cm and c == cm[-1][1] + 1 and g == cm[-1][3] + 1:
            cm[-1][1], cm[-1][3] = c, g
        else:
            cm.append([c, c, g, g])
    cm.append([0xFFFF, 0xFFFF, 0, 0])
    sc = len(cm)
    es = 1
    while es * 2 <= sc:
        es *= 2
    sr = es * 2
    sub = struct.pack(">HHHHHHH", 4, 16 + sc * 8, 0, sc * 2, sr, int(math.log2(es)), sc * 2 - sr)
    sub += b"".join(struct.pack(">H", s[1]) for s in cm) + b"\0\0"
    sub += b"".join(struct.pack(">H", s[0]) for s in cm)
    sub += b"".join(struct.pack(">H", ((s[2] - s[0]) if s[0] != 0xFFFF else 1) & 0xFFFF) for s in cm)
    sub += b"\0\0" * sc
    return struct.pack(">HH", 0, 1) + struct.pack(">HHI", 3, 1, 12) + sub, (items[0][0] if items else 0), (items[-1][0] if items else 0)


def _name(name, italic, bold):
    sub = ("Bold " if bold else "") + ("Italic" if italic else "")
    sub = sub.strip() or "Regular"
    ps = re.sub(r"[^A-Za-z0-9-]", "", name) or "SWFFont"
    strs = [(1, name), (2, sub), (3, "%s;%s" % (ps, sub)), (4, name + ("" if sub == "Regular" else " " + sub)),
            (5, "Version 1.0"), (6, ps)]
    recs, sd = b"", b""
    for nid, s in strs:
        e = s.encode("utf-16-be")
        recs += struct.pack(">HHHHHH", 3, 1, 0x409, nid, len(e), len(sd))
        sd += e
    return struct.pack(">HHH", 0, len(strs), 6 + len(recs)) + recs + sd


def build_sfnt(name, upm, glyphs, adv, codes, ascent, descent, leading=0, bold=False, italic=False,
               kerning=None, cff=None, cff_info=None):
    """glyphs[i] = list of contours [(x, y, on)] in font units, y up.
    adv[i] - advance in font units. codes[i] - Unicode. kerning: {(code1, code2): value}.
    cff: raw CFF data -> OpenType (OTTO) instead of TrueType."""
    n = len(adv)
    blobs, xmin_all, xmax_all, ymin_all, ymax_all = [], 0, 0, 0, 0
    maxp = maxc = 0
    lsb = []
    if cff is None:
        for g in glyphs:
            cs = []
            for c in g:
                c = [(int(round(max(-30000, min(30000, x)))), int(round(max(-30000, min(30000, y)))), on) for x, y, on in c]
                if len(c) > 1 and c[-1][2] and c[-1][:2] == c[0][:2]:
                    c = c[:-1]
                if len(c) >= 3:
                    cs.append(c)
            if not cs:
                blobs.append(b"")
                lsb.append(0)
                continue
            cs = fix_winding(cs)
            pts = [p for c in cs for p in c]
            ends, k = [], -1
            for c in cs:
                k += len(c)
                ends.append(k)
            xs, ys = [p[0] for p in pts], [p[1] for p in pts]
            hd = struct.pack(">hhhhh", len(cs), min(xs), min(ys), max(xs), max(ys))
            body = b"".join(struct.pack(">H", e) for e in ends) + b"\0\0" + bytes(p[2] for p in pts)
            px = py = 0
            xb = yb = b""
            for x, y, _ in pts:
                xb += struct.pack(">h", x - px)
                yb += struct.pack(">h", y - py)
                px, py = x, y
            bl = hd + body + xb + yb
            blobs.append(bl + b"\0" * (-len(bl) % 4))
            lsb.append(min(xs))
            xmin_all, xmax_all = min(xmin_all, min(xs)), max(xmax_all, max(xs))
            ymin_all, ymax_all = min(ymin_all, min(ys)), max(ymax_all, max(ys))
            maxp, maxc = max(maxp, len(pts)), max(maxc, len(cs))
    else:
        lsb = [0] * n
        xmax_all, ymax_all, ymin_all = upm, ascent, -descent
    adv = [max(0, min(65535, int(round(a)))) for a in adv]
    pairs = {}
    for i, c in enumerate(codes[:n]):
        if c and c not in pairs:
            pairs[c] = i
    cmap, first, last = _cmap(pairs)
    mac = (1 if bold else 0) | (2 if italic else 0)
    head = struct.pack(">IIIIHHqqhhhhHHhhh", 0x00010000, 0x00010000, 0, 0x5F0F3CF5, 3, upm, 3000000000, 3000000000,
                       xmin_all, ymin_all if cff is None else -descent, xmax_all, ymax_all if cff is None else ascent,
                       mac, 8, 2, 0 if cff else 1, 0)
    amax = max(adv + [1])
    hhea = struct.pack(">IhhhHhhhhhhhhhhhH", 0x00010000, ascent, -descent, leading, amax, min(lsb + [0]), 0, xmax_all,
                       1, 0, 0, 0, 0, 0, 0, 0, n)
    hmtx = b"".join(struct.pack(">Hh", a, l) for a, l in zip(adv, lsb))
    avg = int(sum(adv) / max(1, n))
    sel = (1 if italic else 0) | (0x20 if bold else 0) | (0x40 if not (bold or italic) else 0)
    os2 = struct.pack(">HhHHH", 3, avg, 700 if bold else 400, 5, 0)
    os2 += struct.pack(">10h", upm // 10, upm // 10, 0, upm // 10, upm // 10, upm // 10, 0, upm // 3, upm // 20, upm // 4)
    os2 += struct.pack(">h", 0) + b"\0" * 10 + struct.pack(">IIII", 0, 0, 0, 0) + b"SWF "
    os2 += struct.pack(">HHH", sel, min(first, 0xFFFF), min(last, 0xFFFF))
    os2 += struct.pack(">hhh", ascent, -descent, leading)
    os2 += struct.pack(">HH", max(ascent, ymax_all), max(descent, -ymin_all))
    os2 += struct.pack(">II", 1, 0) + struct.pack(">hh", upm // 2, upm * 7 // 10) + struct.pack(">HHH", 0, 32, 0)
    post = struct.pack(">IiHhIIIII", 0x00030000, 0, 0, 0, 0, 0, 0, 0, 0)
    tables = {"OS/2": os2, "cmap": cmap, "head": head, "hhea": hhea, "hmtx": hmtx, "name": _name(name, italic, bold),
              "post": post}
    if cff is None:
        glyf, loca = b"", b""
        for b in blobs:
            loca += struct.pack(">I", len(glyf))
            glyf += b
        loca += struct.pack(">I", len(glyf))
        tables.update(glyf=glyf, loca=loca,
                      maxp=struct.pack(">IHHHHHHHHHHHHHH", 0x00010000, n, maxp, maxc, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0))
        sfver = 0x00010000
    else:
        tables["CFF "] = cff
        tables["maxp"] = struct.pack(">IH", 0x00005000, n)
        sfver = 0x4F54544F
    if kerning:
        c2g = pairs
        kp = sorted(((c2g[a], c2g[b], v) for (a, b), v in kerning.items() if a in c2g and b in c2g and v))
        if kp:
            kp = kp[:10920]
            es = 1
            while es * 2 <= len(kp):
                es *= 2
            sub = struct.pack(">HHHH", len(kp), es * 6, int(math.log2(es)), (len(kp) - es) * 6)
            sub += b"".join(struct.pack(">HHh", a, b, max(-32768, min(32767, int(v)))) for a, b, v in kp)
            tables["kern"] = struct.pack(">HH", 0, 1) + struct.pack(">HHH", 0, 6 + len(sub), 1) + sub
    tags = sorted(tables)
    nt = len(tags)
    es = 1
    while es * 2 <= nt:
        es *= 2
    out = struct.pack(">IHHHH", sfver, nt, es * 16, int(math.log2(es)), nt * 16 - es * 16)
    off, body, dire, head_off = 12 + 16 * nt, b"", b"", 0
    for t in tags:
        data = tables[t]
        if t == "head":
            head_off = off + len(body)
        dire += struct.pack(">4sIII", t.encode(), _csum(data), off + len(body), len(data))
        body += data + b"\0" * (-len(data) % 4)
    fb = bytearray(out + dire + body)
    struct.pack_into(">I", fb, head_off + 8, (0xB1B0AFBA - _csum(bytes(fb))) & 0xFFFFFFFF)
    return bytes(fb)
'''))
_EMBEDDED.append(('swf_abc', r'''"""swf_abc - ABC (AVM2) parser, disassembler and ActionScript 3 decompiler."""
import re
import struct

from swf_decomp import (E, Ins, Structurer, and_e, binop, cmp_e, indent, negate, or_e, qstr, strip_par, wrap)

NSKIND = {0x08: "ns", 0x16: "public", 0x17: "internal", 0x18: "protected", 0x19: "explicit",
          0x1A: "static protected", 0x05: "private"}

OPS = {
    0x01: ("bkpt", ""), 0x02: ("nop", ""), 0x03: ("throw", ""), 0x04: ("getsuper", "m"),
    0x05: ("setsuper", "m"), 0x06: ("dxns", "u"), 0x07: ("dxnslate", ""), 0x08: ("kill", "u"),
    0x09: ("label", ""), 0x0C: ("ifnlt", "j"), 0x0D: ("ifnle", "j"), 0x0E: ("ifngt", "j"),
    0x0F: ("ifnge", "j"), 0x10: ("jump", "j"), 0x11: ("iftrue", "j"), 0x12: ("iffalse", "j"),
    0x13: ("ifeq", "j"), 0x14: ("ifne", "j"), 0x15: ("iflt", "j"), 0x16: ("ifle", "j"),
    0x17: ("ifgt", "j"), 0x18: ("ifge", "j"), 0x19: ("ifstricteq", "j"), 0x1A: ("ifstrictne", "j"),
    0x1B: ("lookupswitch", "s"), 0x1C: ("pushwith", ""), 0x1D: ("popscope", ""),
    0x1E: ("nextname", ""), 0x1F: ("hasnext", ""), 0x20: ("pushnull", ""), 0x21: ("pushundefined", ""),
    0x23: ("nextvalue", ""), 0x24: ("pushbyte", "b"), 0x25: ("pushshort", "u"), 0x26: ("pushtrue", ""),
    0x27: ("pushfalse", ""), 0x28: ("pushnan", ""), 0x29: ("pop", ""), 0x2A: ("dup", ""),
    0x2B: ("swap", ""), 0x2C: ("pushstring", "u"), 0x2D: ("pushint", "u"), 0x2E: ("pushuint", "u"),
    0x2F: ("pushdouble", "u"), 0x30: ("pushscope", ""), 0x31: ("pushnamespace", "u"),
    0x32: ("hasnext2", "uu"), 0x35: ("li8", ""), 0x36: ("li16", ""), 0x37: ("li32", ""),
    0x38: ("lf32", ""), 0x39: ("lf64", ""), 0x3A: ("si8", ""), 0x3B: ("si16", ""), 0x3C: ("si32", ""),
    0x3D: ("sf32", ""), 0x3E: ("sf64", ""), 0x40: ("newfunction", "u"), 0x41: ("call", "u"),
    0x42: ("construct", "u"), 0x43: ("callmethod", "uu"), 0x44: ("callstatic", "uu"),
    0x45: ("callsuper", "mu"), 0x46: ("callproperty", "mu"), 0x47: ("returnvoid", ""),
    0x48: ("returnvalue", ""), 0x49: ("constructsuper", "u"), 0x4A: ("constructprop", "mu"),
    0x4C: ("callproplex", "mu"), 0x4E: ("callsupervoid", "mu"), 0x4F: ("callpropvoid", "mu"),
    0x50: ("sxi1", ""), 0x51: ("sxi8", ""), 0x52: ("sxi16", ""), 0x53: ("applytype", "u"),
    0x55: ("newobject", "u"), 0x56: ("newarray", "u"), 0x57: ("newactivation", ""),
    0x58: ("newclass", "u"), 0x59: ("getdescendants", "m"), 0x5A: ("newcatch", "u"),
    0x5D: ("findpropstrict", "m"), 0x5E: ("findproperty", "m"), 0x5F: ("finddef", "m"),
    0x60: ("getlex", "m"), 0x61: ("setproperty", "m"), 0x62: ("getlocal", "u"), 0x63: ("setlocal", "u"),
    0x64: ("getglobalscope", ""), 0x65: ("getscopeobject", "b"), 0x66: ("getproperty", "m"),
    0x68: ("initproperty", "m"), 0x6A: ("deleteproperty", "m"), 0x6C: ("getslot", "u"),
    0x6D: ("setslot", "u"), 0x6E: ("getglobalslot", "u"), 0x6F: ("setglobalslot", "u"),
    0x70: ("convert_s", ""), 0x71: ("esc_xelem", ""), 0x72: ("esc_xattr", ""), 0x73: ("convert_i", ""),
    0x74: ("convert_u", ""), 0x75: ("convert_d", ""), 0x76: ("convert_b", ""), 0x77: ("convert_o", ""),
    0x78: ("checkfilter", ""), 0x80: ("coerce", "m"), 0x81: ("coerce_b", ""), 0x82: ("coerce_a", ""),
    0x83: ("coerce_i", ""), 0x84: ("coerce_d", ""), 0x85: ("coerce_s", ""), 0x86: ("astype", "m"),
    0x87: ("astypelate", ""), 0x88: ("coerce_u", ""), 0x89: ("coerce_o", ""), 0x90: ("negate", ""),
    0x91: ("increment", ""), 0x92: ("inclocal", "u"), 0x93: ("decrement", ""), 0x94: ("declocal", "u"),
    0x95: ("typeof", ""), 0x96: ("not", ""), 0x97: ("bitnot", ""), 0xA0: ("add", ""),
    0xA1: ("subtract", ""), 0xA2: ("multiply", ""), 0xA3: ("divide", ""), 0xA4: ("modulo", ""),
    0xA5: ("lshift", ""), 0xA6: ("rshift", ""), 0xA7: ("urshift", ""), 0xA8: ("bitand", ""),
    0xA9: ("bitor", ""), 0xAA: ("bitxor", ""), 0xAB: ("equals", ""), 0xAC: ("strictequals", ""),
    0xAD: ("lessthan", ""), 0xAE: ("lessequals", ""), 0xAF: ("greaterthan", ""),
    0xB0: ("greaterequals", ""), 0xB1: ("instanceof", ""), 0xB2: ("istype", "m"),
    0xB3: ("istypelate", ""), 0xB4: ("in", ""), 0xC0: ("increment_i", ""), 0xC1: ("decrement_i", ""),
    0xC2: ("inclocal_i", "u"), 0xC3: ("declocal_i", "u"), 0xC4: ("negate_i", ""), 0xC5: ("add_i", ""),
    0xC6: ("subtract_i", ""), 0xC7: ("multiply_i", ""),
    0xD0: ("getlocal0", ""), 0xD1: ("getlocal1", ""), 0xD2: ("getlocal2", ""), 0xD3: ("getlocal3", ""),
    0xD4: ("setlocal0", ""), 0xD5: ("setlocal1", ""), 0xD6: ("setlocal2", ""), 0xD7: ("setlocal3", ""),
    0xEF: ("debug", "d"), 0xF0: ("debugline", "u"), 0xF1: ("debugfile", "u"), 0xF2: ("bkptline", "u"),
    0xF3: ("timestamp", ""),
}
CJ = {0x0C, 0x0D, 0x0E, 0x0F, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1A}


class R:
    def __init__(self, d, p=0):
        self.d, self.p = d, p

    def u8(self):
        v = self.d[self.p]
        self.p += 1
        return v

    def u16(self):
        v = struct.unpack_from("<H", self.d, self.p)[0]
        self.p += 2
        return v

    def u30(self):
        v = sh = 0
        while True:
            b = self.d[self.p]
            self.p += 1
            v |= (b & 0x7F) << sh
            sh += 7
            if not b & 0x80:
                return v & 0xFFFFFFFF

    def s32(self):
        v = self.u30()
        return v - (1 << 32) if v & 0x80000000 else v

    def bytes(self, n):
        v = self.d[self.p:self.p + n]
        self.p += n
        return v


class ABC:
    def __init__(self, data):
        r = R(data)
        self.minor, self.major = r.u16(), r.u16()
        n = r.u30()
        self.ints = [0] + [r.s32() for _ in range(max(0, n - 1))]
        n = r.u30()
        self.uints = [0] + [r.u30() for _ in range(max(0, n - 1))]
        n = r.u30()
        self.doubles = [float("nan")] + [struct.unpack("<d", r.bytes(8))[0] for _ in range(max(0, n - 1))]
        n = r.u30()
        self.strings = [""] + [r.bytes(r.u30()).decode("utf-8", "replace") for _ in range(max(0, n - 1))]
        n = r.u30()
        self.ns = [(0, 0)] + [(r.u8(), r.u30()) for _ in range(max(0, n - 1))]
        n = r.u30()
        self.nssets = [[]] + [[r.u30() for _ in range(r.u30())] for _ in range(max(0, n - 1))]
        n = r.u30()
        self.mn = [None]
        for _ in range(max(0, n - 1)):
            k = r.u8()
            if k in (0x07, 0x0D):
                self.mn.append((k, r.u30(), r.u30()))
            elif k in (0x0F, 0x10):
                self.mn.append((k, r.u30()))
            elif k in (0x11, 0x12):
                self.mn.append((k,))
            elif k in (0x09, 0x0E):
                self.mn.append((k, r.u30(), r.u30()))
            elif k in (0x1B, 0x1C):
                self.mn.append((k, r.u30()))
            elif k == 0x1D:
                q = r.u30()
                self.mn.append((k, q, [r.u30() for _ in range(r.u30())]))
            else:
                raise ValueError("multiname kind 0x%x" % k)
        n = r.u30()
        self.methods = []
        for _ in range(n):
            pc = r.u30()
            ret = r.u30()
            ptypes = [r.u30() for _ in range(pc)]
            name = r.u30()
            fl = r.u8()
            opts = []
            if fl & 0x08:
                opts = [(r.u30(), r.u8()) for _ in range(r.u30())]
            pnames = [r.u30() for _ in range(pc)] if fl & 0x80 else []
            self.methods.append(dict(pc=pc, ret=ret, ptypes=ptypes, name=name, flags=fl, opts=opts, pnames=pnames))
        n = r.u30()
        for _ in range(n):
            r.u30()
            for _ in range(2 * r.u30()):
                r.u30()
        n = r.u30()
        self.instances = []
        for _ in range(n):
            name, sup, fl = r.u30(), r.u30(), r.u8()
            pns = r.u30() if fl & 8 else 0
            ifs = [r.u30() for _ in range(r.u30())]
            init = r.u30()
            self.instances.append(dict(name=name, super=sup, flags=fl, ifaces=ifs, init=init, traits=self.traits(r)))
        self.classes = [dict(init=r.u30(), traits=self.traits(r)) for _ in range(n)]
        self.scripts = [dict(init=r.u30(), traits=self.traits(r)) for _ in range(r.u30())]
        self.bodies = {}
        for _ in range(r.u30()):
            m, ms, lc, isd, msd = r.u30(), r.u30(), r.u30(), r.u30(), r.u30()
            code = r.bytes(r.u30())
            exc = [dict(frm=r.u30(), to=r.u30(), target=r.u30(), type=r.u30(), var=r.u30()) for _ in range(r.u30())]
            self.bodies[m] = dict(locals=lc, code=code, exc=exc, traits=self.traits(r))

    def traits(self, r):
        out = []
        for _ in range(r.u30()):
            name, kb = r.u30(), r.u8()
            kind, attrs = kb & 15, kb >> 4
            t = dict(name=name, kind=kind, attrs=attrs)
            if kind in (0, 6):
                t["slot"], t["type"], vi = r.u30(), r.u30(), r.u30()
                t["val"] = (r.u8(), vi) if vi else None
            elif kind == 4:
                t["slot"], t["cls"] = r.u30(), r.u30()
            elif kind == 5:
                t["slot"], t["method"] = r.u30(), r.u30()
            else:
                t["disp"], t["method"] = r.u30(), r.u30()
            if attrs & 4:
                for _ in range(r.u30()):
                    r.u30()
            out.append(t)
        return out

    def s(self, i):
        return self.strings[i] if 0 <= i < len(self.strings) else "?"

    def mn_info(self, i):
        """-> dict(name, ns, nskind, rtns, rtname)"""
        if not i or i >= len(self.mn):
            return dict(name="*", ns="", nskind=None, rtns=False, rtname=False)
        m = self.mn[i]
        k = m[0]
        if k in (0x07, 0x0D):
            nk, nn = self.ns[m[1]] if m[1] < len(self.ns) else (0, 0)
            return dict(name=self.s(m[2]) if m[2] else "*", ns=self.s(nn), nskind=nk, rtns=False, rtname=False)
        if k in (0x0F, 0x10):
            return dict(name=self.s(m[1]), ns="", nskind=None, rtns=True, rtname=False)
        if k in (0x11, 0x12):
            return dict(name="", ns="", nskind=None, rtns=True, rtname=True)
        if k in (0x09, 0x0E):
            nss = self.nssets[m[2]] if m[2] < len(self.nssets) else []
            nk, nn = self.ns[nss[0]] if nss else (0, 0)
            return dict(name=self.s(m[1]), ns=self.s(nn), nskind=nk, rtns=False, rtname=False)
        if k in (0x1B, 0x1C):
            return dict(name="", ns="", nskind=None, rtns=False, rtname=True)
        if k == 0x1D:
            b = self.mn_info(m[1])
            ps = ", ".join(self.mn_info(p)["name"] for p in m[2])
            return dict(name="%s.<%s>" % (b["name"], ps), ns=b["ns"], nskind=b["nskind"], rtns=False, rtname=False)
        return dict(name="?", ns="", nskind=None, rtns=False, rtname=False)

    def mn_str(self, i):
        return self.mn_info(i)["name"]

    def full(self, i):
        m = self.mn_info(i)
        return (m["ns"] + "." if m["ns"] else "") + m["name"]

    def const(self, kind, idx):
        if kind == 0x01:
            return qstr(self.s(idx))
        if kind == 0x03:
            return str(self.ints[idx])
        if kind == 0x04:
            return str(self.uints[idx])
        if kind == 0x06:
            return repr(self.doubles[idx])
        return {0x0B: "true", 0x0A: "false", 0x0C: "null", 0x00: "undefined"}.get(kind, "/*const 0x%x*/" % kind)

    def parse_code(self, code):
        r = R(code)
        res = []
        while r.p < len(code):
            a = r.p
            op = r.u8()
            nm, fm = OPS.get(op, ("op_%02X" % op, ""))
            x = Ins(a, 0, op, nm)
            args = []
            for c in fm:
                if c == "u":
                    args.append(r.u30())
                elif c == "m":
                    args.append(r.u30())
                elif c == "b":
                    v = r.u8()
                    args.append(v - 256 if v > 127 and op == 0x24 else v)
                elif c == "j":
                    b = code[r.p:r.p + 3]
                    off = int.from_bytes(b, "little", signed=True)
                    r.p += 3
                    x.target = r.p + off
                    x.kind = "jmp" if op == 0x10 else "cjmp"
                    args.append(x.target)
                elif c == "s":
                    d = int.from_bytes(r.bytes(3), "little", signed=True)
                    cnt = r.u30()
                    x.target = a + d
                    x.targets = [a + int.from_bytes(r.bytes(3), "little", signed=True) for _ in range(cnt + 1)]
                    x.kind = "sw"
                elif c == "d":
                    args = [r.u8(), r.u30(), r.u8(), r.u30()]
            x.args, x.nxt = args, r.p
            res.append(x)
        return res

    def disasm(self, code):
        out = []
        for x in self.parse_code(code):
            a = ""
            if x.args:
                if OPS.get(x.op, ("", ""))[1].startswith("m"):
                    a = "%s %s" % (self.full(x.args[0]), " ".join(str(v) for v in x.args[1:]))
                elif x.op == 0x2C:
                    a = qstr(self.s(x.args[0]))
                else:
                    a = " ".join(("L%d" % v if x.kind in ("jmp", "cjmp") else str(v)) for v in x.args)
            if x.kind == "sw":
                a = "default L%d, cases %s" % (x.target, ["L%d" % t for t in x.targets])
            out.append("%04X: %s %s" % (x.addr, x.name, a))
        return out


class AVM2Sim:
    def __init__(self, abc, mi, body, ins, nested=0):
        self.abc, self.mi, self.body, self.nested = abc, mi, body, nested
        self.m = abc.methods[mi]
        self.stack, self.out = [], []
        self.lnames = {0: "this"}
        pc = self.m["pc"]
        for k in range(pc):
            nm = abc.s(self.m["pnames"][k]) if self.m["pnames"] else "arg%d" % (k + 1)
            self.lnames[k + 1] = nm or "arg%d" % (k + 1)
        if self.m["flags"] & 0x04:
            self.lnames[pc + 1] = "rest"
        for x in ins:
            if x.op == 0xEF and x.args and x.args[0] == 1:
                nm = abc.s(x.args[1])
                if nm and x.args[2] + 1 not in self.lnames:
                    self.lnames[x.args[2] + 1] = nm
        self.nparams = pc + (1 if self.m["flags"] & 4 else 0)
        self.declared = set(range(1, self.nparams + 1))
        self.lvals = {}
        self.slotnames = {}
        for t in body.get("traits", []):
            if t["kind"] in (0, 6):
                self.slotnames[t["slot"]] = abc.mn_str(t["name"])
        self.supp = False
        self.tmp = 0

    def snapshot(self):
        return (list(self.stack), len(self.out), dict(self.lvals))

    def restore(self, s):
        self.stack = list(s[0])
        del self.out[s[1]:]
        self.lvals = s[2]

    def begin_catch(self, g):
        self.supp = True
        self.stack = [E(g.get("var") or "e")]

    def lname(self, n):
        return self.lnames.get(n + 1 if False else n) or "_loc%d_" % n

    def pop(self):
        return self.stack.pop() if self.stack else E("undefined /*stack*/")

    def push(self, e):
        self.stack.append(e)

    def mn_pop(self, i):
        """pops the runtime parts of a multiname off the stack. -> (info, name_expr|None)"""
        info = self.abc.mn_info(i)
        nm = None
        if info["rtname"]:
            nm = self.pop()
        if info["rtns"]:
            self.pop()
        return info, nm

    def prop(self, obj, info, nm):
        if nm is not None:
            return E("%s[%s]" % (wrap(obj, 14), strip_par(nm.s)), 14)
        if obj.scope:
            return E(info["name"], 99)
        return E("%s.%s" % (wrap(obj, 14), info["name"]), 14)

    def args(self, n):
        return [self.pop() for _ in range(n)][::-1]

    def stmt(self, s):
        self.out.append(s + ";")

    def take_cond(self, x):
        P = self.pop
        o = x.op
        if o == 0x11:
            return P()
        if o == 0x12:
            return negate(P())
        b, a = P(), P()
        if o == 0x13:
            return cmp_e(a, "==", b, 8, "!=")
        if o == 0x14:
            return cmp_e(a, "!=", b, 8, "==")
        if o == 0x19:
            return cmp_e(a, "===", b, 8, "!==")
        if o == 0x1A:
            return cmp_e(a, "!==", b, 8, "===")
        ops = {0x15: "<", 0x16: "<=", 0x17: ">", 0x18: ">="}
        if o in ops:
            return binop(a, ops[o], b, 9)
        ops = {0x0C: "<", 0x0D: "<=", 0x0E: ">", 0x0F: ">="}
        return negate(binop(a, ops[o], b, 9))

    def loop_hook(self, cond, body):
        m = re.match(r"^hasnext2\((\S+), (\S+)\)$", strip_par(cond.s))
        if not m or not body:
            return None
        mm = re.match(r"^(?:var )?(\S+?) = __next(name|value)\((\S+)\);$", body[0])
        if not mm:
            return None
        obj = mm.group(3)
        src = obj
        for k in range(len(self.out) - 1, max(-1, len(self.out) - 6), -1):
            l = self.out[k]
            if re.match(r"^(var )?%s = 0;$" % re.escape(m.group(2)), l):
                del self.out[k]
                break
        for k in range(len(self.out) - 1, max(-1, len(self.out) - 6), -1):
            l = self.out[k]
            mo = re.match(r"^(?:var )?%s = (.+);$" % re.escape(m.group(1)), l)
            if mo:
                src = mo.group(1)
                del self.out[k]
                break
        kw = "for each" if mm.group(2) == "value" else "for"
        return "%s (var %s in %s) {\n%s\n}" % (kw, mm.group(1), src, "\n".join(indent(body[1:])))

    def newfunction(self, mi):
        return E(method_src(self.abc, mi, None, nested=self.nested + 1), 99)

    def exec(self, x):
        o, abc, P, push = x.op, self.abc, self.pop, self.push
        a = x.args
        if self.supp:
            if o == 0x08:
                self.supp = False
            return
        if o in (0xF0, 0xF1, 0xF2, 0xEF, 0x09, 0x02, 0x01, 0xF3, 0x1D, 0x30, 0x1C):
            if o in (0x30, 0x1C):
                P()
            return
        if o == 0x24 or o == 0x25:
            v = a[0] if o == 0x24 else ((a[0] & 0xFFFF) - 0x10000 if a[0] & 0x8000 else a[0] & 0xFFFF)
            push(E(str(v), 13 if v < 0 else 99))
        elif o == 0x2C:
            push(E(qstr(abc.s(a[0]))))
        elif o == 0x2D:
            push(E(str(abc.ints[a[0]])))
        elif o == 0x2E:
            push(E(str(abc.uints[a[0]])))
        elif o == 0x2F:
            v = abc.doubles[a[0]]
            push(E(str(int(v)) if v == v and abs(v) < 1e15 and v == int(v) else repr(v)))
        elif o in (0x20, 0x21, 0x26, 0x27, 0x28):
            push(E({0x20: "null", 0x21: "undefined", 0x26: "true", 0x27: "false", 0x28: "NaN"}[o]))
        elif o == 0x29:
            e = P()
            if e.call:
                self.stmt(strip_par(e.s))
        elif o == 0x2A:
            e = self.stack[-1] if self.stack else E("undefined")
            if e.call:
                self.tmp += 1
                t = "_tmp%d_" % self.tmp
                self.stmt("var %s = %s" % (t, strip_par(e.s)))
                self.stack[-1] = E(t)
                e = E(t)
            push(e)
        elif o == 0x2B:
            if len(self.stack) > 1:
                self.stack[-1], self.stack[-2] = self.stack[-2], self.stack[-1]
        elif o in (0xD0, 0xD1, 0xD2, 0xD3, 0x62):
            n = a[0] if o == 0x62 else o - 0xD0
            push(E(self.lname(n)))
        elif o in (0xD4, 0xD5, 0xD6, 0xD7, 0x63):
            n = a[0] if o == 0x63 else o - 0xD4
            v = P()
            nm = self.lname(n)
            self.lvals[n] = v
            if n == 0:
                return
            if n not in self.declared:
                self.declared.add(n)
                self.stmt("var %s = %s" % (nm, strip_par(v.s)))
            else:
                self.stmt("%s = %s" % (nm, strip_par(v.s)))
        elif o == 0x08:
            self.declared.discard(a[0])
        elif o in (0x92, 0x94, 0xC2, 0xC3):
            self.stmt("%s%s" % (self.lname(a[0]), "++" if o in (0x92, 0xC2) else "--"))
        elif o in (0x5D, 0x5E, 0x5F):
            info, nm = self.mn_pop(a[0])
            push(E(info["name"], 99, scope=True))
        elif o == 0x60:
            info, nm = self.mn_pop(a[0])
            push(E(info["name"]))
        elif o in (0x66, 0x04):
            info, nm = self.mn_pop(a[0])
            ob = P()
            if o == 0x04:
                ob = E("super")
            push(self.prop(ob, info, nm))
        elif o in (0x61, 0x68, 0x05):
            v = P()
            info, nm = self.mn_pop(a[0])
            ob = P()
            if o == 0x05:
                ob = E("super")
            if v.s.startswith("class_"):
                return
            self.stmt("%s = %s" % (self.prop(ob, info, nm).s, strip_par(v.s)))
        elif o == 0x6A:
            info, nm = self.mn_pop(a[0])
            ob = P()
            push(E("delete " + self.prop(ob, info, nm).s, 13, call=True))
        elif o == 0x59:
            info, nm = self.mn_pop(a[0])
            ob = P()
            push(E("%s..%s" % (wrap(ob, 14), info["name"] if nm is None else "(%s)" % nm.s), 14))
        elif o in (0x46, 0x4C, 0x4F, 0x45, 0x4E, 0x4A):
            args = self.args(a[1])
            info, nm = self.mn_pop(a[0])
            ob = P()
            al = ", ".join(strip_par(v.s) for v in args)
            if o == 0x4A:
                push(E("new %s(%s)" % (info["name"] if ob.scope or nm is None else self.prop(ob, info, nm).s, al), 14, call=True))
                return
            if o in (0x45, 0x4E):
                ob = E("super")
            tgt = self.prop(ob, info, nm).s
            e = E("%s(%s)" % (tgt, al), 14, call=True)
            if o in (0x4F, 0x4E):
                self.stmt(e.s)
            else:
                push(e)
        elif o == 0x41:
            args = self.args(a[0])
            rcv, fn = P(), P()
            al = ", ".join(strip_par(v.s) for v in args)
            push(E("%s(%s)" % (wrap(fn, 14), al) if rcv.s in ("null", "this", "undefined", "global") else
                   "%s.call(%s)" % (wrap(fn, 14), ", ".join([strip_par(rcv.s)] + [strip_par(v.s) for v in args])), 14, call=True))
        elif o == 0x42:
            args = self.args(a[0])
            f = P()
            push(E("new %s(%s)" % (wrap(f, 14), ", ".join(strip_par(v.s) for v in args)), 14, call=True))
        elif o == 0x49:
            args = self.args(a[0])
            P()
            self.stmt("super(%s)" % ", ".join(strip_par(v.s) for v in args))
        elif o in (0x43, 0x44):
            args = self.args(a[1])
            ob = P()
            push(E("%s.method%d(%s)" % (wrap(ob, 14), a[0], ", ".join(strip_par(v.s) for v in args)), 14, call=True))
        elif o == 0x53:
            args = self.args(a[0])
            f = P()
            push(E("%s.<%s>" % (wrap(f, 14), ", ".join(v.s for v in args)), 14))
        elif o == 0x55:
            kv = []
            items = self.args(a[0] * 2)
            for k in range(0, len(items), 2):
                kk = items[k]
                kv.append("%s: %s" % (kk.s.strip('"') if re.match(r'^"[A-Za-z_]\w*"$', kk.s) else "[%s]" % kk.s, strip_par(items[k + 1].s)))
            push(E("{%s}" % ", ".join(kv)))
        elif o == 0x56:
            push(E("[%s]" % ", ".join(strip_par(v.s) for v in self.args(a[0]))))
        elif o == 0x40:
            push(self.newfunction(a[0]))
        elif o == 0x58:
            push(E("class_%d" % a[0]))
        elif o == 0x57:
            push(E("_activation_", scope=False))
        elif o == 0x5A:
            push(E("_catch_"))
        elif o == 0x64:
            push(E("global", scope=True))
        elif o == 0x65:
            push(E("_scope%d_" % a[0]))
        elif o in (0x6C, 0x6E):
            ob = P()
            nm = self.slotnames.get(a[0]) if ob.s.startswith("_") else None
            push(E(nm) if nm else E("%s.slot%d" % (wrap(ob, 14), a[0]), 14))
        elif o in (0x6D, 0x6F):
            v, ob = P(), P()
            nm = self.slotnames.get(a[0]) if ob.s.startswith("_") else None
            if not v.s.startswith("_catch") and not v.s.startswith("class_"):
                self.stmt("%s = %s" % (nm or "%s.slot%d" % (wrap(ob, 14), a[0]), strip_par(v.s)))
        elif o == 0x47:
            self.stmt("return")
        elif o == 0x48:
            self.stmt("return " + strip_par(P().s))
        elif o == 0x03:
            self.stmt("throw " + strip_par(P().s))
        elif o in (0x70, 0x73, 0x74, 0x75, 0x76, 0x77, 0x80, 0x81, 0x82, 0x83, 0x84, 0x85, 0x88, 0x89, 0x78, 0x71, 0x72):
            if o == 0x80:
                self.mn_pop(a[0]) if False else None
        elif o == 0x86:
            info, nm = self.mn_pop(a[0])
            v = P()
            push(E("%s as %s" % (wrap(v, 9), info["name"]), 9))
        elif o == 0xB2:
            info, nm = self.mn_pop(a[0])
            v = P()
            push(E("%s is %s" % (wrap(v, 9), info["name"]), 9))
        elif o in (0x87, 0xB3):
            t, v = P(), P()
            push(E("%s %s %s" % (wrap(v, 9), "as" if o == 0x87 else "is", wrap(t, 10)), 9))
        elif o == 0xB1:
            b, c = P(), P()
            push(binop(c, "instanceof", b, 9))
        elif o == 0xB4:
            b, c = P(), P()
            push(binop(c, "in", b, 9))
        elif o == 0x90 or o == 0xC4:
            push(E("-" + wrap(P(), 13), 13))
        elif o == 0x97:
            push(E("~" + wrap(P(), 13), 13))
        elif o == 0x96:
            push(negate(P()))
        elif o == 0x95:
            push(E("typeof " + wrap(P(), 13), 13))
        elif o in (0x91, 0xC0):
            push(binop(P(), "+", E("1"), 11))
        elif o in (0x93, 0xC1):
            push(binop(P(), "-", E("1"), 11))
        elif o in (0xA0, 0xA1, 0xA2, 0xA3, 0xA4, 0xA5, 0xA6, 0xA7, 0xA8, 0xA9, 0xAA, 0xC5, 0xC6, 0xC7):
            sym = {0xA0: ("+", 11), 0xA1: ("-", 11), 0xA2: ("*", 12), 0xA3: ("/", 12), 0xA4: ("%", 12),
                   0xA5: ("<<", 10), 0xA6: (">>", 10), 0xA7: (">>>", 10), 0xA8: ("&", 7), 0xA9: ("|", 5),
                   0xAA: ("^", 6), 0xC5: ("+", 11), 0xC6: ("-", 11), 0xC7: ("*", 12)}[o]
            b, c = P(), P()
            push(binop(c, sym[0], b, sym[1]))
        elif o in (0xAB, 0xAC, 0xAD, 0xAE, 0xAF, 0xB0):
            b, c = P(), P()
            if o == 0xAB:
                push(cmp_e(c, "==", b, 8, "!="))
            elif o == 0xAC:
                push(cmp_e(c, "===", b, 8, "!=="))
            else:
                push(binop(c, {0xAD: "<", 0xAE: "<=", 0xAF: ">", 0xB0: ">="}[o], b, 9))
        elif o == 0x32:
            e = E("hasnext2(%s, %s)" % (self.lname(a[0]), self.lname(a[1])))
            push(e)
        elif o == 0x1E:
            i, ob = P(), P()
            push(E("__nextname(%s)" % strip_par(ob.s), 14))
        elif o == 0x23:
            i, ob = P(), P()
            push(E("__nextvalue(%s)" % strip_par(ob.s), 14))
        elif o == 0x1F:
            P(); P()
            push(E("hasnext()"))
        elif o in (0x06, 0x07):
            if o == 0x07:
                P()
        elif o == 0x31:
            pass
        else:
            self.out.append("// %s %s" % (x.name, a))


def sig(abc, mi, name):
    m = abc.methods[mi]
    ps = []
    nopt = len(m["opts"])
    for k in range(m["pc"]):
        nm = abc.s(m["pnames"][k]) if m["pnames"] else "arg%d" % (k + 1)
        t = abc.mn_str(m["ptypes"][k]) if m["ptypes"][k] else "*"
        s = "%s:%s" % (nm, t)
        oi = k - (m["pc"] - nopt)
        if oi >= 0:
            s += " = " + abc.const(m["opts"][oi][1], m["opts"][oi][0])
        ps.append(s)
    if m["flags"] & 4:
        ps.append("...rest")
    ret = abc.mn_str(m["ret"]) if m["ret"] else "*"
    return "function %s(%s):%s" % (name or "", ", ".join(ps), ret)


def method_body_lines(abc, mi, nested=0):
    body = abc.bodies.get(mi)
    if body is None:
        return ["// (no body - abstract/native method)"]
    try:
        ins = abc.parse_code(body["code"])
        if not ins:
            return []
        sim = AVM2Sim(abc, mi, body, ins, nested)
        a2i = {x.addr: i for i, x in enumerate(ins)}
        tries = []
        import bisect
        addrs = [x.addr for x in ins]
        for e in body["exc"]:
            tries.append(dict(**{"from": bisect.bisect_left(addrs, e["frm"])}, to=e["to"], target=e["target"],
                              var=abc.mn_str(e["var"]) if e["var"] else None,
                              type=abc.mn_str(e["type"]) if e["type"] else None))
        st = Structurer(ins, sim, tries)
        lines = st.block(0, len(ins), [])
        while lines and lines[-1] == "return;":
            lines.pop()
        return lines
    except Exception as ex:
        return ["// decompilation error: %s" % ex] + ["// " + l for l in abc.disasm(body["code"])]


def method_src(abc, mi, name, nested=0):
    lines = method_body_lines(abc, mi, nested)
    return "%s {\n%s\n}" % (sig(abc, mi, name), "\n".join(indent(lines)))


def vis(abc, nameidx):
    i = abc.mn_info(nameidx)
    k = NSKIND.get(i["nskind"], "")
    if k in ("public", ""):
        return "public"
    if k == "ns":
        return i["ns"] or "internal"
    return k


def trait_src(abc, t, static=False, owner_iface=False):
    nm = abc.mn_str(t["name"])
    v = vis(abc, t["name"])
    st = "static " if static else ""
    k = t["kind"]
    if k in (0, 6):
        ty = abc.mn_str(t["type"]) if t["type"] else "*"
        init = (" = " + abc.const(t["val"][0], t["val"][1])) if t["val"] else ""
        return ["%s %s%s %s:%s%s;" % (v, st, "const" if k == 6 else "var", nm, ty, init)]
    if k in (1, 2, 3):
        pre = "override " if t["attrs"] & 2 else ""
        pre += "final " if t["attrs"] & 1 else ""
        s = sig(abc, t["method"], "")
        s = s.replace("function (", "function %s%s(" % ({2: "get ", 3: "set "}.get(k, ""), nm), 1)
        body = method_body_lines(abc, t["method"])
        if owner_iface or t["method"] not in abc.bodies:
            return ["%s %s%s%s;" % (v, st, pre, s)]
        return ["%s %s%s%s {" % (v, st, pre, s)] + indent(body) + ["}"]
    if k == 5:
        return ["%s %sfunction %s = %s;" % (v, st, nm, method_src(abc, t["method"], nm))]
    return []


def dump_abc(data):
    """-> dict file_name -> text"""
    abc = ABC(data)
    files = {}
    seen_cls = set()
    for si, sc in enumerate(abc.scripts):
        for t in sc["traits"]:
            if t["kind"] != 4:
                continue
            ci = t["cls"]
            seen_cls.add(ci)
            inst, cl = abc.instances[ci], abc.classes[ci]
            info = abc.mn_info(inst["name"])
            is_iface = bool(inst["flags"] & 4)
            head = ["public" if not inst["flags"] & 0 else "public"]
            mods = ("final " if inst["flags"] & 2 else "") + ("dynamic " if inst["flags"] & 1 else "")
            sup = abc.mn_str(inst["super"]) if inst["super"] else ""
            ext = " extends %s" % sup if sup and sup != "Object" else ""
            ifs = ", ".join(abc.mn_str(i) for i in inst["ifaces"])
            if is_iface:
                decl = "public interface %s%s" % (info["name"], (" extends " + ifs) if ifs else "")
            else:
                decl = "public %sclass %s%s%s" % (mods, info["name"], ext, (" implements " + ifs) if ifs else "")
            body = []
            for tr in cl["traits"]:
                body += trait_src(abc, tr, True) + [""]
            cin = [l for l in method_body_lines(abc, cl["init"]) if l.strip()]
            if cin:
                body += ["// static initializer"] + cin + [""]
            if not is_iface:
                s = sig(abc, inst["init"], "").replace("function (", "function %s(" % info["name"], 1)
                s = re.sub(r"\):\*$", ")", s)
                body += ["public " + s + " {"] + indent(method_body_lines(abc, inst["init"])) + ["}", ""]
            for tr in inst["traits"]:
                body += trait_src(abc, tr, False, is_iface) + [""]
            pkg = info["ns"]
            txt = "package %s {\n%s\n}\n" % (pkg, "\n".join(indent([decl + " {"] + indent(body) + ["}"])))
            fn = ("%s.%s" % (pkg, info["name"]) if pkg else info["name"]) + ".as"
            files[fn] = txt
    for si, sc in enumerate(abc.scripts):
        lines = []
        for t in sc["traits"]:
            if t["kind"] != 4:
                lines += trait_src(abc, t)
        init = [l for l in method_body_lines(abc, sc["init"]) if l.strip()]
        if lines or init:
            files["script_%d.as" % si] = "\n".join(lines + ([""] if lines and init else []) + init) + "\n"
    return files, abc


def frame_stops(abc, symbols):
    """symbols: {cid: classname}. -> {cid: frame number (0-based) at which stop() is called}"""
    res = {}
    by_name = {}
    for ci, inst in enumerate(abc.instances):
        by_name[abc.full(inst["name"])] = ci
        by_name.setdefault(abc.mn_str(inst["name"]), ci)
    for cid, cname in symbols.items():
        ci = by_name.get(cname) if cname in by_name else by_name.get(cname.split(".")[-1])
        if ci is None:
            continue
        best = None
        for t in abc.instances[ci]["traits"]:
            if t["kind"] != 1:
                continue
            m = re.match(r"^frame(\d+)$", abc.mn_str(t["name"]))
            body = abc.bodies.get(t["method"])
            if not m or not body:
                continue
            for x in abc.parse_code(body["code"]):
                if x.op in (0x4F, 0x46) and abc.mn_str(x.args[0]) == "stop":
                    f = int(m.group(1)) - 1
                    best = f if best is None else min(best, f)
        if best is not None:
            res[cid] = best
    return res
'''))


def _load_embedded():
    for name, src in _EMBEDDED:
        if name in _sys.modules:
            continue
        mod = _types.ModuleType(name)
        mod.__file__ = "<embedded %s>" % name
        _sys.modules[name] = mod
        exec(compile(src, "<embedded %s>" % name, "exec"), mod.__dict__)


_load_embedded()

import argparse
import json
import math
import os
import sys

import swf_extract_v2 as v2
from swf_extract_v2 import *
from swf_abc import ABC, dump_abc, frame_stops
from swf_decomp import decompile_as2, disasm_as2, parse_actions
from swf_extra import (build_sfnt, cx_filter, decompose, filter_svg, flv_audio, fnum, html_runs, name_to_code,
                       parse_cff, parse_filters, smil)

__version__ = "3.0"
CATEGORIES3 = CATEGORIES + ["buttons", "timelines"]
MSTEPS = 64
CLIP_EVENTS = ["load", "enterFrame", "unload", "mouseMove", "mouseDown", "mouseUp", "keyDown", "keyUp", "data",
               "initialize", "press", "release", "releaseOutside", "rollOver", "rollOut", "dragOver", "dragOut",
               "keyPress", "construct"]
BTN_EVENTS = ["idleToOverUp", "overUpToIdle", "overUpToOverDown", "overDownToOverUp", "overDownToOutDown",
              "outDownToOverDown", "outDownToIdle", "idleToOverDown", "overDownToIdle"]


_orig_sound_payload = v2.sound_payload


def _sound_payload(fmt_, rate, bits, ch, blocks, count=None):
    if fmt_ in (4, 5, 6, 11):
        ri = RATES.index(rate) if rate in RATES else 3
        return "flv", flv_audio(fmt_, ri, bits == 16, ch == 2, blocks)
    return _orig_sound_payload(fmt_, rate, bits, ch, blocks, count)


v2.sound_payload = _sound_payload


def encu32(d, p):
    v = sh = 0
    while True:
        b = d[p]
        p += 1
        v |= (b & 0x7F) << sh
        sh += 7
        if not b & 0x80:
            return v, p


def parse_clip_actions(d, p, ver):
    p += 2
    p += 4 if ver >= 6 else 2
    res = []
    while p + 2 <= len(d):
        if ver >= 6:
            fl = u32(d, p)
            p += 4
        else:
            fl = u16(d, p)
            p += 2
        if fl == 0:
            break
        sz = u32(d, p)
        p += 4
        key = None
        data = d[p:p + sz]
        if ver >= 6 and fl & (1 << 17) and data:
            key, data = data[0], data[1:]
        names = [n for i, n in enumerate(CLIP_EVENTS) if fl & (1 << i)]
        res.append(dict(events=names, key=key, actions=bytes(data)))
        p += sz
    return res


def place3(code, d, disp, fidx, ver, ctr):
    b = Bits(d)

    def new(**kw):
        ctr[0] += 1
        o = dict(id=None, depth=None, m=None, cx=None, ratio=None, clip=0, blend=None, vis=True, f0=fidx,
                 inst=ctr[0], name=None, filters=None, cache=False, bg=None, cls=None, cactions=None)
        o.update(kw)
        return o

    if code == 4:
        cid, depth = b.u16(), b.u16()
        m = b.matrix()
        cx = b.cxform(False) if b.left() > 0 else None
        disp[depth] = new(id=cid, depth=depth, m=m, cx=cx)
        return
    fl = b.u8()
    fl3 = b.u8() if code == 70 else 0
    depth = b.u16()
    cls = None
    if code == 70 and (fl3 & 8 or (fl3 & 0x10 and fl & 2)):
        cls = b.cstr()
    cid = b.u16() if fl & 2 else None
    m = b.matrix() if fl & 4 else None
    cx = b.cxform(True) if fl & 8 else None
    ratio = b.u16() if fl & 16 else None
    name = b.cstr() if fl & 32 else None
    clip = b.u16() if fl & 64 else None
    filters = blend = cache = vis = bg = ca = None
    try:
        if code == 70:
            if fl3 & 1:
                filters, p = parse_filters(d, b.pos())
                b.p = p * 8
            if fl3 & 2:
                blend = b.u8()
            if fl3 & 4:
                cache = b.u8()
            if fl3 & 0x20:
                vis = b.u8()
            if fl3 & 0x40:
                bg = b.rgba()
        if fl & 0x80:
            ca = parse_clip_actions(d, b.pos(), ver)
    except Exception as e:
        warn("PlaceObject: tag tail: %s" % e)
    old = disp.get(depth)
    if cid is not None and (not fl & 1 or old is None):
        disp[depth] = new(id=cid, depth=depth, m=m, cx=cx, ratio=ratio, clip=clip or 0, blend=blend,
                          vis=True if vis is None else bool(vis), name=name, filters=filters,
                          cache=bool(cache), bg=bg, cls=cls, cactions=ca)
        return
    if old is None:
        return
    o = dict(old)
    if cid is not None:
        ctr[0] += 1
        o.update(id=cid, inst=ctr[0], f0=fidx)
    for k, val in (("m", m), ("cx", cx), ("ratio", ratio), ("clip", clip), ("blend", blend), ("name", name),
                   ("filters", filters), ("bg", bg), ("cactions", ca)):
        if val is not None:
            o[k] = val
    if vis is not None:
        o["vis"] = bool(vis)
    disp[depth] = o


def build_timeline3(tags, ver):
    frames, disp, labels, ctr = [], {}, {}, [0]
    extra = dict(actions={}, sounds={}, cactions=[], init=[])
    for code, d in tags:
        try:
            if code == 1:
                frames.append([dict(disp[k]) for k in sorted(disp)])
            elif code in (4, 26, 70):
                place3(code, d, disp, len(frames), ver, ctr)
            elif code == 5:
                disp.pop(u16(d, 2), None)
            elif code == 28:
                disp.pop(u16(d, 0), None)
            elif code == 43:
                labels[len(frames)] = Bits(d).cstr()
            elif code == 12:
                extra["actions"].setdefault(len(frames), []).append(d)
            elif code == 59:
                extra["init"].append((len(frames), u16(d, 0), d[2:]))
            elif code == 15:
                extra["sounds"].setdefault(len(frames), []).append(d)
        except Exception as e:
            warn("timeline, tag %d: %s" % (code, e))
    if not frames and disp:
        frames.append([dict(disp[k]) for k in sorted(disp)])
    seen = set()
    for fi, items in enumerate(frames):
        for it in items:
            if it.get("cactions") and it["inst"] not in seen:
                seen.add(it["inst"])
                extra["cactions"].append((fi, it["depth"], it["id"], it["cactions"]))
    return frames, labels, extra


def tracks(frames, n):
    T = {}
    for k in range(min(n, len(frames))):
        for it in frames[k]:
            t = T.setdefault(it["inst"], dict(depth=it["depth"], id=it["id"], a=k, items={}, b=k + 1))
            t["items"][k] = it
            t["b"] = k + 1
    return sorted(T.values(), key=lambda t: (t["depth"], t["a"]))


def fill(vals, a, b, n):
    """vals: dict frame->value (within [a,b)). -> list of length n with no gaps."""
    first = vals[a]
    out, last = [], first
    for k in range(n):
        if k in vals:
            last = vals[k]
        out.append(last if k >= a else first)
    return out


class Renderer3(Renderer):
    def __init__(self, ex):
        super().__init__(ex)
        self.fcache = {}
        self.fps = ex.fps

    def filter_id(self, flist):
        key = repr(flist)
        if key not in self.fcache:
            fid = self.uid("fx")
            try:
                self.defs.append(filter_svg(fid, flist))
            except Exception as e:
                warn("filter: %s" % e)
                fid = None
            self.fcache[key] = fid
        return self.fcache[key]

    def cx_id(self, cx):
        key = ("cx",) + tuple(cx)
        if key not in self.fcache:
            fid = self.uid("cx")
            self.defs.append(cx_filter(fid, cx))
            self.fcache[key] = fid
        return self.fcache[key]

    def attrs(self, it):
        a = ""
        m = it.get("m")
        if m and tuple(m) != IDENT:
            a += ' transform="%s"' % mat_str(m)
        if it.get("cx"):
            a += self.cx_attrs(it["cx"])
        bl = BLEND.get(it.get("blend"))
        if bl:
            a += ' style="mix-blend-mode:%s"' % bl
        return a

    def item(self, it, f, depth):
        kind = self.ex.kind(it["id"])
        if kind == "morph" and not (depth > 12 or it.get("vis") is False):
            q = 1000 + int(round((it.get("ratio") or 0) / 65535.0 * MSTEPS))
            s = '<use xlink:href="#%s"%s/>' % (self.shape(it["id"], q), self.attrs(it))
        else:
            s = super().item(it, f, depth)
        if s and it.get("filters"):
            fid = self.filter_id(it["filters"])
            if fid:
                s = '<g filter="url(#%s)">%s</g>' % (fid, s)
        return s

    def root(self, tid, n, loop):
        if n <= 1:
            return "<g>%s</g>" % self.frame(tid, 0)
        D = n / self.fps
        ck = self.uid("ck")
        begin = "0s;%s.end" % ck if loop else "0s"
        clock = '<set id="%s" attributeName="display" to="inline" begin="%s" dur="%.6fs"/>' % (ck, begin, D)
        return clock + self.timeline_body(tid, n, ck, D, 0)

    def timeline_body(self, tid, n, ck, D, depth):
        frames = self.ex.timeline(tid)[0]
        T = tracks(frames, n)
        out, used = [], set()
        for i, t in enumerate(T):
            if i in used:
                continue
            clipd = max((it.get("clip") or 0) for it in t["items"].values())
            if clipd:
                kids = []
                for j in range(i + 1, len(T)):
                    if T[j]["depth"] <= clipd and j not in used:
                        kids.append(j)
                        used.add(j)
                inner = "".join(self.inst(T[j], n, D, ck, depth) for j in kids)
                out.append(self.clip_group(t, inner, n, D, ck))
            else:
                out.append(self.inst(t, n, D, ck, depth))
        return "".join(out)

    def clip_group(self, t, inner, n, D, ck):
        d = self.ex.clip_d(t["id"]) if self.ex.kind(t["id"]) in ("shape", "morph") else None
        if not d:
            return inner
        a, b = t["a"], min(t["b"], n)
        ms = fill({k: tuple(t["items"][k].get("m") or IDENT) for k in range(a, b) if k in t["items"]}, a, b, n)
        ids = {}
        for m in ms:
            if m not in ids:
                cid = self.uid("c")
                ids[m] = cid
                tr = ' transform="%s"' % mat_str(m) if m != IDENT else ""
                self.defs.append('<clipPath id="%s"><path d="%s"%s clip-rule="evenodd"/></clipPath>' % (cid, d, tr))
        vals = ["url(#%s)" % ids[ms[k]] if a <= k < b else "none" for k in range(n)]
        st, an = smil("clip-path", vals, n, D, ck + ".begin")
        return '<g clip-path="%s">%s%s</g>' % (st or vals[0], an, inner)

    def inst(self, t, n, D, ck, depth):
        if depth > 12:
            return ""
        a, b, items, cid = t["a"], min(t["b"], n), t["items"], t["id"]
        if a >= n:
            return ""
        kind = self.ex.kind(cid)
        begin = ck + ".begin"
        P = lambda key, dflt=None: fill({k: (items[k].get(key) if items[k].get(key) is not None else dflt)
                                         for k in range(a, b) if k in items}, a, b, n)
        alive = ["inline" if (a <= k < b and items.get(k, {}).get("vis", True)) else "none" for k in range(n)]
        content = ""
        if kind == "shape":
            content = '<use xlink:href="#%s"/>' % self.shape(cid)
        elif kind == "text":
            content = '<use xlink:href="#%s"/>' % self.text(cid)
        elif kind == "edit":
            content = self.ex.edit_svg(cid)
        elif kind == "morph":
            qs = [1000 + int(round((r or 0) / 65535.0 * MSTEPS)) for r in P("ratio", 0)]
            vs = set(qs[k] for k in range(a, b))
            if len(vs) == 1:
                content = '<use xlink:href="#%s"/>' % self.shape(cid, qs[a])
            else:
                for q in sorted(vs):
                    vv = ["inline" if (a <= k < b and qs[k] == q and alive[k] == "inline") else "none" for k in range(n)]
                    st, an = smil("display", vv, n, D, begin)
                    if st == "none":
                        continue
                    content += '<g%s>%s<use xlink:href="#%s"/></g>' % ("" if st else ' display="none"', an, self.shape(cid, q))
        elif kind == "sprite":
            content = self.sprite_inst(cid, a, n, D, ck, depth)
        if not content:
            return ""
        layers = []
        st, an = smil("display", alive, n, D, begin)
        if st == "none":
            return ""
        if an:
            layers.append((' display="none"', an))
        bl = next((BLEND.get(it.get("blend")) for it in items.values() if BLEND.get(it.get("blend"))), None)
        if bl:
            layers.append((' style="mix-blend-mode:%s"' % bl, ""))
        ms = P("m")
        ms = [tuple(m) if m else IDENT for m in ms]
        if len(set(ms)) == 1:
            if ms[0] != IDENT:
                layers.append((' transform="%s"' % mat_str(ms[0]), ""))
        else:
            dec = [decompose(m) for m in ms]
            if any(x is None for x in dec):
                layers.append((' transform="%s"' % mat_str(ms[a]), ""))
            else:
                spec = [("translate", lambda x: "%s %s" % (fnum(x[0]), fnum(x[1])), "0 0"),
                        ("rotate", lambda x: fnum(x[2]), "0"),
                        ("skewX", lambda x: fnum(x[3]), "0"),
                        ("scale", lambda x: "%s %s" % (fnum(x[4]), fnum(x[5])), "1 1")]
                for kindn, fn, ident in spec:
                    vals = [fn(x) for x in dec]
                    st, an = smil("transform", vals, n, D, begin, kind=kindn)
                    if an:
                        layers.append(("", an))
                    elif st != ident:
                        layers.append((' transform="%s(%s)"' % (kindn, st), ""))
        cxs = P("cx")
        ops, fvs = [], []
        flts = P("filters")
        for k in range(n):
            cx, fl = cxs[k], flts[k]
            op, parts = "1", []
            if cx:
                rm, gm, bm, am, ra, ga, ba, aa = cx
                if (rm, gm, bm) == (1, 1, 1) and ra == ga == ba == aa == 0 and am <= 1:
                    op = fnum(max(0.0, am))
                elif tuple(cx) != (1, 1, 1, 1, 0, 0, 0, 0):
                    parts.append("url(#%s)" % self.cx_id(cx))
            if fl:
                fid = self.filter_id(fl)
                if fid:
                    parts.append("url(#%s)" % fid)
            ops.append(op)
            fvs.append(" ".join(parts) if parts else "none")
        for attr, vals, dflt in (("opacity", ops, "1"), ("filter", fvs, "none")):
            st, an = smil(attr, vals, n, D, begin)
            if an:
                layers.append(("", an))
            elif st != dflt:
                layers.append((' %s="%s"' % (attr, st), ""))
        res = content
        for at, an in reversed(layers):
            res = "<g%s>%s%s</g>" % (at, an, res)
        return res

    def sprite_inst(self, cid, a, n, D, ck, depth):
        nc, loop = self.ex.effective(cid)
        if nc == 0:
            return ""
        if self.ex.is_static(cid):
            return '<use xlink:href="#%s"/>' % self.sprite(cid, 0, depth + 1)
        Dc = nc / self.fps
        ckc = self.uid("ck")
        begin = "%s.begin+%.6fs" % (ck, a / self.fps)
        if loop:
            begin += ";%s.end" % ckc
        clock = '<set id="%s" attributeName="display" to="inline" begin="%s" dur="%.6fs"/>' % (ckc, begin, Dc)
        return "<g>%s%s</g>" % (clock, self.timeline_body(cid, nc, ckc, Dc, depth + 1))


def parse_font_full(code, d):
    b = Bits(d)
    fid = b.u16()
    flags = b.u8()
    b.u8()
    nl = b.u8()
    name = b.bytes(nl).decode("utf-8", "replace").rstrip("\0")
    n = b.u16()
    wide_off, wide_codes = flags & 8, flags & 4 or code == 75
    start = b.pos()
    offs = [b.u32() if wide_off else b.u16() for _ in range(n)]
    code_off = b.u32() if wide_off else b.u16()
    recs = []
    for o in offs:
        try:
            bb = Bits(d, start + o)
            nf, nl_ = bb.ub(4), bb.ub(4)
            recs.append(read_records(bb, nf, nl_, 1))
        except Exception:
            recs.append([])
    b.p = (start + code_off) * 8
    codes = [b.u16() if wide_codes else b.u8() for _ in range(n)]
    f = dict(id=fid, name=name, glyphs=recs, codes=codes, bold=bool(flags & 1), italic=bool(flags & 2),
             em=20480 if code == 75 else 1024, adv=None, ascent=None, descent=None, leading=0, kern={})
    if flags & 0x80:
        f["ascent"], f["descent"], f["leading"] = b.s16(), b.s16(), b.s16()
        f["adv"] = [b.s16() for _ in range(n)]
        for _ in range(n):
            b.rect()
        kc = b.u16()
        for _ in range(kc):
            c1, c2 = (b.u16(), b.u16()) if wide_codes else (b.u8(), b.u8())
            f["kern"][(c1, c2)] = b.s16()
    return f


def font_points(records, k):
    """Glyph records -> contours [(x, y, on)] (y up), scale k."""
    out, cur, pos = [], None, None
    for r in records:
        if r[0] == "s":
            if r[1] is not None:
                cur = [(r[1][0] * k, -r[1][1] * k, 1)]
                out.append(cur)
                pos = (r[1][0], r[1][1])
            continue
        if cur is None or pos != (r[1], r[2]):
            cur = [(r[1] * k, -r[2] * k, 1)]
            out.append(cur)
        if r[0] == "l":
            cur.append((r[3] * k, -r[4] * k, 1))
            pos = (r[3], r[4])
        else:
            cur.append((r[3] * k, -r[4] * k, 0))
            cur.append((r[5] * k, -r[6] * k, 1))
            pos = (r[5], r[6])
    return out


def parse_button(code, d):
    b = Bits(d)
    bid = b.u16()
    if code == 34:
        b.u8()
        b.u16()
    recs = []
    while True:
        fl = b.u8()
        if fl == 0:
            break
        cid, depth = b.u16(), b.u16()
        m = b.matrix()
        cx = flt = bl = None
        if code == 34:
            cx = b.cxform(True)
            if fl & 0x10:
                flt, p = parse_filters(d, b.pos())
                b.p = p * 8
            if fl & 0x20:
                bl = b.u8()
        recs.append(dict(states=fl & 15, id=cid, depth=depth, m=m, cx=cx, filters=flt, blend=bl))
    acts = []
    p = b.pos()
    if code == 7:
        acts.append(dict(events=["press"], key=None, actions=bytes(d[p:])))
    else:
        while p + 4 <= len(d):
            size = u16(d, p)
            cond = u16(d, p + 2)
            end = p + size if size else len(d)
            evs = [BTN_EVENTS[i] for i in range(9) if cond & (1 << i)]
            key = cond >> 9
            acts.append(dict(events=evs, key=key or None, actions=bytes(d[p + 4:end])))
            if not size:
                break
            p = end
    return dict(id=bid, records=recs, actions=acts)


def parse_edit3(d):
    b = Bits(d)
    cid = b.u16()
    bounds = b.rect()
    f1, f2 = b.u8(), b.u8()
    o = dict(id=cid, bounds=bounds, html=bool(f2 & 2), text="", var="", font=None, fontclass="", height=240,
             color=(0, 0, 0, 255), align=0, lm=0, rm=0, indent=0, leading=0, wrap=bool(f1 & 0x40),
             multi=bool(f1 & 0x20), password=bool(f1 & 0x10))
    if f1 & 1:
        o["font"] = b.u16()
    if f2 & 0x80:
        o["fontclass"] = b.cstr()
    if f1 & 1 or f2 & 0x80:
        o["height"] = b.u16()
    if f1 & 4:
        o["color"] = b.rgba()
    if f1 & 2:
        b.u16()
    if f2 & 0x20:
        o["align"], o["lm"], o["rm"], o["indent"], o["leading"] = b.u8(), b.u16(), b.u16(), b.u16(), b.s16()
    o["var"] = b.cstr()
    if f1 & 0x80:
        o["text"] = b.cstr()
    return o


class Extractor3(Extractor):
    def __init__(self, swf, raw=False, decompile=True):
        super().__init__(swf, raw)
        self.main_all, self.buttons, self.abcs, self.symbols = [], {}, [], {}
        self.scenes, self.finfo, self.stops = [], {}, {}
        self.decompile = decompile
        self.ver = swf["version"]
        self._tl3, self._eff = {}, {}

    def feed(self):
        for code, d in iter_tags(self.swf["body"], self.swf["pos"]):
            nm = TAGNAMES.get(code, "Tag%d" % code)
            self.hist[nm] = self.hist.get(nm, 0) + 1
            if code in TIMELINE:
                self.main_tags.append((code, d))
            if code in TIMELINE or code in (12, 15, 59):
                self.main_all.append((code, d))
            try:
                self.handle(code, d)
            except Exception as e:
                warn("tag %s: %s" % (nm, e))
        self.post()

    def handle(self, code, d):
        super().handle(code, d)
        if code in (7, 34):
            self.buttons[u16(d, 0)] = parse_button(code, d)
        elif code == 76:
            b = Bits(d, 2)
            for _ in range(u16(d, 0)):
                cid = b.u16()
                self.symbols[cid] = b.cstr()
        elif code == 86:
            p = 0
            ns, p = encu32(d, p)
            for _ in range(ns):
                off, p = encu32(d, p)
                e = d.find(b"\0", p)
                self.scenes.append(dict(offset=off, name=d[p:e].decode("utf-8", "replace")))
                p = e + 1
            nl, p = encu32(d, p)
            labels = []
            for _ in range(nl):
                fr, p = encu32(d, p)
                e = d.find(b"\0", p)
                labels.append(dict(frame=fr, label=d[p:e].decode("utf-8", "replace")))
                p = e + 1
            self.scene_labels = labels
        elif code in (13, 62):
            b = Bits(d)
            fid = b.u16()
            nl = b.u8()
            nm = b.bytes(nl).decode("utf-8", "replace").rstrip("\0")
            fl = b.u8()
            if code == 62:
                b.u8()
            wide = fl & 1
            cds = []
            while b.left() >= (2 if wide else 1):
                cds.append(b.u16() if wide else b.u8())
            self.finfo[fid] = dict(name=nm, codes=cds, bold=bool(fl & 2), italic=bool(fl & 4))
        elif code in (72, 82):
            try:
                data = d
                if code == 82:
                    s = Bits(d, 4).cstr()
                    data = d[4 + len(s.encode("utf-8")) + 1:]
                self.abcs.append(ABC(data))
            except Exception as e:
                warn("ABC: %s" % e)

    def post(self):
        for tid in [None] + sorted(self.sprites):
            ex = self.timeline(tid)[2]
            for fno in sorted(ex["actions"]):
                if any(self.has_stop(a) for a in ex["actions"][fno]):
                    self.stops[tid] = fno
                    break
        for abc in self.abcs:
            try:
                for cid, f in frame_stops(abc, self.symbols).items():
                    tid = None if cid == 0 else cid
                    self.stops[tid] = min(self.stops.get(tid, f), f)
            except Exception:
                pass

    @staticmethod
    def has_stop(a):
        try:
            ins = parse_actions(a)
        except Exception:
            return False
        if any(x.kind in ("jmp", "cjmp") for x in ins):
            return False
        return any(x.op == 0x07 for x in ins)

    def timeline(self, tid):
        if tid not in self._tl3:
            tags = self.main_all if tid is None else self.sprites[tid]["tags"]
            self._tl3[tid] = build_timeline3(tags, self.ver)
        return self._tl3[tid]

    def effective(self, tid):
        """-> (frames, looped)"""
        if tid in self._eff:
            return self._eff[tid]
        n = len(self.timeline(tid)[0])
        loop = True
        st = self.stops.get(tid)
        if st is not None:
            n, loop = min(n, st + 1), False
        n = min(n, self.max_frames) if getattr(self, "max_frames", 0) else n
        self._eff[tid] = (n, loop)
        return self._eff[tid]

    def is_static(self, tid, seen=()):
        n, _ = self.effective(tid)
        if n > 1:
            return False
        for it in (self.timeline(tid)[0][:1] or [[]])[0]:
            if self.kind(it["id"]) == "sprite" and it["id"] not in seen and not self.is_static(it["id"], seen + (tid,)):
                return False
        return True

    def shape_geom(self, sid, q=None):
        if sid in self.morphs and q is not None and q >= 1000:
            return v2.morph_geom(self.morph(sid), (q - 1000) / float(MSTEPS))
        return super().shape_geom(sid, q)

    def font_family(self, o):
        if o["fontclass"]:
            return o["fontclass"] + ",sans-serif"
        f = self.font(o["font"]) if o["font"] is not None else None
        return ((f["name"] + ",") if f and f["name"] else "") + "sans-serif"

    def edit_svg(self, cid):
        o = parse_edit3(self.edits[cid])
        if not o["text"]:
            return ""
        x0, x1, y0, _ = o["bounds"]
        h = o["height"]
        col = hx(o["color"])
        runs = html_runs(o["text"], col, h) if o["html"] else [(o["text"], dict(color=col, size=h, b=False, i=False))]
        lines, cur = [], []
        for txt, st in runs:
            for k, part in enumerate(txt.replace("\r", "\n").split("\n")):
                if k:
                    lines.append(cur)
                    cur = []
                if part:
                    sz = st["size"] * 20 if o["html"] and st["size"] < 200 else st["size"]
                    cur.append((part, st, sz))
        lines.append(cur)
        width = (x1 - x0) - 80 - o["lm"] - o["rm"]
        if o["wrap"] and width > 0:
            wrapped = []
            for ln in lines:
                acc, w = [], 0
                for part, st, sz in ln:
                    for word in part.split(" "):
                        ww = (len(word) + 1) * sz * 0.5
                        if acc and w + ww > width:
                            wrapped.append(acc)
                            acc, w = [], 0
                        acc.append((word + " ", st, sz))
                        w += ww
                wrapped.append(acc)
            lines = wrapped
        anchor, tx = {1: ("end", x1 - 40 - o["rm"]), 2: ("middle", (x0 + x1) / 2.0)}.get(o["align"], ("start", x0 + 40 + o["lm"]))
        fam = self.font_family(o)
        out, y = [], y0 + 40 + h * 0.85
        for ln in lines:
            spans = "".join('<tspan fill="%s" font-size="%s"%s%s>%s</tspan>' % (
                st["color"] if str(st["color"]).startswith("#") else hx(o["color"]), fnum(sz),
                ' font-weight="bold"' if st["b"] else "", ' font-style="italic"' if st["i"] else "",
                htmlmod.escape(("•" * len(p)) if o["password"] else p)) for p, st, sz in ln)
            if spans:
                out.append('<text x="%s" y="%s" text-anchor="%s" xml:space="preserve" font-family="%s">%s</text>' % (
                    fnum(tx), fnum(y), anchor, fam, spans))
            y += h * 1.2 + o["leading"]
        return "".join(out)

    def emit(self, kind, fname, data, **meta):
        if isinstance(data, str):
            data = data.encode("utf-8")
        d = os.path.join(self.outdir, kind)
        os.makedirs(d, exist_ok=True)
        k, stem = 1, fname
        while (kind, fname) in self.taken:
            k += 1
            base, dot, ext = stem.rpartition(".")
            fname = "%s_%d.%s" % (base, k, ext)
        self.taken.add((kind, fname))
        with open(os.path.join(d, fname), "wb") as fh:
            fh.write(data)
        self.manifest.append(dict(file="%s/%s" % (kind, fname), kind=kind, size=len(data), **meta))

    def save(self, outdir, only, want_frames, max_frames):
        self.max_frames = max_frames
        self._eff.clear()
        self.outdir = outdir
        only = set(only)
        v2_only = only - {"fonts", "sprites"}
        manifest = super().save(outdir, v2_only, want_frames, max_frames or 10 ** 9)
        self.manifest = manifest
        self.taken = set((m["kind"], os.path.basename(m["file"])) for m in manifest)
        g = lambda what, fn: self.guard(what, fn)
        if "sprites" in only:
            self.save_sprites()
        if "fonts" in only:
            self.save_fonts()
        if "buttons" in only:
            self.save_buttons()
        if "scripts" in only and self.decompile:
            self.save_scripts()
        if "timelines" in only:
            self.save_timelines()
        self.write_info()
        return self.manifest

    def guard(self, what, fn):
        try:
            fn()
        except Exception as e:
            warn("%s: %s" % (what, e))

    def sname(self, cid):
        nm = self.names.get(cid)
        return "%s_%s" % (cid, safe(nm)) if nm else str(cid)

    def save_sprites(self):
        for sid in sorted(self.sprites) + [None]:
            def f(sid=sid):
                n, loop = self.effective(sid)
                if not self.timeline(sid)[0] or n == 0:
                    return
                box = self.swf["rect"] if sid is None else self.bbox(sid)
                if box is None:
                    return
                r = Renderer3(self)
                body = r.root(sid, n, loop)
                if not body.strip("<g></g>"):
                    # empty first frame + stop(): the animation starts later via gotoAndPlay,
                    # so render the whole timeline, otherwise the sprite is silently lost
                    tfr = self.timeline(sid)[0]
                    nfull = len(tfr)
                    if nfull <= n or not any(len(fr) for fr in tfr[n:]):
                        return
                    body = r.root(sid, nfull, False)
                    if not body.strip("<g></g>"):
                        return
                doc = r.document(box, body, self.bg if sid is None else None)
                self.emit("sprites", "main.svg" if sid is None else "%s.svg" % self.sname(sid), doc, id=sid, tag=39)
            self.guard("sprite %s" % ("main" if sid is None else sid), f)

    def save_fonts(self):
        adv = {}
        for tid, (code, d) in self.texts.items():
            try:
                t = parse_text(d, code == 33)
                for rec in t["recs"]:
                    gl = rec["glyphs"]
                    f = self.fontdefs.get(rec["font"])
                    if not f:
                        continue
                    em = 20480 if f[0] == 75 else 1024
                    for (g1, x1), (g2, x2) in zip(gl, gl[1:]):
                        adv.setdefault((rec["font"], g1), (x2 - x1) * em / float(rec["height"]))
            except Exception:
                pass
        for fid in sorted(self.fontdefs):
            def f(fid=fid):
                code, d = self.fontdefs[fid]
                if code == 91:
                    b = Bits(d, 2)
                    fl = b.u8()
                    name = b.cstr()
                    if not fl & 4:
                        return
                    cff = d[b.pos():]
                    if cff[:4] in (b"OTTO", b"\x00\x01\x00\x00", b"true"):
                        # the data is already a ready-made sfnt (OpenType/TrueType) - save as is
                        ext = "otf" if cff[:4] == b"OTTO" else "ttf"
                        self.emit("fonts", "%d_%s.%s" % (fid, safe(name), ext), cff, id=fid, tag=91)
                        return
                    self.emit("fonts", "%d_%s.cff" % (fid, safe(name)), cff, id=fid, tag=91)
                    try:
                        ci = parse_cff(cff)
                        codes = [name_to_code(x) for x in ci["names"]]
                        n = ci["n"]
                        otf = build_sfnt(name or "SWFFont%d" % fid, 1000, [[] for _ in range(n)], ci["widths"], codes,
                                         800, 200, 0, bool(fl & 1), bool(fl & 2), None, cff=cff)
                        self.emit("fonts", "%d_%s.otf" % (fid, safe(name)), otf, id=fid, tag=91)
                    except Exception as e:
                        warn("CFF->OTF %d: %s" % (fid, e))
                    return
                if code == 10:
                    ft = v2.parse_font(code, d)
                    ft.update(leading=0, kern={})
                else:
                    ft = parse_font_full(code, d)
                info = self.finfo.get(fid)
                if info:
                    if not ft.get("codes"):
                        ft["codes"] = info["codes"]
                    ft["name"] = ft["name"] or info["name"]
                    ft["bold"], ft["italic"] = ft["bold"] or info["bold"], ft["italic"] or info["italic"]
                ft["name"] = ft["name"] or self.fontnames.get(fid, "") or "SWFFont%d" % fid
                if not ft["glyphs"]:
                    return
                em = ft["em"]
                k = 2048.0 / em if em == 20480 else 1.0
                upm = 2048 if em == 20480 else 1024
                n = len(ft["glyphs"])
                codes = (list(ft["codes"] or []) + [0] * n)[:n]
                ad = []
                for i in range(n):
                    if ft.get("adv"):
                        ad.append(ft["adv"][i] * k)
                    elif (fid, i) in adv:
                        ad.append(adv[(fid, i)] * k)
                    else:
                        ad.append(upm * 0.5)
                pts = [font_points(g, k) for g in ft["glyphs"]]
                asc = int((ft.get("ascent") or em * 0.8) * k)
                dsc = int((ft.get("descent") or em * 0.2) * k)
                kern = {c: v * k for c, v in (ft.get("kern") or {}).items()}
                ttf = build_sfnt(ft["name"], upm, [[]] + pts, [upm * 0.3] + ad, [0] + codes, asc, dsc,
                                 int((ft.get("leading") or 0) * k), ft["bold"], ft["italic"], kern)
                self.emit("fonts", "%s.ttf" % self.fname_font(fid, ft["name"]), ttf, id=fid, tag=code)
            self.guard("font %d" % fid, f)

    @staticmethod
    def fname_font(fid, name):
        return "%d_%s" % (fid, safe(name)) if name else str(fid)

    def save_buttons(self):
        for bid, bt in sorted(self.buttons.items()):
            for st, label in ((1, "up"), (2, "over"), (4, "down"), (8, "hit")):
                def f(bid=bid, bt=bt, st=st, label=label):
                    items = [dict(id=r["id"], depth=r["depth"], m=r["m"], cx=r["cx"], ratio=None, clip=0,
                                  blend=r["blend"], vis=True, f0=0, filters=r["filters"])
                             for r in sorted(bt["records"], key=lambda r: r["depth"]) if r["states"] & st]
                    if not items:
                        return
                    box = None
                    for it in items:
                        try:
                            bb = self.char_bounds(it["id"], ())
                        except Exception:
                            bb = None
                        if bb:
                            box = union(box, xf_box(bb, it["m"] or IDENT))
                    if box is None:
                        return
                    r = Renderer3(self)
                    body = "".join(r.item(it, 0, 0) for it in items)
                    self.emit("buttons", "%s_%s.svg" % (self.sname(bid), label), r.document(box, body), id=bid, state=label)
                self.guard("button %d" % bid, f)

    def walk(self, tags):
        """(frame number, code, data) for every tag in the list."""
        fr = 0
        for code, d in tags:
            yield fr, code, d
            if code == 1:
                fr += 1

    def as2_file(self, name, data, header=""):
        try:
            src = "\n".join(decompile_as2(data))
        except Exception as e:
            src = "// error: %s" % e
        self.emit("scripts", name + ".as", (header + "\n" if header else "") + src + "\n")
        self.emit("scripts", name + ".asm.txt", "\n".join(disasm_as2(data)) + "\n")

    def save_scripts(self):
        for i, abc in enumerate(self.abcs):
            def f(i=i, abc=abc):
                files, _ = dump_abc(abc_raw(abc))
                for fn, txt in files.items():
                    self.emit("scripts", "abc%d__%s" % (i, fn), txt)
                self.emit("scripts", "abc%d.asm.txt" % i, "\n".join(
                    "// method %d\n%s" % (m, "\n".join(abc.disasm(b["code"]))) for m, b in sorted(abc.bodies.items())))
            self.guard("AS3 %d" % i, f)
        for scope, tags in [("main", self.main_all)] + [("sprite%d" % s, self.sprites[s]["tags"]) for s in sorted(self.sprites)]:
            for fr, code, d in self.walk(tags):
                if code == 12 and d:
                    self.guard("AS2", lambda: self.as2_file("%s_frame%03d" % (scope, fr + 1), d, "// %s, frame %d" % (scope, fr + 1)))
                elif code == 59:
                    self.guard("AS2", lambda: self.as2_file("%s_init_%d" % (scope, u16(d, 0)), d[2:], "// DoInitAction of sprite %d" % u16(d, 0)))
        for tid in [None] + sorted(self.sprites):
            for fi, depth, cid, cas in self.timeline(tid)[2]["cactions"]:
                for k, ca in enumerate(cas):
                    ev = ",".join(ca["events"]) + (" key=%s" % ca["key"] if ca["key"] else "")
                    self.guard("clipaction", lambda: self.as2_file(
                        "clip_%s_f%03d_d%d_%d" % ("main" if tid is None else tid, fi + 1, depth, k), ca["actions"],
                        "// onClipEvent(%s), clip %d" % (ev, cid)))
        for bid, bt in self.buttons.items():
            for k, a in enumerate(bt["actions"]):
                self.guard("button", lambda: self.as2_file("button_%d_%d" % (bid, k), a["actions"],
                                                           "// on(%s)" % ",".join(a["events"])))

    def save_timelines(self):
        for tid in [None] + sorted(self.sprites):
            def f(tid=tid):
                frames, labels, ex = self.timeline(tid)
                n, loop = self.effective(tid)
                data = dict(id=tid, frames=len(frames), effective_frames=n, loops=loop, labels=labels,
                            sounds={k: [u16(x, 0) for x in v] for k, v in ex["sounds"].items()},
                            display_list=[[{k: v for k, v in it.items() if k not in ("cactions",) and v not in (None, False, [], 0)}
                                           for it in fr] for fr in frames])
                self.emit("timelines", "%s.json" % ("main" if tid is None else self.sname(tid)),
                          json.dumps(data, ensure_ascii=False, default=str))
            self.guard("timeline", f)

    def write_info(self):
        r = self.swf["rect"]
        info = dict(tool="swf_extract %s" % __version__, version=self.swf["version"], compression=self.swf["sig"],
                    stage_px=[(r[1] - r[0]) / 20.0, (r[3] - r[2]) / 20.0], fps=self.fps, frames=self.swf["nframes"],
                    tags=self.hist, symbols={str(k): v for k, v in self.symbols.items()},
                    exports={str(k): v for k, v in self.names.items()},
                    frame_labels={str(k): v for k, v in self.timeline(None)[1].items()},
                    scenes=self.scenes, scene_labels=getattr(self, "scene_labels", []),
                    stop_frames={("main" if k is None else str(k)): v + 1 for k, v in self.stops.items()},
                    metadata=self.meta)
        with open(os.path.join(self.outdir, "info.json"), "w", encoding="utf-8") as fh:
            json.dump(info, fh, ensure_ascii=False, indent=2)
        with open(os.path.join(self.outdir, "manifest.json"), "w", encoding="utf-8") as fh:
            json.dump(self.manifest, fh, ensure_ascii=False, indent=2)


def abc_raw(abc):
    return abc.raw


_ABC_init = ABC.__init__


def _abc_init(self, data):
    self.raw = bytes(data)
    _ABC_init(self, data)


ABC.__init__ = _abc_init
from swf_decomp import E
from swf_extract_v2 import read_records


def extract(src, outroot, only, raw=False, frames=False, max_frames=0, list_only=False, name=None, depth=0,
            decompile=True):
    swf = load_swf(src)
    stem = name or os.path.splitext(os.path.basename(src))[0]
    ex = Extractor3(swf, raw, decompile)
    ex.max_frames = max_frames
    ex.feed()
    if list_only:
        r = swf["rect"]
        print("%s: SWF v%d (%s), %gx%g px, %.1f fps, %d frames" % (
            stem, swf["version"], swf["sig"], (r[1] - r[0]) / 20.0, (r[3] - r[2]) / 20.0, swf["fps"], swf["nframes"]))
        for k, v in sorted(ex.hist.items(), key=lambda x: -x[1]):
            print("   %-28s %d" % (k, v))
        return
    outdir = os.path.join(outroot, stem)
    manifest = ex.save(outdir, only, frames, max_frames)
    counts = {}
    for m in manifest:
        counts[m["kind"]] = counts.get(m["kind"], 0) + 1
    print("%s (SWF v%d) -> %s: %s" % (stem, swf["version"], outdir, counts or "nothing found"))
    if depth < 3 and "binary" in only:
        for m in manifest:
            if m["kind"] == "binary" and m["file"].endswith(".swf"):
                try:
                    extract(os.path.join(outdir, m["file"]), outdir, only, raw, frames, max_frames, False,
                            "nested_" + os.path.splitext(os.path.basename(m["file"]))[0], depth + 1, decompile)
                except Exception as e:
                    warn("nested swf: %s" % e)


def main():
    ap = argparse.ArgumentParser(description="Extract assets from SWF files (v%s)" % __version__)
    ap.add_argument("inputs", nargs="+", help="SWF files, glob patterns or folders")
    ap.add_argument("-o", "--out", default="swf_out")
    ap.add_argument("--only", help="comma-separated categories: " + ",".join(CATEGORIES3))
    ap.add_argument("--skip", help="categories to skip")
    ap.add_argument("--frames", action="store_true", help="export every sprite frame as a separate static SVG")
    ap.add_argument("--max-frames", type=int, default=0, help="max frames per animation (0 = unlimited)")
    ap.add_argument("--raw", action="store_true", help="additionally dump raw tags")
    ap.add_argument("--no-decompile", action="store_true", help="do not decompile ActionScript")
    ap.add_argument("--list", action="store_true", help="only show the file contents summary")
    a = ap.parse_args()
    only = set(a.only.split(",")) if a.only else set(CATEGORIES3)
    if a.skip:
        only -= set(a.skip.split(","))
    files = collect(a.inputs)
    if not files:
        print("no files found", file=sys.stderr)
        return 1
    for p in files:
        try:
            extract(p, a.out, only, a.raw, a.frames, a.max_frames, a.list, decompile=not a.no_decompile)
        except Exception as e:
            print("%s: error - %s" % (p, e), file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
