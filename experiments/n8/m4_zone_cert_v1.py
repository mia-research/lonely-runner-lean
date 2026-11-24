#!/usr/bin/env python3
"""m4_zone_cert_v1 -- certificate trees for Fresh/ZoneCover.lean, and an exact mirror of its
checker.  Trees come from m4_zone_cover_v2.cover (Fractions, full Floyd-Warshall closure); the
mirror recomputes them with the Lean arithmetic (natural pairs (p,q) = bound q*g_s <= p*g_r,
one-constraint update addC, gcd normalisation, leafOKz) and must return True on every tree it
emits.  w = largest gap index allowed for reading 0 (0: R in [1,7]; 1: also R in [9,15])."""
import sys, json
from math import gcd
from fractions import Fraction as F
sys.path.insert(0, '.')
import m4_zone_cover_v2 as Z

# ---- the Lean mirror -------------------------------------------------------------------
def faceOf(v): return (max(2 * v - 1, 2), 2 * v + 1)
def boxOfL0(l): return [(2, 2)] + [faceOf(v) for v in l[1:]]
def getU(U, r, s): return U[r][s] if r < len(U) and s < len(U[r]) else (0, 0)
def bnorm(a):
    d = gcd(a[0], a[1])
    return a if d == 0 else (a[0] // d, a[1] // d)
def bmul3(a, c, b): return bnorm((a[0] * c[0] * b[0], a[1] * c[1] * b[1]))
def bmin(a, b): return a if a[0] * b[1] <= b[0] * a[1] else b
def addC(U, r, s, p, q):
    return [[bmin(getU(U, x, y), bmul3(getU(U, x, r), (p, q), getU(U, s, y))) for y in range(7)] for x in range(7)]
def rootZ(box):
    return [[(1, 1) if r == s else (box[s][1], box[r][0]) for s in range(7)] for r in range(7)]
def leafOKz(w, m, U):
    md = lambda i: m[i] if i < len(m) else 0
    if not md(0) <= w: return False
    for r in range(7):
        for s in range(7):
            p, q = getU(U, r, s)
            if not (0 < q and p * (8 * md(r) + 1) <= (8 * md(s) + 7) * q): return False
    return True
def zc(w, t, U):
    if t[0] == "L": return leafOKz(w, t[1], U)
    _, r, s, p, q, a, b = t
    return r < 7 and s < 7 and zc(w, a, addC(U, r, s, p, q)) and zc(w, b, addC(U, s, r, q, p))

# ---- generation ------------------------------------------------------------------------
def convert(t):
    if t[0] == "L": return ("L", list(t[1]))
    if t[0] == "U": raise ValueError("uncovered")
    _, r, s, c, A, B = t
    c = F(c)
    return ("C", r, s, c.numerator, c.denominator, convert(A), convert(B))

def cert(l, w=0):
    Z.W0 = w
    stats = {"nodes": 0, "leaves": 0, "maxd": 0, "uncovered": []}
    t = Z.cover(Z.box_zone(l), 0, stats)
    if stats["uncovered"]: return None, stats
    t = convert(t)
    assert zc(w, t, rootZ(boxOfL0(l))), ("mirror rejects", l)
    return t, stats

def to_lean(t):
    if t[0] == "L": return "(.leaf [" + ",".join(map(str, t[1])) + "])"
    _, r, s, p, q, a, b = t
    return f"(.cut {r} {s} {p} {q} {to_lean(a)} {to_lean(b)})"

def size(t): return 1 if t[0] == "L" else 1 + size(t[5]) + size(t[6])

if __name__ == "__main__":
    l = json.loads(sys.argv[1]); w = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    t, st = cert(l, w)
    print(json.dumps({"l": l, "nodes": size(t), "mirror": True}), file=sys.stderr)
    print(to_lean(t))
