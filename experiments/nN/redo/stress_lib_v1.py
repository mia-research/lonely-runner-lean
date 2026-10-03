# stress_lib_v1.py -- exact (gmpy2 mpq) fast cascade, outcome, class label, and exact checks of claims G, C, S.
# The official path()/outcome() (Fractions) are exec'd from the existing files and used to cross-check every reported item.
import os, sys, random, time
from fractions import Fraction as F
from math import floor
from gmpy2 import mpq, mpz
import gmpy2
os.chdir(os.path.dirname(os.path.abspath(__file__)))
exec(open('cascade_path_map_v1.py').read().split('\nif __name__ ==')[0])
exec(open('outcome_classes_v2.py').read().split('\nif __name__ ==')[0])
OFFICIAL_path, OFFICIAL_outcome = path, outcome
def Q(x): return mpq(x.numerator, x.denominator) if isinstance(x, F) else mpq(x)
def Fr(x): return F(int(x.numerator), int(x.denominator))
HALF = mpq(1, 2)
def fpath(rh):
    """rh: sorted list of mpq, rh[0]==1.  steps: (R, setter_index, lap, R2).  Same tie rule as path(): max of (exit, index, lap)."""
    R = mpq(1) / rh[0]; steps = []
    while True:
        best = None
        for i, r in enumerate(rh):
            x = R * r; j = int(gmpy2.floor(x / 8 + HALF))
            if abs(x - 8 * j) < 1:
                k = ((8 * j + 1) / r, i, j)
                if best is None or k > best: best = k
        if best is None: return steps, R
        steps.append((R, best[1], best[2], best[0])); R = best[0]
def is_strip(r):
    j = int(gmpy2.floor(r / 8 + HALF)); return j >= 1 and abs(r - 8 * j) < 1
def fout(rh):
    steps, R = fpath(rh); n = len(rh)
    best = None
    for y, r in enumerate(rh):
        j = max(1, int(gmpy2.ceil((R * r + 1) / 8)))
        e = (8 * j - 1) / r
        if best is None or e < best[0]: best = (e, y + 1, j)
    opener = (steps[-1][1] + 1, steps[-1][2]) if steps else None
    return dict(R=R, steps=steps, opener=opener, closer=(best[1], best[2]), width=best[0] - R, nm=len(steps))
def label(rh, o):
    nm = o['nm']; w0 = (o['width'] == 0)
    if nm == 0: return 'K0z' if w0 else 'K0'
    s, j = o['opener']; c = o['closer']; t = '2' if nm >= 2 else '1'
    if w0: return 'K' + t + 'z'
    if c[0] == s: return 'K' + t + ('s1' if j == 1 else 's2')
    if nm == 1: return 'K1' + ('a' if j == 1 else 'b')
    st = is_strip(rh[s - 1])
    return 'K2' + (('a' if j == 1 else 'b') if st else ('c' if j == 1 else 'd'))
KNOWN_NONEMPTY = {'K0','K0z','K1a','K1b','K1s1','K1s2','K1z','K2b','K2c','K2d','K2s2','K2z'}
def check(rh):
    """returns (class, landing, list of violation / anomaly strings).  rh sorted distinct mpq with rh[0]==1."""
    o = fout(rh); steps = o['steps']; R = o['R']; v = []
    cl = label(rh, o)
    if cl not in KNOWN_NONEMPTY: v.append('CLASS_NOT_LISTED_OR_EMPTY:' + cl)
    # (G)
    gate_set = any(s[1] == 0 and s[2] == 1 for s in steps)
    st9 = any(s[3] == 9 for s in steps)
    if not ((R > 7) == gate_set == st9): v.append('G_iff:R>7=%s gateSetter=%s state9=%s' % (R > 7, gate_set, st9))
    if 7 < R < 9: v.append('G_landing_in_(7,9)')
    # (C)
    vals = [(7 - ((R * r) % 8)) / r for r in rh]
    mn = min(vals)
    if vals[o['closer'][0] - 1] != mn: v.append('C_argmin')
    if steps and o['closer'][0] == o['opener'][0] and o['opener'][0] != len(rh): v.append('C_own_reading_not_fastest')
    # all argmin readings for ties
    if steps and sum(1 for x in vals if x == mn) > 1 and any(vals[i] == mn and i + 1 == o['opener'][0] and i != len(rh) - 1 for i in range(len(rh))):
        v.append('C_tie_with_opener_nonfastest')
    # (S)
    seen = set(); prefix_distinct = True
    for k, s in enumerate(steps):
        if s[1] in seen: prefix_distinct = False
        seen.add(s[1])
        if prefix_distinct and k <= 6:
            if not rh[6 - k] > 7 * mpq(7, 9) ** k: v.append('S_bound_k=%d' % k)
        Rk, y, j, R2 = s
        if R2 / Rk > mpq(8 * j + 1, 8 * j - 1): v.append('S_ratio_step%d' % k)
        if mpq(8 * j + 1, 8 * j - 1) > mpq(9, 7): v.append('S_ratio97_step%d' % k)
        if k > 0 and steps[k - 1][1] == y: v.append('S_consecutive_same_setter_step%d' % k)
    # structural anomalies
    if o['width'] < 0: v.append('NEG_WIDTH')
    if steps:
        s, j = o['opener']
        if o['nm'] == 1 and not (is_strip(rh[s - 1]) and j == int(gmpy2.floor(rh[s - 1] / 8 + HALF))): v.append('NM1_opener_not_own_strip_lap')
        if o['nm'] >= 2 and abs(rh[s - 1] * 1 - 8 * j) < 1 and False: pass
        if o['nm'] >= 2:
            # opener zone (s,j) contains R=1 ?
            if 8 * j - 1 < rh[s - 1] < 8 * j + 1: v.append('NM2_opener_zone_contains_1')
        if (8 * j + 1) / rh[s - 1] != R: v.append('LANDING_NOT_OPENER_EXIT')
    return cl, R, v, o
def verify_official(rh):
    """exact re-run with the official Fraction code; returns (R, outcome dict)"""
    rr = [Fr(x) for x in rh]; o = OFFICIAL_outcome(rr); return o
def norm(xs):
    xs = sorted(xs); m = xs[0]; return [x / m for x in xs]
