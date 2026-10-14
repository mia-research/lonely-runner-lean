"""modgap_strengthen_v1 (2026-10-06): the strengthened statement (6,1): for seven readings S there are a reading d and an instant t with the six others at distance >= 1/7 and d at distance >= 1/8.
Exact (Fractions).  Rule 7 exception authorised by the owner for this attempt; order 7 enters only as the framework's own Lean theorem (existenceAtN_seven), which gives the first component.
Method (all [P] by the cascade's own step at threshold h = 1/7): T = S minus d (six readings).  The lonely components of T at 1/7 are found in order: the first lonely instant by the cascade at
threshold 1/7 from 1/(7 d_min(T)); its component [l, r] ends at the least exit (a reading reaching 6/7); the next component starts at the cascade restarted from F = max over the closers of their next-lap edge
(8->7 version: (7(M+1)+1)/(7x)).  In a component [l, r], d has a clear point (distance >= 1/8) iff d is clear at l, or d's edge E = (8 round(d l) + 1)/(8 d) from inside its blocked window is <= r.
Recorded per set: for each d, k_d = the index (1-based) of the first component of T at 1/7 that contains a point clear for d at 1/8 (cap 40), and min over d.  Populations: the stored residual members
(C, BS, DA, DB, T1) and S1 = {1} + 6-subsets of [2, 24] (first 20,000 with full_residual not required, as controls).
[PROVISIONAL: counting tool; supports: the index counts]"""
import sys, json, itertools, math, collections
sys.path.insert(0, '.')
from fractions import Fraction as F
from members_reach_check_v1 import load, full_residual
H = F(1, 7); E8 = F(1, 8)
def cd(x):
    x = x - math.floor(x); return min(x, 1 - x)
def cascade_h(T, t0):
    t = t0
    while True:
        bl = [x for x in T if cd(x * t) < H]
        if not bl: return t
        t = max(F(7 * round(x * t) + 1, 7 * x) for x in bl)
def comp_right(T, l):
    best = None
    for x in T:
        v = x * l; N = math.ceil(v - F(6, 7)); e = (N + F(6, 7)) / x
        if best is None or e < best[0]: best = (e, [x])
        elif e == best[0]: best[1].append(x)
    return best
def components(T, kmax):
    t = cascade_h(T, F(1, 7 * min(T))); out = []
    for _ in range(kmax):
        r, cl = comp_right(T, t); out.append((t, r))
        Fs = [F(7 * (math.floor(x * r - F(6, 7)) + 1) + 1, 7 * x) for x in cl]
        t = cascade_h(T, max(Fs))
    return out
def d_clear_in(d, l, r):
    if cd(d * l) >= E8: return True
    E = F(8 * round(d * l) + 1, 8 * d)
    return E <= r
def kd(S, d, kmax=40):
    T = [x for x in S if x != d]
    for k, (l, r) in enumerate(components(T, kmax), 1):
        if d_clear_in(d, l, r): return k
    return None
out = open('modgap_strengthen_v1.out', 'w'); out.write(__doc__ + "\n")
C = [S for S in dict.fromkeys(load('../residual_members_C_list_v1.json')) if full_residual(S)]
BS = [S for S in dict.fromkeys(load('both_shadowed_members_v1.json')) if full_residual(S)]
st = json.load(open('divisible_members_v2.json'))
DA = list(dict.fromkeys(tuple(sorted(S)) for S in st['A'])); DB = list(dict.fromkeys(tuple(sorted(S)) for S in st['B']))
known = set(C) | set(BS) | set(DA) | set(DB)
T1 = [S for S in dict.fromkeys(tuple(sorted(x[2])) for x in json.load(open('members_5978_v1.json'))) if S not in known and full_residual(S)]
def s1():
    n = 0
    for r in itertools.combinations(range(2, 25), 6):
        yield (1,) + r; n += 1
        if n >= 20000: return
for name, sets in (('C', C), ('BS', BS), ('DA', DA), ('DB', DB), ('T1', T1[:1500]), ('S1 control', s1())):
    c = collections.Counter(); dmaxc = collections.Counter(); dminc = collections.Counter(); n = 0; none_ = []
    for S in sets:
        n += 1
        ks = {d: kd(S, d) for d in S}
        best = min([k for k in ks.values() if k is not None] or [None]) if any(k is not None for k in ks.values()) else None
        c[best if best is None or best <= 6 else '>6'] += 1
        dmaxc[ks[S[-1]] if ks[S[-1]] is None or ks[S[-1]] <= 6 else '>6'] += 1
        dminc[ks[S[0]] if ks[S[0]] is None or ks[S[0]] <= 6 else '>6'] += 1
        if best is None and len(none_) < 5: none_.append(S)
    out.write("\n==== %s: %d sets\n  min over d of k_d (first component of the six at 1/7 where d is clear at 1/8): %s\n  k for d = d_max: %s\n  k for d = d_min: %s\n  sets with no d found within 40 components: %d %s\n" %
              (name, n, dict(sorted(c.items(), key=str)), dict(sorted(dmaxc.items(), key=str)), dict(sorted(dminc.items(), key=str)), c[None], none_))
out.close(); print(open('modgap_strengthen_v1.out').read()[len(__doc__):])
