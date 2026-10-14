"""E406 (2026-10-06), divided_flank_v1: the openings of one flank e, taken along an arithmetic progression of lap
indices j = j0 + P*s, applied to the divisible members stored in divisible_members_v2.json (fixed draws, reproducible).
Exact integer arithmetic (Theorem 10's certificate: opening j of flank e is lonely iff for every d,
d*(8j+1) mod 8e lies in [e, 7e]).
Along the progression, d*(8j+1) mod 8e moves by 8*d*P mod 8e per step, so d is FIXED when e | d*P and otherwise
ROTATES through a coset of (1/D_d)Z, D_d = e / gcd(e, d*P).  A rotating d blocks at most ceil(D_d/4) of every D_d
consecutive steps; so if every fixed reading is clear at j0 and the rotating readings' fractions
ceil(D/4)/D sum below 1, some step is a lonely opening [PROVISIONAL: counting tool; supports: the free step].
Flank chosen: the multiple of 8 whose cofactor every odd reading divides; P = 8 * lcm over the odd readings w of
(c / w).  Recorded per member: whether some j0 in [0, P) has every fixed reading clear (mask non-empty), the
number of rotating readings, whether the counting condition holds, and an exact check of the opening the
argument names (the least step s, searched up to CAP = 10^5 steps, with every reading clear).
"""
import sys, math, collections, random, time
from math import gcd, lcm
from fractions import Fraction as F
sys.path.insert(0, '.')
from divisible_members_v1 import build_A, build_B, full_residual

CAP = 10**5
def clear_at_opening(d, e, j):
    r = d * (8 * j + 1) % (8 * e); return e <= r <= 7 * e
def analyse(S):
    M = [d for d in S if d % 8 == 0]; W = [d for d in S if d % 8]
    divided = [m for m in M if all((m // 8) % w == 0 for w in W)]
    if not divided: return ('no single divided flank',)
    e = divided[0]; c = e // 8
    P = 8 * lcm(*[c // w for w in W])
    others = [d for d in S if d != e]
    fixed = [d for d in others if (d * P) % e == 0]; rot = [d for d in others if (d * P) % e]
    Ds = [e // gcd(e, d * P) for d in rot]
    frac = sum(F(-(-D // 4), D) for D in Ds)
    mask = [j0 for j0 in range(P) if all(clear_at_opening(d, e, j0) for d in fixed)]
    if not mask: return ('mask empty', len(rot), tuple(sorted(Ds)))
    if frac >= 1: return ('counting fails', len(rot), tuple(sorted(Ds)))
    j0 = mask[0]; N = 8 * e // (8 * P) if (8 * e) % (8 * P) == 0 else None
    period = lcm(*Ds) if Ds else 1
    for s in range(min(period, CAP)):
        j = j0 + P * s
        if all(clear_at_opening(d, e, j) for d in S): return ('settled', len(rot), tuple(sorted(Ds, key=lambda D: min(D, 10**6))[:0]), j)
    return ('no opening found within the first %d steps (period %s)' % (min(period, CAP), 'large' if period > CAP else period), len(rot))

if __name__ == '__main__':
    import json
    out = open('divided_flank_v1.out', 'w'); out.write(__doc__ + "\n")
    store = json.load(open('divisible_members_v2.json'))
    for name in ('A', 'B'):
        mem = [tuple(S) for S in store[name]]
        st = collections.Counter(); ex = collections.defaultdict(list)
        for S in mem:
            r = analyse(S); key = r[:2]
            st[key] += 1
            if len(ex[r[0]]) < 3: ex[r[0]].append((S, r))
        out.write("\nconstruction %s: members %d\n" % (name, len(mem)))
        for k, v in sorted(st.items(), key=str): out.write("  %s: %d\n" % (k, v))
        for k, v in ex.items():
            for e in v: out.write("  example [%s] %s\n" % (k, e))
    out.close(); print(open('divided_flank_v1.out').read()[len(__doc__):])
