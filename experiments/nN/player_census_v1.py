"""Every player in every lonely cell, for the hard sets and for ordinary sets.

Integer disparities, one period (0, 1).  A lonely cell [L, R] is opened by flank eL at its lap jL,
L = (jL + 1/8)/eL, and closed by flank eR at its lap kR, R = (kR - 1/8)/eR.  Rung of a boundary:
N = e/gcd(j, e), unit i = j/gcd(j, e) (the instant is i/N + 1/(8e) for an opening).  For every
runner: its signed reading (position on the circle, in (-1/2, 1/2]) at L, at the midpoint and at R,
and its slack there (|reading| - 1/8); the pressing runner is the non-boundary runner of least slack
at the midpoint.  Also the midpoint's nearest point i/q with q <= 8, and the nearest mirror meeting
k/(eL + eR) of the boundary pair.

Reports: two hard sets in full; then, for the 28 hard sets of [1,40] and 400 ordinary residual sets,
the distributions that could describe the hard sets' cells.
"""
import itertools, random, sys
from fractions import Fraction as Fr
from math import gcd
from collections import Counter
_rs = __file__.replace('player_census_v1.py', 'rung_selection_v1.py')
_s = open(_rs).read(); __file__ = _rs; exec(_s[:_s.index("for top in (30, 40):")])

def signed(x):
    x = x % 1
    return x if x <= Fr(1, 2) else x - 1

def cells_full(S):
    z = sorted((Fr(8 * k - 1, 8 * d), Fr(8 * k + 1, 8 * d), d, k) for d in S for k in range(0, d + 1))
    out = []; hi = None; cur = None
    for lo, h, d, k in z:
        if hi is not None and lo >= hi and hi < 1:
            out.append(dict(L=hi, eL=cur[0], jL=cur[1], R=lo, eR=d, kR=k))
        if hi is None or h > hi: hi, cur = h, (d, k)
    return out

def rung(e, j):
    g = gcd(j, e); return e // g, j // g

def census(S):
    s = sorted(S); rank = {d: s.index(d) + 1 for d in S}
    rows = []
    for c in cells_full(S):
        L, R = c['L'], c['R']; mid = (L + R) / 2
        eL, eR = c['eL'], c['eR']
        pos = {d: (signed(d * L), signed(d * mid), signed(d * R)) for d in S}
        slack = {d: abs(pos[d][1]) - Fr(1, 8) for d in S}
        others = [d for d in S if d not in (eL, eR)]
        press = min(others, key=lambda d: slack[d]) if others else None
        q, i, off = min(((q, i, abs(mid - Fr(i, q))) for q in range(1, 9) for i in range(q + 1)), key=lambda x: x[2])
        m = eL + eR; k = round(mid * m)
        rows.append(dict(S=S, L=L, R=R, width=R - L, eL=eL, rL=rank[eL], jL=c['jL'], NL=rung(eL, c['jL']),
                         eR=eR, rR=rank[eR], kR=c['kR'], NR=rung(eR, c['kR'] - 1) if c['kR'] > 0 else (eR, 0),
                         pos=pos, slack=slack, press=press, rP=rank[press] if press else None,
                         farey=(q, i, off), mirror=(k, m, abs(mid - Fr(k, m)))))
    return rows

R40 = [S for S in itertools.combinations(range(1, 41), 7) if eight_residual(S)]
f25 = [S for S in R40 if not any(rule(S, q, free_exact) for q in range(2, 6))]
hard = [S for S in f25 if not any(rule(S, q, free_exact) for q in (6, 7, 8))]

for S in hard[:2]:
    print(f"==== {S}")
    for r in census(S):
        print(f"  cell [{r['L']}, {r['R']}] width*max {float(r['width'] * max(S)):.3f}: opened by {r['eL']} (rank {r['rL']}, lap {r['jL']}, rung N={r['NL'][0]} i={r['NL'][1]}), "
              f"closed by {r['eR']} (rank {r['rR']}, lap {r['kR']}); pressing runner {r['press']} (slack {float(r['slack'][r['press']]):.3f}); "
              f"nearest i/q {r['farey'][1]}/{r['farey'][0]} off {float(r['farey'][2]):.3f}; mirror {r['mirror'][0]}/{r['mirror'][1]} off {float(r['mirror'][2]):.4f}")
        print("     readings at L | mid | R:", {d: tuple(round(float(x), 3) for x in r['pos'][d]) for d in S})

random.seed(14)
easy = random.sample([S for S in R40 if S not in set(f25)], 400)
for label, sets in (("28 hard", hard), ("400 ordinary", easy)):
    rows = [r for S in sets for r in census(S)]
    n = len(rows); per = n / len(sets)
    pair = Counter((r['rL'], r['rR']) for r in rows)
    press = Counter(r['rP'] for r in rows)
    NL = Counter(min(r['NL'][0], 13) for r in rows)
    fq = Counter(r['farey'][0] for r in rows)
    same_res = sum(1 for r in rows if (r['eL'] - r['eR']) % 8 == 0 or (r['eL'] + r['eR']) % 8 == 0)
    mir = sum(1 for r in rows if r['mirror'][2] <= r['width'] / 2)
    wid = sorted(float(r['width'] * max(r['S'])) for r in rows)
    print(f"--- {label}: {per:.1f} cells per set")
    print(f"   (opening rank, closing rank), top 8: {[(k, round(v / n, 3)) for k, v in pair.most_common(8)]}")
    print(f"   pressing runner rank: {sorted((k, round(v / n, 3)) for k, v in press.items())}")
    print(f"   opening rung N (13 = 13+): {sorted((k, round(v / n, 3)) for k, v in NL.items())}")
    print(f"   nearest small-q point, q: {sorted((k, round(v / n, 3)) for k, v in fq.items())}")
    print(f"   boundary pair with eL = +-eR mod 8: {same_res / n:.3f};  cell contains the boundary pair's mirror meeting: {mir / n:.3f}")
    print(f"   width x max(S): min {wid[0]:.3f} median {wid[len(wid)//2]:.3f}")
