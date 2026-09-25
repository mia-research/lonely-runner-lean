"""The vertex picture on the hard sets.  At an instant t each runner reads x_d = signed(d t) in
(-1/2, 1/2]; its nearest vertex is k_d = round(8 x_d) (mod 8) and its offset is x_d - k_d/8.
M1: at the midpoint of every lonely cell, the number of distinct nonzero vertices the seven
runners occupy (7 = spread like the regular 8-gon), collisions, mean |offset|; baseline at
uniform random instants.  M2: at every opening (j + 1/8)/d of the two largest runners, the number
of blockers, and each blocker's depth: shallow (1/16 < |x| < 1/8, nearer vertex +-1) or deep
(|x| < 1/16, nearer vertex 0).  M3: the share of the largest runner's openings that are lonely.
Sets: the 28 hard sets of [1,40] and 400 ordinary residual sets, chosen as in player_census_v1."""
import itertools, random, sys
from fractions import Fraction as Fr
from collections import Counter
_rs = __file__.replace('vertex_picture_v1.py', 'rung_selection_v1.py')
_s = open(_rs).read(); __file__ = _rs; exec(_s[:_s.index("for top in (30, 40):")])
_pc = open(_rs.replace('rung_selection_v1.py', 'player_census_v1.py')).read()
exec(_pc[_pc.index("def signed"):_pc.index("def census")])
R40 = [S for S in itertools.combinations(range(1, 41), 7) if eight_residual(S)]
f25 = [S for S in R40 if not any(rule(S, q, free_exact) for q in range(2, 6))]
hard = [S for S in f25 if not any(rule(S, q, free_exact) for q in (6, 7, 8))]
random.seed(14)
easy = random.sample([S for S in R40 if S not in set(f25)], 400)

def vertex_stats(S, t):
    xs = [signed(d * t) for d in S]
    ks = [round(8 * x) % 8 for x in xs]
    nz = [k for k in ks if k]
    return len(set(nz)), len(nz) - len(set(nz)), sum(abs(x - Fr(round(8 * x), 8)) for x in xs) / len(xs)

def opening_stats(S, d):
    rows = []
    for j in range(d):
        t = Fr(8 * j + 1, 8 * d)
        xs = {e: signed(e * t) for e in S if e != d}
        blk = {e: x for e, x in xs.items() if abs(x) < Fr(1, 8)}
        rows.append((len(blk), sum(1 for x in blk.values() if abs(x) > Fr(1, 16)), sum(1 for x in blk.values() if abs(x) < Fr(1, 16))))
    return rows

random.seed(5)
for label, sets in (("28 hard", hard), ("400 ordinary", easy)):
    distinct = Counter(); coll = Counter(); offs = []; rdistinct = Counter(); roffs = []
    nblk = {6: Counter(), 7: Counter()}; depth = {6: Counter(), 7: Counter()}; lonely_share = []
    for S in sets:
        s = sorted(S)
        for c in cells_full(S):
            dv, cl, mo = vertex_stats(S, (c['L'] + c['R']) / 2)
            distinct[dv] += 1; coll[cl] += 1; offs.append(float(mo))
        for _ in range(20):
            dv, cl, mo = vertex_stats(S, Fr(random.randrange(10**6), 10**6))
            rdistinct[dv] += 1; roffs.append(float(mo))
        for r, d in ((7, s[-1]), (6, s[-2])):
            rows = opening_stats(S, d)
            for nb, sh, dp in rows:
                nblk[r][nb] += 1; depth[r]['shallow'] += sh; depth[r]['deep'] += dp
            if r == 7: lonely_share.append(sum(1 for nb, _, _ in rows if nb == 0) / len(rows))
    n = sum(distinct.values()); rn = sum(rdistinct.values())
    print(f"--- {label}: {n} lonely cells")
    print("   M1 distinct nonzero vertices at cell midpoints:", {k: round(v / n, 3) for k, v in sorted(distinct.items())})
    print("      collisions:", {k: round(v / n, 3) for k, v in sorted(coll.items())}, " mean |offset| (eighths):", round(8 * sum(offs) / len(offs), 3))
    print("      baseline, uniform instants:", {k: round(v / rn, 3) for k, v in sorted(rdistinct.items())}, " mean |offset|:", round(8 * sum(roffs) / len(roffs), 3))
    for r in (7, 6):
        tb = sum(depth[r].values()); no = sum(nblk[r].values())
        print(f"   M2 openings of the rank-{r} runner: blockers per opening", {k: round(v / no, 3) for k, v in sorted(nblk[r].items())},
              f" blockers shallow {depth[r]['shallow'] / tb:.3f}, deep {depth[r]['deep'] / tb:.3f}")
    print(f"   M3 share of the largest runner's openings that are lonely: mean {sum(lonely_share) / len(lonely_share):.3f}, min {min(lonely_share):.3f}")
