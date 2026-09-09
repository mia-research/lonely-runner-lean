r"""
tb_focus_v1 -- the highest-power arm of the (H3u) counterexample search.

By Theorem B (reports/n8_tail_bound.md Sec.6) a realisable saturated rank-2 lattice M'
whose height-<=3 part M_3 satisfies

        o_inf(M') - o_inf(M_3)  >  1/12

refutes (H3u).  The budget is SMALLEST -- so the search is most likely to succeed --
where o_inf(M_3) is smallest.  The rank-1 classes at height <= 3 realise 11 distinct
limits; the smallest is 1/24, and a plane through such a class needs only

        o_inf(M')  >  1/24 + 1/12  =  1/8  =  0.125

to refute.  Many rank-2 classes exceed 1/8, so this is where a violation would live.

This script fixes M_3 = <n0> for each rank-1 class of height <= 3 whose limit is at
most LIMCAP, sweeps the second generator v over all admissible vectors of height <=
HMAX, keeps the planes whose height-<=3 part is exactly <n0> (so M_3 does not grow),
decides realisability exactly (tb_hunt_v3.realisable), and reports the exact
Delta = o_inf(M') - o_inf(<n0>) against the 1/12 budget.

POPULATION LABEL: a PARAMETER box over generator height (||v||_inf <= HMAX), not a
speed box.  Realisability is exact, so no alpha box enters the decision.

usage: python3 tb_focus_v1.py [HMAX] [LIMCAP_NUM] [LIMCAP_DEN] [CELLCAP]
"""
import sys, itertools
from fractions import Fraction as F

import rt_limit_v2 as RL
import tb_limit_v1 as TB   # exact, DFS-clipped, validated against RL.rank2_limit
from tb_hunt_v3 import plucker, in_plane, realisable, cell_count

HMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 6
LIMCAP = F(int(sys.argv[2]) if len(sys.argv) > 2 else 1,
           int(sys.argv[3]) if len(sys.argv) > 3 else 12)
CELLCAP = int(sys.argv[4]) if len(sys.argv) > 4 else 60000
BUDGET = F(1, 12)

if __name__ == "__main__":
    ADM3 = [v for v in itertools.product(range(-3, 4), repeat=4) if RL.admissible(v)]
    ADMH = [v for v in itertools.product(range(-HMAX, HMAX + 1), repeat=4)
            if RL.admissible(v)]
    print(f"tb_focus_v1  HMAX = {HMAX}  LIMCAP = {LIMCAP}  CELLCAP = {CELLCAP}")
    print(f"admissible: ht<=3 {len(ADM3)}   ht<={HMAX} {len(ADMH)}")

    seen, base = set(), []
    for v in ADM3:
        k, _ = RL.lattice_key([list(v)])
        if k in seen:
            continue
        seen.add(k)
        n0 = tuple(k[0])
        lim = RL.rank1_limit(n0)
        if lim <= LIMCAP:
            base.append((n0, lim))
    base.sort(key=lambda t: t[1])
    print(f"rank-1 height-<=3 classes with limit <= {LIMCAP}: {len(base)}")
    for n0, lim in base[:6]:
        print(f"   n0 = {str(n0):>16}  o_inf = {lim}  needs o_inf(M') > "
              f"{lim + BUDGET} = {float(lim + BUDGET):.7f} to refute")

    best = []
    skipped = 0
    for n0, lim in base:
        seenp = set()
        for v in ADMH:
            p = plucker(n0, v)
            if p is None or p in seenp:
                continue
            seenp.add(p)
            k, rk = RL.lattice_key([list(n0), list(v)])
            if rk != 2:
                continue
            sh = [a for a in ADM3 if in_plane(p, a)]
            k3, rk3 = RL.lattice_key([list(a) for a in sh])
            if rk3 != 1:
                continue                      # M_3 grew to rank 2 -> Delta = 0
            rws = [list(r) for r in k]
            B, _ = RL.kernel_basis(rws)
            if not realisable(B):
                continue
            if cell_count(B) > CELLCAP:
                skipped += 1
                continue
            L = TB.rank2_limit(rws)
            best.append((L - lim, L, lim, n0, k))
        print(f"   ... n0 = {n0} done, running best "
              f"{float(max(b[0] for b in best)) if best else 0:.7f}", flush=True)
    best.sort(reverse=True)
    print(f"\nplanes evaluated: {len(best)}   skipped for cell count: {skipped}")
    if best:
        print(f"MAX Delta = {best[0][0]} = {float(best[0][0]):.7f}   "
              f"(budget 1/12 = {float(BUDGET):.7f})")
        print(f"count with Delta > 1/12: {sum(1 for b in best if b[0] > BUDGET)}")
        print(f"\n   {'Delta':>10} {'o_inf(M)':>10} {'o_inf(M3)':>9}  n0  ->  lattice")
        for d, L, lim, n0, k in best[:20]:
            flag = "   <== REFUTES (H3u)" if d > BUDGET else ""
            print(f"   {float(d):>10.7f} {str(L):>10} {str(lim):>9}  {n0}  {k}{flag}")
