"""The induction on the scale tree (E30), tested at EVERY level of every runner.

Scale tree of a runner's readings R: sort, cut where consecutive readings jump by ratio >= 9 -> levels
L_0 < L_1 < ... < L_m.  U_j = L_0 u ... u L_j; tau_j = U_j's first isolation (exact cascade).
Base: U_j for j < m has <= 6 readings (lonely at 1/(|U_j|+1) > 1/8 by lower orders: positive cells).
STEP(j), j >= 1: tau_j = tau_{j-1} (level j clear there) or tau_j lies in the first lonely cell of
positive length of U_{j-1} at or after tau_{j-1} (U_{j-1}'s cascade continued past point-cells).
Recorded per step: pass/fail; turns (of level j's slowest reading) available in that cell and needed
from its start to level j's first clear instant; whether level j contains a synchronised pair
(consecutive readings within relative 1/9).  Arrangements (four families), every runner; exact."""
import random
from collections import Counter
from fractions import Fraction as F
from math import floor, ceil
from arrangement_lib import readings, nd
from isolated_persistence_v1 import cascade_cap
from nested_cascade_v1 import cascade_from
import separation_arrangements_v1 as SA
def levels(ds):
    out = [[ds[0]]]
    for a, b in zip(ds, ds[1:]):
        if b >= 9 * a: out.append([b])
        else: out[-1].append(b)
    return out
def cell_end(U, t): return min((ceil(c * t + F(1, 8)) - F(1, 8)) / c for c in U)
def first_positive_cell(U, t0):
    s = t0
    while True:
        e = cell_end(U, s)
        if e > s: return s, e
        s = cascade_from(U, s + F(1, 10**15))
def has_sync(L): return any(9 * (L[i + 1] - L[i]) <= L[i] for i in range(len(L) - 1))
if __name__ == "__main__":
    rnd = random.Random(57); SA.rnd = rnd
    def multilevel():
        # 3-4 levels at well separated scales, sizes summing to 8, sometimes with synchronised runs
        c = rnd.choice((3, 4)); sizes = [1] * c
        for _ in range(8 - c): sizes[rnd.randrange(c)] += 1
        V = set(); base = 1
        for s in sizes:
            base *= rnd.choice((12, 20, 50, 200))
            lo = base; sync = rnd.random() < 0.5
            pool = range(lo, lo + (max(3 * s, lo // 40) if sync else 8 * lo))
            V |= set(rnd.sample(pool, s))
        return sorted(V)
    fams = {n: (lambda n=n: SA.family(n)) for n in ("uniform", "clustered", "slow-plus-fast")}
    fams["multi-level"] = multilevel
    res = Counter(); steps_by_depth = Counter(); rows = {True: [], False: []}; fails = []
    for name, gen in fams.items():
        for _ in range(300):
            V = sorted(set(gen()))
            if len(V) < 8: continue
            for k in range(8):
                ds = readings(V, k); Ls = levels(ds)
                if len(Ls) < 2: continue
                U = []
                for j, L in enumerate(Ls):
                    prev = list(U); U = U + L
                    if j == 0: continue
                    tprev, _ = cascade_cap(prev); tj, _ = cascade_cap(U)
                    s, e = first_positive_cell(prev, tprev)
                    ok = (tj == tprev) or (s <= tj <= e)
                    res['pass' if ok else 'FAIL'] += 1; steps_by_depth[(len(Ls) - 1, j)] += 1
                    if not ok and len(fails) < 5: fails.append((name, V[k], Ls, j, float(tprev), float(s), float(e), float(tj)))
                    if tj != tprev:
                        mL = min(L); tn = cascade_from(L, s)
                        rows[has_sync(L)].append((float((e - s) * mL), float((tn - s) * mL)))
    print(f"steps tested: {sum(res.values())};  {dict(res)};  steps by (levels - 1, j): {dict(sorted(steps_by_depth.items()))}")
    for sync, rr in rows.items():
        if not rr: continue
        av = sorted(a for a, n in rr); ne = sorted(n for a, n in rr); mg = min(a - n for a, n in rr)
        print(f"   level {'WITH' if sync else 'without'} a synchronised pair ({len(rr)} steps not settled at tau_(j-1)): turns available min {av[0]:.2f}; needed max {ne[-1]:.3f}, 99% {ne[int(.99*(len(ne)-1))]:.3f}; least margin {mg:.3f}")
    for f in fails: print(f"   FAIL: {f[0]} runner {f[1]}, levels {f[2]}, step j={f[3]}: tau_prev {f[4]:.7f}, cell [{f[5]:.7f}, {f[6]:.7f}], tau_j {f[7]:.7f}")
