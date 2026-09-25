"""The block rule as a CONSTRUCTION (derived from the synchronised-block lemma), level by level.

Runner's readings: core C below the largest ratio gap (>= 9); block above, split into synchronised
clusters (relative spread <= 1/9), sorted by base N_1 < N_2 < ...
Construction: scan t0 from tau_C (the core's own event) up to 2 tau_C on the exact grid
tau_C + j/(64 max(core, offsets)):
  level 0: every core reading clear at t0 with room for the next turn: ||c t0|| >= 1/8 + c/N_1;
  level j: cluster j's offsets leave a gap > 1/4 + 2E_j/N_j at the current instant; its phase is then
           set by the sync_block instant t <- t + fract(-y_j - N_j t)/N_j (y_j = middle of the gap),
           which moves t by < 1/N_j, and the slower levels must stay clear over that move.
The final instant is checked for loneliness EXACTLY (every reading, closed at 1/8).  Success = a named
instant produced by the construction.  Arrangements and every runner as before."""
import random
from fractions import Fraction as F
from math import floor
from collections import Counter
from arrangement_lib import readings, nd
from isolated_persistence_v1 import cascade_cap
from block_rule_derived_v1 import clusters, max_gap
import separation_arrangements_v1 as SA
def gap_mid(pts):
    p = sorted(set(x % 1 for x in pts)); g = [(p[i + 1] - p[i], p[i]) for i in range(len(p) - 1)] + [(1 - p[-1] + p[0], p[-1])]
    L, a = max(g); return L, (a + L / 2) % 1
def construct(core, block, tC):
    cl = clusters(block)
    scale = max([max(core)] + [c[-1] - c[0] for c in cl] + [1])
    step = F(1, 64 * scale); t0 = tC
    while t0 < 2 * tC:
        if all(nd(c * t0) >= F(1, 8) + F(c, cl[0][0]) for c in core):
            t = t0; ok = True; slower = list(core)
            for j, c in enumerate(cl):
                N = c[0]; E = c[-1] - c[0]
                L, y = gap_mid([(x - N) * t for x in c]) if len(c) > 1 else (F(1), F(1, 2))
                if L <= F(1, 4) + F(2 * E, N): ok = False; break
                t_new = t + ((-y - N * t) % 1) / N
                if not all(nd(s * u) >= F(1, 8) for s in slower for u in (t, t_new)): ok = False; break
                slower += c; t = t_new
            if ok and all(nd(d * t) >= F(1, 8) for d in core + block): return t
        t0 += step
    return None
if __name__ == "__main__":
    rnd = random.Random(55); SA.rnd = rnd
    n = ok = 0; fails = []; lvl = Counter()
    for name in ("uniform", "clustered", "slow-plus-fast"):
        for _ in range(300):
            V = sorted(set(SA.family(name)))
            if len(V) < 8: continue
            for k in range(8):
                ds = readings(V, k)
                rs = [(F(ds[i + 1], ds[i]), i) for i in range(len(ds) - 1)]
                r, i = max(rs)
                if r < 9: continue
                core, block = ds[:i + 1], ds[i + 1:]
                if len(block) < 3: continue
                n += 1; lvl[len(clusters(block))] += 1
                tC, _ = cascade_cap(core)
                t = construct(core, block, tC)
                if t is not None: ok += 1
                elif len(fails) < 8: fails.append((V[k], core, clusters(block), float(tC), float(cascade_cap(ds)[0])))
    print(f"{n} separated runners (block 3-6): the level-by-level construction produces an exactly lonely instant before 2 tau_C for {ok}/{n}")
    print(f"   number of fast clusters per runner: {dict(sorted(lvl.items()))}")
    for s, core, cl, tC, t in fails:
        print(f"   construction fails: runner {s}, core {core}, clusters {cl}; tau_C = {tC:.7f}, cascade event {t:.7f}")
