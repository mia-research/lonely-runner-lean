"""Step 2: general grids with ONE doubled slot.  Reduced speeds u = residue + 8*laps, residues = all of 0..7 except the
empty slot r, plus a second runner in slot s; every runner's laps random in [0, Q]; all speeds +100.  Every runner,
exact cascade.  Measured:
  (a) runners outside the doubled slot delayed past the grid instant 1/8 (grid argument says: never);
  (b) for each pair member (partner 8m away): does the minimal relocation t = 1/8 + 1/(64m) work?  If not, the runners
      blocking it: their difference D, residue offset D mod 8, and the stretch D/(8m) (eighths added by the stretch);
  (c) the pair member's cascade event R = 8t*."""
import random, sys
from fractions import Fraction as F
from math import floor
from collections import Counter
def nd(x): x = x % 1; return min(x, 1 - x)
def event(v, k):
    ds = [abs(v[i] - v[k]) for i in range(8) if i != k]; t = F(1, 8 * min(ds))
    while True:
        way = [d for d in ds if nd(d * t) < F(1, 8)]
        if not way: return t
        t = max((F(floor(d * t - F(1, 8)) + 1) + F(1, 8)) / d for d in way)
if __name__ == '__main__':
    rnd = random.Random(40)
    for Q in (1, 3, 10, 50):
        delayed_other = 0; minimal_ok = 0; pair_n = 0; block = Counter(); ex = []
        for trial in range(1500):
            s, r = rnd.sample(range(8), 2)
            res = [x for x in range(8) if x != r] + [s]
            while True:
                laps = [rnd.randint(0, Q) for _ in range(8)]
                u = [res[i] + 8 * laps[i] for i in range(8)]
                if len(set(u)) == 8: break
            v = [100 + x for x in u]
            pair = [i for i in range(8) if res[i] == s]
            for k in range(8):
                t = event(v, k)
                if k not in pair:
                    delayed_other += t > F(1, 8); continue
                pair_n += 1
                p = [i for i in pair if i != k][0]; m = abs(v[p] - v[k]) // 8
                tm = F(1, 8) + F(1, 64 * m)
                blockers = [i for i in range(8) if i != k and nd((v[i] - v[k]) * tm) < F(1, 8)]
                if not blockers: minimal_ok += 1; continue
                for i in blockers:
                    D = v[i] - v[k]
                    block[(D % 8, 'ahead' if D > 0 else 'behind', 'stretch<1' if abs(F(D, 8 * m)) < 1 else 'stretch>=1')] += 1
                if len(ex) < 4: ex.append((v, k, m, [(v[i] - v[k]) for i in blockers], 8 * t))
        print(f"\n== laps up to Q = {Q}: 1500 arrangements")
        print(f"   (a) runners outside the doubled slot delayed past 1/8: {delayed_other}")
        print(f"   (b) pair members: {pair_n}; minimal relocation 1/8 + 1/(64m) works for {minimal_ok}")
        print(f"       blockers of the minimal relocation by (residue offset, side, stretch size):")
        for key, n in block.most_common(12): print(f"         {key}: {n}")
        for v, k, m, bl, R in ex: print(f"       e.g. speeds {v}, runner {v[k]}, m={m}: blocked by differences {bl}; event R = {R}")
