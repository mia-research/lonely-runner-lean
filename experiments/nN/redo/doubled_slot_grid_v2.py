"""doubled_slot_grid_v1 reclassified.  Every pair member of a one-doubled-slot grid (laps up to Q) falls in:
  A  lonely at or before the grid instant (event R = 8t* <= 1): not delayed;
  B  delayed (R > 1) and the minimal relocation 1/8 + 1/(64m) is lonely;
  C  delayed and the minimal relocation is not lonely.
For C: the blockers of the minimal relocation (residue offset, side, stretch D/(8m) in eighths), and the event read as a
flank opening (8N+1)/(8d): the flank's difference d, its residue offset, its lap N."""
import random
from fractions import Fraction as F
from math import floor
from collections import Counter
from doubled_slot_grid_v1 import event, nd
rnd = random.Random(41)
for Q in (1, 3, 10, 50):
    cls = Counter(); cblock = Counter(); cflank = Counter(); ex = []
    for trial in range(2000):
        s, r = rnd.sample(range(8), 2)
        res = [x for x in range(8) if x != r] + [s]
        while True:
            laps = [rnd.randint(0, Q) for _ in range(8)]; u = [res[i] + 8 * laps[i] for i in range(8)]
            if len(set(u)) == 8: break
        v = [100 + x for x in u]; pair = [i for i in range(8) if res[i] == s]
        for k in pair:
            t = event(v, k); p = [i for i in pair if i != k][0]; m = abs(v[p] - v[k]) // 8
            if t <= F(1, 8): cls['A not delayed'] += 1; continue
            tm = F(1, 8) + F(1, 64 * m)
            bl = [i for i in range(8) if i != k and nd((v[i] - v[k]) * tm) < F(1, 8)]
            if not bl: cls['B minimal relocation'] += 1; continue
            cls['C other'] += 1
            for i in bl:
                D = v[i] - v[k]; cblock[(D % 8, 'ahead' if D > 0 else 'behind', 'stretch<1' if abs(F(D, 8 * m)) < 1 else '>=1')] += 1
            fl = [i for i in range(8) if i != k and (abs(v[i] - v[k]) * t) % 1 == F(1, 8)]
            d = min(abs(v[i] - v[k]) for i in fl); i0 = [i for i in fl if abs(v[i] - v[k]) == d][0]
            cflank[('partner' if i0 == p else f'offset {(v[i0] - v[k]) % 8}', floor(d * t))] += 1
            if len(ex) < 3: ex.append((v, v[k], m, [v[i] - v[k] for i in bl], 8 * t, v[i0] - v[k], floor(d * t)))
    tot = sum(cls.values())
    print(f"\n== laps up to Q = {Q}: {tot} pair members: " + ", ".join(f"{k} {n}" for k, n in sorted(cls.items())))
    print("   C, blockers of the minimal relocation:", dict(cblock.most_common(8)))
    print("   C, the event's flank (who, lap):", dict(cflank.most_common(10)))
    for e in ex: print(f"   e.g. speeds {e[0]}, runner {e[1]}, m={e[2]}: blockers {e[3]}; event R={e[4]} at flank {e[5]}, lap {e[6]}")
