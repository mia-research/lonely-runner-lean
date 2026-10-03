# tie_r7_search_v1.py -- landings at R*=7 (entry of reading 1's lap-1 zone): which opener (rank, lap) occur. Exact. Search description below.
# Search: reading a = (8j+1)/7 for j = 1..9 (so R=7 is the exit of its lap j); four other readings drawn uniformly from multiples of 1/100 in [1.01, 9.5]; reading 1 = 1.
# plus one reading drawn in (7,9) (so that R=1 is blocked and the cascade moves) in half the draws. 40,000 draws per j. Seeds fixed.
import random, time
from fractions import Fraction as F
from collections import Counter
exec(open('cascade_path_map_v1.py').read().split('\nif __name__ ==')[0])
rnd = random.Random(7007); out = Counter(); t0 = time.time(); ex = {}
for j in range(1, 10):
    a = F(8 * j + 1, 7)
    for _ in range(40000):
        others = [F(rnd.randint(101, 950), 100) for _ in range(4)]
        extra = [F(rnd.randint(701, 899), 100)] if rnd.random() < 0.5 else [F(rnd.randint(101, 950), 100)]
        rh = sorted(set([F(1), a] + others + extra))
        if len(rh) != 7 or rh[0] != 1: continue
        steps, R = path(rh)
        out[(j, 'draws')] += 1
        if R == 7:
            ia = rh.index(a) + 1
            op = (steps[-1]['setter'] + 1, steps[-1]['lap']) if steps else None
            out[(j, 'landing at 7')] += 1
            out[(j, 'opener', op)] += 1
            if (j, op) not in ex: ex[(j, op)] = rh
print('seconds', round(time.time() - t0))
for j in range(1, 10): print('j', j, 'rho_a =', F(8 * j + 1, 7), 'draws', out[(j, 'draws')], 'landing at R*=7:', out[(j, 'landing at 7')], 'openers:', {k[2]: v for k, v in out.items() if k[0] == j and k[1] == 'opener'})
for k, v in sorted(ex.items(), key=lambda kv: str(kv[0]))[:12]: print(k, [str(x) for x in v])
