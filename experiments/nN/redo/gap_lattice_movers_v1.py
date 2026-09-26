"""Owner: base the lattice on the smallest gap.  Step t = tau + k/g: readings that are multiples of g stay exactly put
(the static part), the others move by frac(x/g) per step (the movers).  One mover is the proved off-lattice rule; m
movers need a common clear step (the mover ladder, MANUSCRIPT_v21 s6.11).  Measured on generic reduced sets (every six
coprime) and the four residual sets the exact rule left: the number of movers m at g = g_1 (the smallest reading, the
nearest runner's gap) and the least m over every lattice g in [2, max S].  Exact (integer arithmetic)."""
import random
from math import gcd
from functools import reduce
from collections import Counter
def movers(S, g): return sum(1 for d in S if d % g != 0)
rnd = random.Random(7); at_g1 = Counter(); best = Counter(); n = 0
while n < 2000:
    S = sorted(rnd.sample(range(1, 400), 7)); h = reduce(gcd, S); S = [s // h for s in S]
    if not all(reduce(gcd, [d for d in S if d != x]) == 1 for x in S): continue
    n += 1
    at_g1[movers(S, S[0])] += 1
    best[min(movers(S, g) for g in range(2, max(S) + 1))] += 1
print(f"generic reduced sets (every six coprime), random in [1,400]: {n}")
print(f"  movers at g = g_1 (the nearest runner's gap):     {dict(sorted(at_g1.items()))}")
print(f"  least movers over every lattice g in [2, max]:    {dict(sorted(best.items()))}")
for S in [(2,12,15,21,32,34,38), (4,5,6,8,14,32,37), (4,5,6,14,17,32,38), (4,7,8,15,29,36,37)]:
    bg = min(range(2, max(S) + 1), key=lambda g: movers(S, g))
    print(f"  residual {S}: movers at g_1 = {movers(S, S[0])}; least {movers(S, bg)} at g = {bg} (movers {[d for d in S if d % bg]})")
