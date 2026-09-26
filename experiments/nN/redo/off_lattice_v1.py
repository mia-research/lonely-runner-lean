"""The off-lattice rule (owner: check seriously; it generalises).  S = seven positive whole-number readings.  If some
x in S has h = gcd(S \\ {x}) not dividing x, the subject is lonely: the other six are lonely at 1/7 at some tau (native
order seven), every t_k = tau + k/h keeps them exactly where they were, and x advances by frac(x/h) per step, so some k
puts x clear (exists_clear_step).  Checks, exact:
 (1) soundness: construct tau by the exact cascade at threshold 1/7 on the six, then the least k clearing x; verify
     the whole set is lonely at t_k (at 1/8);
 (2) the class it leaves: reduced sets in which every six of the seven are coprime;
 (3) which of the recorded residual sets it closes.
"""
import random
from fractions import Fraction as F
from math import gcd, floor
from functools import reduce
from arrangement_lib import nd
def cascade_q(ds, q):
    t = F(1, q * min(ds))
    while True:
        way = [d for d in ds if nd(d * t) < F(1, q)]
        if not way: return t
        t = max((F(floor(d * t - F(1, q)) + 1) + F(1, q)) / d for d in way)
def off_lattice_instant(S):
    for x in S:
        D = [d for d in S if d != x]; h = reduce(gcd, D)
        if x % h == 0: continue
        tau = cascade_q(D, 7)
        for k in range(0, 10 * h + 10):
            t = tau + F(k, h)
            if nd(x * t) >= F(1, 8): return x, h, t
    return None
rnd = random.Random(44); ok = bad = applies = n = 0
for _ in range(3000):
    S = sorted(rnd.sample(range(1, 400), 7)); g = reduce(gcd, S); S = [s // g for s in S]; n += 1
    r = off_lattice_instant(S)
    if r:
        applies += 1; x, h, t = r
        if all(nd(d * t) >= F(1, 8) for d in S): ok += 1
        else: bad += 1; print("FAIL", S, r)
print(f"(1) random reduced 7-sets in [1,400]: {n}; rule applies {applies}; instant verified lonely {ok}; failures {bad}")
def all_six_coprime(S):
    return all(reduce(gcd, [d for d in S if d != x]) == 1 for x in S)
print(f"(2) of these, every six coprime (the class the rule leaves): {sum(all_six_coprime(sorted(set(rnd.sample(range(1,400),7)))) for _ in range(3000))} of 3000 fresh samples")
res40 = [(2,12,15,21,32,34,38), (4,5,6,8,14,32,37), (4,5,6,14,16,34,38), (4,5,6,14,17,32,38),
         (4,5,6,14,32,34,38), (4,6,14,15,16,34,38), (4,7,8,15,29,36,37)]
print("(3) the seven [1,40] residual sets of v21 s17D:")
for S in res40:
    r = off_lattice_instant(list(S))
    print(f"    {S}: " + (f"closed -- x={r[0]}, h={r[1]}, lonely at t={r[2]}" if r else "not closed (every six coprime)"))
