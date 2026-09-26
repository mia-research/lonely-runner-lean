"""Parity lattice with two movers (owner: a quick digression).  S = seven positive whole-number readings with exactly two
odd readings x1, x2 (the movers at g = 2) and five even readings E (static: t -> t + 1/2 moves each even reading a whole
number of laps, each odd reading half a lap).  Candidate rule, exact:
  tau0 = the first lonely instant of E at threshold 1/6 (native order six), with room delta = (1/6 - 1/8)/max E on each
  side (1-Lipschitz); success if some tau in {tau0 + j*delta/4 : j = -4..4} has both odd readings clear at tau or both
  at tau + 1/2 (then the subject is lonely there: E is clear at 1/8 on the whole room, and unchanged by + 1/2).
Also the proved separation case (min odd > 3 max E).  Sets: generic reduced sets with exactly two odd readings (random),
and the three residual sets of v21 s17D with two odd readings."""
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
def rule(S):
    O = [d for d in S if d % 2]; E = [d for d in S if d % 2 == 0]
    assert len(O) == 2
    tau0 = cascade_q(E, 6); delta = (F(1, 6) - F(1, 8)) / max(E)
    for j in range(-4, 5):
        tau = tau0 + j * delta / 4
        if tau <= 0: continue
        for shift in (F(0), F(1, 2)):
            t = tau + shift
            if all(nd(d * t) >= F(1, 8) for d in S): return t, j, shift
    return None
rnd = random.Random(5); n = ok = sep = 0; fails = []
while n < 1000:
    S = sorted(rnd.sample(range(1, 400), 7)); g = reduce(gcd, S); S = [s // g for s in S]
    if sum(d % 2 for d in S) != 2 or len(set(S)) < 7: continue
    n += 1; r = rule(S); ok += bool(r)
    O = [d for d in S if d % 2]; E = [d for d in S if d % 2 == 0]
    sep += min(O) > 3 * max(E)
    if not r: fails.append(S)
print(f"generic reduced sets with exactly two odd readings: {n}; rule succeeds {ok}; separation case (min odd > 3 max even) {sep}")
print(f"  failures: {len(fails)}  e.g. {fails[:6]}")
for S in [(2,12,15,21,32,34,38), (4,5,6,8,14,32,37), (4,5,6,14,17,32,38)]:
    r = rule(list(S))
    print(f"  residual {S}: " + (f"lonely at t = {r[0]} (tau0 + {r[1]}/4 room, shift {r[2]})" if r else "rule does not succeed"))
