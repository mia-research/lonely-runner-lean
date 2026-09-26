"""The grid nudge.  At t = 1/8 a whole-number reading d sits at (d mod 8)/8: clear unless 8 | d.  For a residual set
(every modulus 2..8 divides some reading) the only blocked readings at t = 1/8 are the multiples of 8.  Nudge to
t = (1/8)(1 + s/d0), s = +1 or -1, d0 the largest multiple of 8 in the set: d0 moves exactly to the slot edge; every
other d moves by s d/(8 d0).  Prediction: the forward nudge fails exactly when a reading is 7 mod 8 (pushed into the
slot) or another multiple of 8 is not pushed out; the backward nudge likewise with 1 mod 8.  Exact test on every
residual set with readings <= 32; tallied by (has a reading = 1 mod 8, has one = 7 mod 8, number of multiples of 8)."""
import itertools
from fractions import Fraction as F
from collections import Counter
from multiprocessing import Pool
from arrangement_lib import nd
from residual_cascade_v1 import residual

def lonely(T, t): return all(nd(d * t) >= F(1, 8) for d in T)

def chunk(first):
    c = Counter()
    for rest in itertools.combinations(range(first + 1, 33), 6):
        T = (first,) + rest
        if not residual(T): continue
        m8 = [d for d in T if d % 8 == 0]; d0 = max(m8)
        has1 = any(d % 8 == 1 for d in T); has7 = any(d % 8 == 7 for d in T)
        fwd = lonely(T, F(1, 8) * (1 + F(1, d0))); back = lonely(T, F(1, 8) * (1 - F(1, d0)))
        c[(has1, has7, len(m8), fwd, back)] += 1
    return c

if __name__ == '__main__':
    with Pool() as pool: parts = pool.map(chunk, range(1, 27))
    tot = Counter()
    for p in parts: tot.update(p)
    print(f"residual sets, readings <= 32: {sum(tot.values())}")
    print("  (has 1 mod 8, has 7 mod 8, multiples of 8, forward nudge lonely, backward nudge lonely): count")
    for k, v in sorted(tot.items()): print(f"  {k}: {v}")
    either = sum(v for k, v in tot.items() if k[3] or k[4])
    print(f"  one of the two nudges isolates: {either}")
