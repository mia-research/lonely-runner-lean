"""Candidate: if the largest disparity e has no prime factor <= 7, its flank has a lonely opening
(Theorem 10 at e: some j < e with every d*(8j+1) mod 8e in [e, 7e]).  Random 7-sets {d_1..d_6, e},
d_i distinct in [1, e-1], no residual filter; e prime, e composite with no factor <= 7, and a
control with a factor <= 7.  Reports failures, with the first examples."""
import random, sys
from collections import Counter
random.seed(7)
def works(S, e):
    return any(all(e <= (d * (8 * j + 1)) % (8 * e) <= 7 * e for d in S if d != e) for j in range(e))
def rough(e): return all(e % p for p in (2, 3, 5, 7))
def isprime(n): return n > 1 and all(n % p for p in range(2, int(n ** .5) + 1))
groups = {
  'prime 41..199': [e for e in range(41, 200) if isprime(e)],
  'composite, no factor <= 7': [121, 143, 169, 187, 209, 221, 247, 253, 289, 299],
  'control: factor <= 7, 41..199': [e for e in range(41, 200) if not rough(e)],
}
TR = int(sys.argv[1]) if len(sys.argv) > 1 else 400
for name, es in groups.items():
    fail = []; n = 0
    for e in es:
        for _ in range(TR):
            S = tuple(sorted(random.sample(range(1, e), 6))) + (e,)
            n += 1
            if not works(S, e): fail.append(S)
    print(f"{name}: {len(fail)} failures of {n}", fail[:4])
