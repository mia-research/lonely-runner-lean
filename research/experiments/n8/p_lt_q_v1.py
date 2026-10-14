"""H restated in our own machinery: at the largest flank each mover is rho = p/q with p < q,
and bad iff blocks(p, 8k+1, q).  So H is the candidate problem with EVERY NUMERATOR BELOW ITS
MODULUS.  Is p < q what does the work?  Compare against numerators drawn freely."""
from fractions import Fraction as F
import random

def blocks(p, A, q):
    M = 8*q; r = (p*A) % M
    return min(r, M-r) < q

def shadowed(pairs, kmax=60000):
    for k in range(kmax):
        if not any(blocks(p, 8*k+1, q) for p, q in pairs): return False
    return True

rng = random.Random(20260919)
print(f"{'arm':<42} {'sets':>8} {'shadowed':>10}")
for label, gen in (
  ("6 movers, p < q  (the largest flank)",
   lambda: [(lambda q: (rng.randrange(1, q), q))(rng.randrange(2, 60)) for _ in range(6)]),
  ("6 movers, p unrestricted",
   lambda: [(rng.randrange(1, 400), rng.randrange(2, 60)) for _ in range(6)]),
  ("6 movers, p > q",
   lambda: [(lambda q: (rng.randrange(q+1, q+400), q))(rng.randrange(2, 60)) for _ in range(6)]),
  ("3 movers, p < q",
   lambda: [(lambda q: (rng.randrange(1, q), q))(rng.randrange(2, 60)) for _ in range(3)]),
):
    tot = sh = 0; ex = None
    for _ in range(3000):
        pr = gen()
        pr = [(p, q) for p, q in pr if p % q != 0]
        if len(pr) < 2: continue
        tot += 1
        if shadowed(pr, 3000):
            if shadowed(pr, 60000):
                sh += 1
                if ex is None: ex = pr
    print(f"  {label:<40} {tot:>8,} {sh:>10,}" + (f"   e.g. {ex}" if ex else ""))
