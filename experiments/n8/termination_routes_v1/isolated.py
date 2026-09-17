# "Move off the isolation time and it isn't isolated anymore."
# That premise says the lonely set has EMPTY INTERIOR -- isolated points.
# Is that true generally, or only for the tight configurations?
from fractions import Fraction as F
import random
n = 8
def circ(x):
    f = x - (x.numerator // x.denominator); return min(f, 1-f)
def lonely(ds, t): return all(circ(d*t) >= F(1,n) for d in ds)

def lonely_structure(ds, steps=20000):
    """Measure the lonely set over one period: is it points, or intervals?"""
    hits = []
    for j in range(steps):
        t = F(j, steps)
        if lonely(ds, t): hits.append(j)
    if not hits: return 0, 0
    # longest run of consecutive grid points = interval width in units of 1/steps
    best = run = 1
    for a, b in zip(hits, hits[1:]):
        run = run + 1 if b == a + 1 else 1
        best = max(best, run)
    return len(hits), best

print("ds                              lonely grid pts   longest run   reading")
tight = [(1,2,3,4,5,6,7), (1,3,4,5,6,7,9), (1,2,3,4,5,6,9)]
rng = random.Random(4)
rnd = [tuple(sorted(rng.sample(range(1,40),7))) for _ in range(6)]
for ds in tight + rnd:
    cnt, run = lonely_structure([F(x) for x in ds])
    kind = "EMPTY" if cnt==0 else ("isolated points" if run<=2 else f"intervals (~{run/20000:.5f} wide)")
    mark = "  <- AP / tight" if ds in tight else ""
    print(f"{str(ds):32s} {cnt:6d}        {run:6d}     {kind}{mark}")
