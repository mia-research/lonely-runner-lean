"""At each cascade isolation (whole-number arrangements, every runner), the flank is the reading e of the runner pinning
the event (the last setter; the nearest runner when the event is the bound).  Movers: readings whose ratio to e is not a
whole number, ratio a/c in lowest terms.  Does the flank sum criterion (FlankSumN.flank_sum) hold there:
sum over movers (1/4 + 1/c) < 1, and no whole ratio divisible by 8?  And if not, does SOME reading of the runner give a
flank where it holds?  Exact."""
import random
from fractions import Fraction as F
from math import floor
from collections import Counter
from arrangement_lib import readings, nd

def event_flank(ds):
    t = F(1, 8 * min(ds)); e = min(ds)
    while True:
        way = [d for d in ds if nd(d * t) < F(1, 8)]
        if not way: return t, e
        cand = {d: (F(floor(d * t - F(1, 8)) + 1) + F(1, 8)) / d for d in way}
        e = max(cand, key=lambda x: cand[x]); t = cand[e]

def criterion(ds, e):
    movers = []; dead = False
    for d in ds:
        r = F(d, e)
        if r.denominator == 1:
            if r.numerator % 8 == 0: dead = True
        else: movers.append(r.denominator)
    return (not dead) and sum(F(1, 4) + F(1, c) for c in movers) < 1, len(movers)

rnd = random.Random(52); tot = at_event = some = 0; nm = Counter(); nm_fail = Counter()
for _ in range(1500):
    V = sorted(rnd.sample(range(1, 250), 8))
    for k in range(8):
        ds = readings(V, k); tot += 1
        t, e = event_flank(ds)
        ok, m = criterion(ds, e); at_event += ok; nm[m] += 1
        if not ok: nm_fail[m] += 1
        some += any(criterion(ds, x)[0] for x in ds)
print(f"subjects {tot}")
print(f"  flank sum criterion holds at the event's own flank: {at_event}")
print(f"  holds at SOME reading's flank: {some}")
print(f"  movers at the event's flank: {sorted(nm.items())}; failing the criterion, by movers: {sorted(nm_fail.items())}")
