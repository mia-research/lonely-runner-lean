"""WP2 (proof plan): map Case C by the cascade.  Exact; positive whole-number speeds; the subject is the SLOWEST runner
v_0 (EndRunnerN), with its own gap g_1 < W/22 (W the spread).  Readings d_1 = g_1 < d_2 < ... < d_7 = W.
Runner 2 (the nearest) is clear only on its bands; its first clear band is t in [1/(8 g_1), 7/(8 g_1)] -- a window of
ROOM = (3/4)(d_2/g_1) laps of d_2.  Per arrangement:
  u* = g_1 t* (the event in laps of the nearest runner), in the first band iff u* <= 7/8;
  WAIT = d_2 (t* - 1/(8 g_1)): how long, in laps of d_2, the other six take to clear together after the band opens;
  WAIT/ROOM, and the runner that pins the event.
Shapes of the rest (gaps g_2..g_7): even; clumped with outliers; even with a clump.  Then perturbation paths."""
import random
from fractions import Fraction as F
from math import floor
from collections import Counter
from arrangement_lib import nd
def cascade(ds):
    t = F(1, 8 * min(ds))
    while True:
        way = [d for d in ds if nd(d * t) < F(1, 8)]
        if not way: return t
        t = max((F(floor(d * t - F(1, 8)) + 1) + F(1, 8)) / d for d in way)
def arrangement(g):                       # speeds from gaps, slowest at 1000 (positive)
    V = [1000]
    for x in g: V.append(V[-1] + x)
    return V
def measure(V):
    ds = sorted(v - V[0] for v in V[1:]); g1 = ds[0]; d2 = ds[1]
    t = cascade(ds); u = g1 * t
    wait = d2 * (t - F(1, 8 * g1)); room = F(3, 4) * F(d2, g1)
    pins = [i for i, d in enumerate(ds) if nd(d * t) == F(1, 8)]
    return u, wait, room, pins
rnd = random.Random(26)
def rest(shape):
    base = rnd.randint(200, 2000)
    if shape == 'even':
        return [base + rnd.randint(-base // 10, base // 10) for _ in range(6)]
    if shape == 'clumped+outliers':
        g = [rnd.randint(1, base // 20) for _ in range(6)]
        for i in rnd.sample(range(6), rnd.randint(1, 2)): g[i] = base * rnd.randint(3, 20)
        return g
    if shape == 'even+clump':
        g = [base + rnd.randint(-base // 10, base // 10) for _ in range(6)]
        i = rnd.randrange(5); g[i] = rnd.randint(1, base // 30); g[i + 1] = rnd.randint(1, base // 30)
        return g
out = []
print("Case C (slowest runner, g_1 < W/22): event location and the six runners' wait, in laps of d_2")
for shape in ('even', 'clumped+outliers', 'even+clump'):
    for g1div in (30, 100, 1000):
        n = first = 0; worst = F(0); worstw = F(0); pinc = Counter(); ex = None
        while n < 150:
            g = rest(shape); W6 = sum(g)
            g1 = max(1, (W6) // (g1div - 1))
            if (g1 + W6) <= 22 * g1: continue
            V = arrangement([g1] + g)
            if len(set(V)) < 8: continue
            u, wait, room, pins = measure(V); n += 1
            first += u <= F(7, 8)
            if wait / room > worst: worst = wait / room; ex = (V, u, wait, room)
            worstw = max(worstw, wait)
            pinc[tuple(pins)] += 1
        print(f"  {shape:17s} g1 ~ W/{g1div:<5d}: {n} arrangements; event in the nearest runner's first band: {first}/{n}; "
              f"max WAIT {float(worstw):.3f} laps of d_2; max WAIT/ROOM {float(worst):.4f}")
        if ex and worst > F(1, 2): print(f"      worst: V={ex[0]} u*={float(ex[1]):.3f} wait={float(ex[2]):.3f} room={float(ex[3]):.3f}")
