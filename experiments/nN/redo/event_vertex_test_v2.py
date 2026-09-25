"""Owner (2026-09-25): "Runner 1 isolation point is near 1/8, runner 2 is 2/8 etc etc runner 8 is 8/8" -- at the
AP's global instant runner k (speed rank k) sits at vertex k/8; at an arrangement's isolation event every runner
is within 1/8 of its own vertex.  Exact test at each subject's cascade event t*, positive speeds, all 8 runners
(the subject included), up to one common rotation c of the circle (a common shift of speeds or of the frame):
   exists c:  circ(v_k t* - k/8 - c) <= 1/8  for every rank k = 1..8          (class 1, literal)
and the same with vertex k a/8 for some odd a (the AP's other global instants 3/8, 5/8, 7/8).
Also the smallest band that works, delta = min over c (and a) of max_k circ(...), in slots (1 slot = 1/8)."""
import re, ast, random
from fractions import Fraction as F
from math import floor
from collections import Counter
from arrangement_lib import readings, nd

def cascade(ds):
    t = F(1, 8 * min(ds))
    while True:
        way = [d for d in ds if nd(d * t) < F(1, 8)]
        if not way: return t
        t = max((F(floor(d * t - F(1, 8)) + 1) + F(1, 8)) / d for d in way)

def circ(x):
    x = x % 1; return min(x, 1 - x)

def band(x):
    """min over c of max_k circ(x_k - c): candidates are circular midpoints of pairs of x (exact)."""
    xs = [a % 1 for a in x]; best = None
    cands = set(xs)
    for i in range(len(xs)):
        for j in range(len(xs)):
            m = (xs[i] + xs[j]) / 2; cands.add(m % 1); cands.add((m + F(1, 2)) % 1)
    for c in cands:
        v = max(circ(a - c) for a in xs)
        if best is None or v < best: best = v
    return best

def test(V):
    Vs = sorted(V); out = []
    for k in range(8):
        ds = readings(Vs, k); t = cascade(ds)
        pos = [v * t for v in Vs]                         # rank j+1 at index j
        d1 = band([pos[j] - F(j + 1, 8) for j in range(8)])
        da = min(band([pos[j] - F((j + 1) * a, 8) for j in range(8)]) for a in (1, 3, 5, 7))
        out.append((d1, da, 8 * min(ds) * t))
    return out

rnd = random.Random(11)
fams = {'AP gap 840 + dev 1/100': [[840 * (j + 1) + 2000 + rnd.randint(-8, 8) for j in range(8)] for _ in range(100)],
        'AP gap 840 + dev 1/8': [[840 * (j + 1) + 2000 + rnd.randint(-105, 105) for j in range(8)] for _ in range(100)],
        'AP gap 840 + dev 1/2': [[840 * (j + 1) + 2000 + rnd.randint(-420, 420) for j in range(8)] for _ in range(100)],
        'AP gap 840 + dev 2': [[840 * (j + 1) + 2000 + rnd.randint(-1680, 1680) for j in range(8)] for _ in range(100)],
        'uniform [1,60]': [rnd.sample(range(1, 61), 8) for _ in range(100)],
        'uniform [1,1000]': [rnd.sample(range(1, 1001), 8) for _ in range(100)]}
late = []
for line in open('late_event_S9_search_v1.out'):
    m = re.search(r'LATE seed \d+: .* V=(\[[^\]]*\]) subject (\d+)', line)
    if m: late.append((ast.literal_eval(m.group(1)), int(m.group(2))))
print("subjects whose event has every runner within 1/8 of its vertex (one common rotation):")
print(f"{'family':26s} {'subjects':>8s} {'class 1':>8s} {'some odd a':>10s}   band needed (slots): class 1 median/max; some a median/max")
for name, arrs in fams.items():
    n = c1 = ca = 0; b1 = []; ba = []
    for V in arrs:
        if len(set(V)) < 8: continue
        for d1, da, R in test(V):
            n += 1; c1 += d1 <= F(1, 8); ca += da <= F(1, 8); b1.append(8 * d1); ba.append(8 * da)
    b1.sort(); ba.sort()
    print(f"{name:26s} {n:8d} {c1:8d} {ca:10d}   {float(b1[n//2]):.2f}/{float(b1[-1]):.2f}; {float(ba[n//2]):.2f}/{float(ba[-1]):.2f}")
n = c1 = ca = 0; ba = []
for V, s in late:
    Vs = sorted(V); k = Vs.index(s); d1, da, R = test(Vs)[k]
    n += 1; c1 += d1 <= F(1, 8); ca += da <= F(1, 8); ba.append(8 * da)
ba.sort()
print(f"{'late events':26s} {n:8d} {c1:8d} {ca:10d}   some a median/max {float(ba[n//2]):.2f}/{float(ba[-1]):.2f}")
