"""Owner: "cascade already gives you the scale, use it.  Informally: try and place most of the front half in AP and grid
can take care of the rest."  At every runner's cascade isolation (scale D* = 1/(8 t*), the candidate scale e/(8k+1) of
the last setter), read each reading d in scale units r = d/D* = 8 d t*:
  AP part  : r <= 7   (first lap; clear because r >= 1 at D* <= d_min)
  grid part: r > 7    (wrapped; clear because r mod 8 is in [1, 7])
Count, per event, how many of the subject's readings are in the AP part, and whether the front half (the smallest
ceil(n/2) readings) is entirely in it.  Exact.  Families: random arrangements (every runner as subject), the Case C
sample of E56, the adversarial Case C climbs (casec_R_climb_v1) and late events (R > 7)."""
import random, re, io, contextlib
from fractions import Fraction as F
from collections import Counter
from arrangement_lib import readings, cascade

def split(ds):
    t, mv = cascade(ds); r = [8 * d * t for d in ds]
    ap = sum(1 for x in r if x <= 7)
    front = all(x <= 7 for x in r[:(len(ds) + 1) // 2])
    return ap, front, 8 * ds[0] * t

def report(name, rows):
    n = len(rows)
    print(f"{name}: events {n}; readings in the AP part (r <= 7): {sorted(Counter(a for a, _, _ in rows).items())}; "
          f"front half entirely AP: {sum(f for _, f, _ in rows)} of {n}")

rnd = random.Random(12); rows = []
for _ in range(500):
    V = sorted(rnd.sample(range(1, 400), 8))
    for k in range(8): rows.append(split(readings(V, k)))
report("random arrangements, every runner", rows)
with contextlib.redirect_stdout(io.StringIO()):
    import case_c_map_v1 as cm
cm.rnd.seed(26); rows = []
for shape in ('even', 'clumped+outliers', 'even+clump'):
    for g1div in (30, 100, 1000):
        n = 0
        while n < 150:
            g = cm.rest(shape); W6 = sum(g); g1 = max(1, W6 // (g1div - 1))
            if g1 + W6 <= 22 * g1: continue
            V = cm.arrangement([g1] + g)
            if len(set(V)) < 8: continue
            n += 1; rows.append(split(sorted(v - V[0] for v in V[1:])))
report("Case C sample (slowest runner)", rows)
rows = []
for line in open('casec_R_climb_v1.out'):
    m = re.search(r'V (\[[^\]]*\])', line)
    if m:
        V = eval(m.group(1)); rows.append(split(sorted(v - V[0] for v in V[1:])))
report("Case C adversarial climbs", rows)
late = [r for r in (split(readings(sorted(rnd.sample(range(1, 400), 8)), 0)) for _ in range(20000)) if r[2] > 7]
report("late events among 20,000 random slowest runners", late)
