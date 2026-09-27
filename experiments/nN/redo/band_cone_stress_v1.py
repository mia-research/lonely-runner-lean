"""E124: stress-test the 41 lap-assignment cones on shapes they were not chosen from: 100,000 random fine shapes and an
adversarial search for shapes outside every cone.  A shape is in cone k iff (8k_i+1) s_j <= (8k_j+7) s_i for all i,j
(s_0 = 1).  Exact."""
import random, re
from fractions import Fraction as F
CONES = []
for line in open('band_category_cover_v1.out'):
    m = re.search(r'laps (\S+|\([^)]*\))\s+newly', line)
    if m:
        t = m.group(1)
        CONES.append(tuple(int(x) for x in (t.strip('()').split(', ') if t.startswith('(') else t)))
print("cones:", len(CONES))
def inside(s, k):
    return all((8 * k[i] + 1) * s[j] <= (8 * k[j] + 7) * s[i] for i in range(7) for j in range(7))
def covered(s): return any(inside(s, k) for k in CONES)
rnd = random.Random(2024); miss = 0; ex = []
for trial in range(100000):
    d1 = rnd.randrange(50, 5000); top = rnd.randrange(7 * d1, 9 * d1 + 1)
    T = sorted([d1, top] + [rnd.randrange(d1, top + 1) for _ in range(5)])
    s = [F(d, d1) for d in T]
    if not covered(s): miss += 1; ex.append([round(float(x), 4) for x in s]) if len(ex) < 5 else None
print("random fine (ties allowed): outside every cone:", miss, ex)
# adversarial: maximise the least violation over cones (want > 0 = outside all)
def score(s):
    best = None
    for k in CONES:
        v = max((8 * k[i] + 1) * s[j] - (8 * k[j] + 7) * s[i] for i in range(7) for j in range(7))
        best = v if best is None or v < best else best
    return best    # <= 0 means inside some cone
worst = (F(-100), None)
for restart in range(40):
    s = [F(1)] + sorted(F(rnd.randrange(1000, 9000), 1000) for _ in range(5)) + [F(rnd.randrange(7000, 9001), 1000)]
    s = [s[0]] + sorted(s[1:6] + [s[6]])[:5] + [max(s[1:])] if False else [F(1)] + sorted(s[1:])
    if not (7 <= s[6] <= 9): continue
    sc = score(s)
    for step in range(3000):
        t = list(s); i = rnd.randrange(1, 7); t[i] += F(rnd.randrange(-200, 201), 10000)
        t = [F(1)] + sorted(t[1:])
        if not (t[1] >= 1 and 7 <= t[6] <= 9): continue
        sc2 = score(t)
        if sc2 >= sc: s, sc = t, sc2
    if sc > worst[0]: worst = (sc, s)
print("adversarial: best (least violation over cones) = %s  (> 0 would be outside every cone) at %s"
      % (float(worst[0]), [round(float(x), 4) for x in worst[1]]))
