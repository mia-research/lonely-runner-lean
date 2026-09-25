"""Owner (2026-09-25): each runner is near its own vertex k/8 AT ITS OWN isolation event (not at others').
Frame (MANUSCRIPT_v21 s2.3): the AP anchored at the slowest and fastest speeds, gap D = W/7, A_k = v0 + k D with
v0 = v_min - D, so the AP's own runners sit at k/8 at t = 1/(8D).  Test, exact: at runner k's (speed rank k) own
cascade event t*_k, is circ((v_k - v0) t*_k - k/8) <= 1/8 ?  Also with vertices k a/8, a odd (any a, per runner).
Also reported: t*_k against the AP instant 1/(8D)."""
import re, ast, random
from fractions import Fraction as F
from math import floor
from arrangement_lib import readings, nd

def cascade(ds):
    t = F(1, 8 * min(ds))
    while True:
        way = [d for d in ds if nd(d * t) < F(1, 8)]
        if not way: return t
        t = max((F(floor(d * t - F(1, 8)) + 1) + F(1, 8)) / d for d in way)

def circ(x):
    x = x % 1; return min(x, 1 - x)

def per_runner(V):
    Vs = sorted(V); D = F(Vs[-1] - Vs[0], 7); v0 = Vs[0] - D; out = []
    for k in range(8):
        t = cascade(readings(Vs, k)); p = (Vs[k] - v0) * t
        d1 = circ(p - F(k + 1, 8)); da = min(circ(p - F((k + 1) * a, 8)) for a in (1, 3, 5, 7))
        out.append((d1, da, t * 8 * D))
    return out

rnd = random.Random(12)
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
print("runners within 1/8 of their own vertex at their own event (frame: AP anchored at slowest and fastest)")
print(f"{'family':26s} {'runners':>7s} {'k/8':>6s} {'k a/8, some odd a':>18s}   event / AP instant: median, max")
for name, arrs in fams.items():
    n = c1 = ca = 0; ratio = []
    for V in arrs:
        if len(set(V)) < 8: continue
        for d1, da, r in per_runner(V):
            n += 1; c1 += d1 <= F(1, 8); ca += da <= F(1, 8); ratio.append(r)
    ratio.sort()
    print(f"{name:26s} {n:7d} {c1:6d} {ca:18d}   {float(ratio[n//2]):.3f}, {float(ratio[-1]):.3f}")
n = c1 = ca = 0
for V, s in late:
    Vs = sorted(V); d1, da, r = per_runner(Vs)[Vs.index(s)]; n += 1; c1 += d1 <= F(1, 8); ca += da <= F(1, 8)
print(f"{'late events (the subject)':26s} {n:7d} {c1:6d} {ca:18d}")
