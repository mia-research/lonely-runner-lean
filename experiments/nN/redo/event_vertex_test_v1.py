"""Owner's statement (2026-09-25): at the isolation event every intervening runner is near its own isolation point
(its AP octagon point), at most 1/8 (one slot) away on either side.  Exact test, one reading of 'own point':
R* = 8 d_min t* (the event in the subject's AP coordinate); r = the odd integer nearest R* (the AP unit instant
r/8 of scale d_min); runner k's AP index a_k = the integer nearest its reading s_k = d_k/d_min; its own point is
a_k r mod 8 (in eighths); its position at the event is s_k R* mod 8.  dev_k = circular difference, in eighths.
Claim tested: |dev_k| <= 1 for every runner.  Also reported: |R* - r|."""
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

def circ8(x):
    x = x % 8; return min(x, 8 - x)

def test(V, k):
    ds = readings(V, k); dmin = min(ds); t = cascade(ds); R = 8 * dmin * t
    r = 2 * floor((R - 1) / 2 + F(1, 2)) + 1               # nearest odd integer
    devs = []
    for d in ds:
        s = F(d, dmin); a = floor(s + F(1, 2))
        devs.append(circ8(s * R - a * r))
    return R, r, max(devs)

rnd = random.Random(3); rows = []
fams = {'uniform [1,60]': [rnd.sample(range(1, 61), 8) for _ in range(150)],
        'AP gap 840 + dev 1/8': [[840 * (j + 1) + 2000 + rnd.randint(-105, 105) for j in range(8)] for _ in range(150)],
        'AP gap 840 + dev 2': [[840 * (j + 1) + 2000 + rnd.randint(-1680, 1680) for j in range(8)] for _ in range(150)]}
late = []
for line in open('late_event_S9_search_v1.out'):
    m = re.search(r'LATE seed \d+: .* V=(\[[^\]]*\]) subject (\d+)', line)
    if m: V = ast.literal_eval(m.group(1)); late.append((V, V.index(int(m.group(2)))))
for name, arrs in fams.items():
    c = Counter(); gapR = []
    for V in arrs:
        if len(set(V)) < 8: continue
        for k in range(8):
            R, r, mx = test(V, k); c['ok' if mx <= 1 else 'over'] += 1; gapR.append(abs(R - r))
    print(f"{name:24s}: runners with every |dev| <= 1 slot: {c['ok']} of {c['ok'] + c['over']}; "
          f"|R* - nearest odd| max {float(max(gapR)):.3f}, median {float(sorted(gapR)[len(gapR)//2]):.3f}")
c = Counter(); worst = F(0)
for V, k in late:
    R, r, mx = test(V, k); c['ok' if mx <= 1 else 'over'] += 1; worst = max(worst, mx)
print(f"{'late events (34)':24s}: runners with every |dev| <= 1 slot: {c['ok']} of {c['ok'] + c['over']}; worst dev {float(worst):.3f} slots")
