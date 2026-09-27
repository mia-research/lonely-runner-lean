"""Named instants for every runner of the AP with deviations |e_i| <= 1/32 (speeds c + i + e_i), checked exactly on
random deviations and on all 2^8 corner deviations e_i = +-1/32 (plus 0), and the smallest band margin found.
  interior k = 1..6: t = 1/(8 min(a, b)), a = 1 + e_{k+1} - e_k, b = 1 + e_k - e_{k-1};
  ends (k = 0, and k = 7 mirrored) with readings r_j (distance to the j-th runner out): t = 1/(8 r_1) if r_7 <= 7 r_1,
  else 49/(8 r_7)."""
import random, itertools
from fractions import Fraction as F
def nd(x): x = x % 1; return min(x, 1 - x)
def instant(e, k):
    if 1 <= k <= 6:
        a = 1 + e[k + 1] - e[k]; b = 1 + e[k] - e[k - 1]; return F(1, 8) / min(a, b)
    r = [None] + [(j + e[j] - e[0]) if k == 0 else (j + e[7] - e[7 - j]) for j in range(1, 8)]
    return F(1, 8) / r[1] if r[7] <= 7 * r[1] else F(49, 8) / r[7]
def check(e):
    v = [i + e[i] for i in range(8)]; worst = F(1)
    for k in range(8):
        t = instant(e, k)
        for j in range(8):
            if j == k: continue
            m = nd((v[j] - v[k]) * t) - F(1, 8)
            if m < 0: return None, (k, j)
            worst = min(worst, m)
    return worst, None
rho = F(1, 32); bad = []; worst = F(1); n = 0
for signs in itertools.product((-1, 0, 1), repeat=8):
    e = [s * rho for s in signs]; w, b = check(e); n += 1
    if w is None: bad.append((signs, b))
rnd = random.Random(48)
for _ in range(20000):
    e = [rho * F(rnd.randint(-1000, 1000), 1000) for _ in range(8)]; w, b = check(e); n += 1
    if w is None: bad.append((e, b))
print(f"{n} deviation vectors (3^8 = 6561 corner/centre + 20000 random), every runner: failures {len(bad)}", bad[:3])
