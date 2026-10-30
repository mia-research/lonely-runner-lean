"""E656 place test. Class: gap-strip records (G > 0) with the subject's nearest reading at its own block's step u.
Place named from the readings: Q = the earliest t = c/(4s), c odd (s the other block's step), with
1/(8u) <= t <= 7/(8Ju) (the own window W) and 8 x_0 t an odd integer (x_0 the other block's reading nearest the
subject). At Q every other-block reading has 8 x_i Q = 8 x_0 Q + 2 c i, odd (forced), and the own block is clear (W).
Checks: (1) Q lonely (exact, every reading; expected by the above); (2) Q equal to the cascade's landing; misses by
kind (no Q in W; Q later than the landing; Q earlier would contradict the landing being first). Exact Fractions."""
import math, pickle
from fractions import Fraction as F
from collections import Counter
E = F(1, 8)
def dist(x):
    f = x - math.floor(x); return min(f, 1 - f)
recs = pickle.load(open('two_block_strip_cascade_v1.pkl', 'rb'))
def sp(p, A, b): return [F(i) for i in range(p)] + [A + j * b for j in range(8 - p)]
res = Counter(); ex = Counter(); samp = []
for (p, b, G, k, t, op, M, mv, R, r) in recs:
    if G <= 0: continue
    v = sp(p, G + p - 1, b)
    ownb = list(range(p)) if k < p else list(range(p, 8)); u = F(1) if k < p else b; s = b if k < p else F(1)
    ds = [abs(v[i] - v[k]) for i in range(8) if i != k]
    if min(ds) < u: continue
    J = max(ownb.index(k), len(ownb) - 1 - ownb.index(k))
    lo, hi = F(1, 8) / u, F(7, 8) / (J * u)
    x0 = min(abs(v[i] - v[k]) for i in range(8) if i not in ownb)
    Q = None
    c = max(1, math.floor(4 * s * lo) - 1)
    if c % 2 == 0: c += 1
    while F(c, 4) / s <= hi:
        tc = F(c, 4) / s
        if tc >= lo:
            y = 8 * x0 * tc
            if y.denominator == 1 and y.numerator % 2 == 1: Q = tc; break
        c += 2
    if Q is None: res['no Q in W'] += 1; continue
    lonely = all(dist(d * Q) >= E for d in ds)
    if not lonely: res['Q not lonely'] += 1
    if Q == t: res['Q = landing'] += 1
    elif Q > t: res['Q later than landing'] += 1; ex[(p, len(ownb), 'b<1' if b < 1 else 'b>1')] += 1
    else: res['Q EARLIER than landing'] += 1; samp.append((p, b, G, k, Q, t))
print(dict(res))
print("Q later than landing, by (p, own block size, b):", sorted(ex.items()))
print("Q earlier (should be impossible):", samp[:5])
