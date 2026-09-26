"""Check, exactly, the first-order law at the progression.  Readings j*d (j = 1..7); at t = a/(8d), a in {1,3,5,7},
every runner sits on an odd multiple of 1/8; those at +-1/8 are j = a (mod 8 inverse) and 8 - that.  Perturb the
readings to j*d + s*e_j.  First order: instant a opens iff  e_j + j*y >= 0 (runner at +1/8) and e_j' + j'*y <= 0
(runner at -1/8) have a common y.  Prediction: a = 1 opens iff e_7 < 7 e_1; a = 7 iff e_7 > 7 e_1; a = 3 opens iff
3 e_5 < 5 e_3; a = 5 iff 3 e_5 > 5 e_3.  Test: exact event of the slowest runner at small s along random integer
directions, against the prediction's first open instant."""
import random
from fractions import Fraction as F
from arrangement_lib import nd
from pinchoff_v1 import cascade_from, EIGHTH
rnd = random.Random(7); d = 700; agree = tot = 0; bad = []
for trial in range(400):
    e = [rnd.randint(-50, 50) for _ in range(7)]
    s = F(1, 10**6)
    ds = [(j + 1) * d + s * e[j] for j in range(7)]
    if sorted(ds) != ds: continue
    t, ch = cascade_from(ds, EIGHTH / ds[0]); R = 8 * ds[0] * t
    open_ = [a for a, ok in ((1, e[6] < 7 * e[0]), (3, 3 * e[4] < 5 * e[2]), (5, 3 * e[4] > 5 * e[2]), (7, e[6] > 7 * e[0])) if ok]
    pred = min(open_) if open_ else None
    tot += 1; hit = pred is not None and abs(R - pred) < F(1, 1000); agree += hit
    if not hit: bad.append((e, float(R), pred))
print(f"directions {tot}; event at the predicted first open progression instant {agree}")
for b in bad[:10]: print("  mismatch", b)
