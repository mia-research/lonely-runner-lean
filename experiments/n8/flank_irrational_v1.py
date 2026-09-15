"""Two and three irrational ratios against a live flank, exactly. Ratios rho = a + b·√2 (a, b rational, b ≠ 0), all in Q(√2)
(so the fractional parts are rationally dependent — the harder case for the argument). Threshold 1/n. At opening k the runner
sits at rho·(k + 1/n) laps; in the way iff within 1/n of an integer (strict), decided exactly with integer square roots.
For random pairs/triples: the first k with every runner clear (search to K). Then adversarial: ratios whose fractional parts
are within 10^−j·√2-ish of the shadowing half-integer pair, to show how late the first clear opening can come."""
from fractions import Fraction as F
import random, math
from lattice_witness_irrational_v1 import sign, floor_q2
def clear(a, b, n):
    k = floor_q2(a, b)
    return sign(a - k - F(1, n), b) >= 0 and sign(a - k - 1 + F(1, n), b) <= 0
def first_clear(rhos, n, K):
    for k in range(K):
        u = k + F(1, n)
        if all(clear(a * u, b * u, n) for a, b in rhos): return k
    return None
n = 8; rng = random.Random(5)
for size in (2, 3):
    worst = (0, None); none = 0
    for _ in range(400):
        rhos = [(F(rng.randint(0, 40)) + F(rng.randint(0, 99), 100), F(rng.choice([-1, 1]) * rng.randint(1, 500), 1000)) for _ in range(size)]
        k = first_clear(rhos, n, 5000)
        if k is None: none += 1
        elif k > worst[0]: worst = (k, rhos)
    print(f'{size} irrational ratios, 400 random sets: none clear within k < 5000: {none}; latest first clear opening k = {worst[0]}')
# adversarial: near the shadowing pair (fractional parts 1/2); the order-8 half-integer shadowing pairs from flank_shadow_v1
from flank_shadow_v1 import arc_in_way
pairs = []
for A1 in range(8):
    for A2 in range(A1, 8):
        r1, r2 = A1 + F(1, 2), A2 + F(1, 2)
        if all(arc_in_way(r1, k, n) or arc_in_way(r2, k, n) for k in range(2)): pairs.append((r1, r2))
print('shadowing half-integer pairs (whole part mod 8):', [(str(a), str(b)) for a, b in pairs])
r1, r2 = pairs[0]
for j in range(1, 6):
    eps = F(1, 10**j)
    rhos = [(r1, eps), (r2, -eps)]          # r1 + eps·√2, r2 − eps·√2
    k = first_clear(rhos, n, 10**6)
    print(f'   perturbed by ±10^-{j}·√2: first clear opening k = {k}')
