"""Order 8, exact AP readings (deviation 0): the cascade's R for seven integer readings with no index = 0 (mod 8)
versus with a slot-sharer.  Random 7-subsets of 2..60 (exact rationals)."""
from fractions import Fraction as F
import math, random
def near(x): return math.floor(x + F(1, 2))
def cascade(s, n=8):
    R = F(1)
    while True:
        best = R; who = False
        for sx in s:
            v = sx * R; N = near(v / n)
            if abs(v - n * N) < 1:
                c = F(n * N + 1) / sx
                if c > best: best, who = c, True
        if not who: return R
        R = best
rng = random.Random(8); mx_no = F(0); mx_sh = F(0); cnt_no = cnt_sh = 0
for _ in range(20000):
    s = sorted(rng.sample(range(2, 61), 7))
    R = cascade([F(x) for x in s])
    if any(x % 8 == 0 for x in s): mx_sh = max(mx_sh, R); cnt_sh += 1
    else: mx_no = max(mx_no, R); cnt_no += 1
print(f'no slot-sharer: {cnt_no} arrangements, max R {mx_no} | with a slot-sharer: {cnt_sh}, max R {mx_sh}')
