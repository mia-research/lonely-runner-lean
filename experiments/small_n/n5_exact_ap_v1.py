"""n=5, exact AP readings (deviation 0): R_final with and without a slot-sharer (index = 0 mod 5), index triples up to 40."""
from fractions import Fraction as F
import math, itertools
def near(x): return math.floor(x + F(1, 2))
def cascade(s):
    R = F(1)
    while True:
        best = R; who = False
        for sx in s:
            v = sx * R; N = near(v / 5)
            if abs(v - 5 * N) < 1:
                c = F(5 * N + 1) / sx
                if c > best: best, who = c, True
        if not who: return R
        R = best
mx_no = F(0); mx_sh = F(0); cnt = 0
for tri in itertools.combinations(range(2, 41), 3):
    R = cascade([F(x) for x in tri]); cnt += 1
    if any(x % 5 == 0 for x in tri): mx_sh = max(mx_sh, R)
    else: mx_no = max(mx_no, R)
print('triples', cnt, '| max R without a slot-sharer', mx_no, '| max R with a slot-sharer', mx_sh)
