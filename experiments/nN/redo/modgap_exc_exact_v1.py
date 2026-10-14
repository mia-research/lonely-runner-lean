"""modgap_exc_exact_v1 (2026-10-06): exact integer/Fraction comparisons for the 9 exceptions of modgap_nogood_v1 (replacing the decimals of modgap_exc_ratios_v1).  For each exception S (d_min = S[0]):
 (a) 26 d_min < d_2 (integer comparison) and the exact least ratio d_2/d_min as a Fraction numerator and denominator digit counts;
 (b) the six readings above d_min: d_7/d_2 as an exact Fraction compared with 7 (spread below 7?);
 (c) the 1/7-landing t of the full seven readings (exact), R7 = 7 d_min t, and whether 21/20 < R7 < 3/2 (large ones) exactly;
 (d) 10^29 <= d_min for the 8 large ones (so |j| <= 16 changes d_min by a relative amount below 16/10^29, exactly)."""
import sys, math
sys.path.insert(0, '.')
exec(open('modgap_dmin_perturb_v1.py').read().split("rnd = random.Random")[0])
from fractions import Fraction as F
H = F(1, 7)
def cd(x):
    x = x - math.floor(x); return min(x, 1 - x)
out = open('modgap_exc_exact_v1.out', 'w'); out.write(__doc__ + "\n")
for S in exc:
    t = F(1, 7 * S[0])
    for _ in range(80):
        B = [x for x in S if cd(x * t) < H]
        if not B: break
        t = max(F(7 * round(x * t) + 1, 7 * x) for x in B)
    R7 = 7 * S[0] * t
    large = S[0] >= 10 ** 29
    out.write("%s: 26 d_min < d_2: %s; d_7/d_2 < 7: %s; (d_7/d_2 as Fraction, num/den digits) %d/%d; R7 in (21/20, 3/2): %s; R7 in (1, 4): %s; d_min >= 10^29: %s\n" %
              ('large' if large else 'small %s' % (S,), 26 * S[0] < S[1], F(S[-1], S[1]) < 7, len(str((F(S[-1], S[1])).numerator)), len(str((F(S[-1], S[1])).denominator)),
               F(21, 20) < R7 < F(3, 2), 1 < R7 < 4, S[0] >= 10 ** 29))
out.close(); print(open('modgap_exc_exact_v1.out').read()[len(__doc__):])
