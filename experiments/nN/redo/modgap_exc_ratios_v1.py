"""modgap_exc_ratios_v1 (2026-10-06): the 9 exceptions (no good d at the first 1/7-component) in cascade coordinates rho_y = d_y / d_min (exact fractions shown as decimals to 6 places, display only), with the
first 1/7-component of S minus d_min and S's own first lonely instant at 1/7 in R-coordinates R = 7 d_min t (the 1/7 analogue of R = 8 d_min t).  Exact."""
import sys, json
sys.path.insert(0, '.')
exec(open('modgap_dmin_perturb_v1.py').read().split("rnd = random.Random")[0])
from fractions import Fraction as F
out = open('modgap_exc_ratios_v1.out', 'w'); out.write(__doc__ + "\n")
for S in exc:
    rho = [F(d, S[0]) for d in S]
    path = []
    t = F(1, 7 * S[0])
    import math
    def cd(x):
        x = x - math.floor(x); return min(x, 1 - x)
    H = F(1, 7)
    for _ in range(60):
        B = [x for x in S if cd(x * t) < H]
        if not B: break
        t = max(F(7 * round(x * t) + 1, 7 * x) for x in B)
    out.write("S small? %s  rho = %s  classes %s  1/7-landing R7 = 7 d_min t = %.6f\n" %
              (S if len(str(S[-1])) < 6 else '[%d-digit]' % len(str(S[-1])), ['%.5f' % float(r) for r in rho], ''.join(('m' if d % 8 == 0 else 'o' if d % 2 else 't' if d % 4 == 2 else 'f') for d in S), float(7 * S[0] * t)))
out.close(); print(open('modgap_exc_ratios_v1.out').read()[len(__doc__):])
