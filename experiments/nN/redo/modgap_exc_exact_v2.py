"""modgap_exc_exact_v2 (2026-10-06): the exact statements about the 9 exceptions of modgap_nogood_v1 cited in E412 (replaces modgap_exc_exact_v1, whose 'large' label compared d_min with 10^29 and whose R7 window was
(21/20, 3/2); the correct exact statements follow).  Exceptions: the sets of T1 and hard_sets_41_60 with d_min = 0 mod 8 and no good d at the first 1/7-component.  Large = d_min >= 10^20 (8 sets), small = the other (1 set).
Checked exactly (integers and Fractions): for the large ones d_min >= 10^26, 26 d_min < d_2 (and whether 30 d_min < d_2 holds for all), 1 < R7 < 3/2 with R7 = 7 d_min t, t the 1/7 landing of the full seven readings
(cascade walk, exact), the least and greatest R7 compared with 1049/1000 and 146/100; for all nine: d_7 < 7 d_2; for the small one: rho_2 and R7 as exact Fractions."""
import sys, math
sys.path.insert(0, '.')
exec(open('modgap_dmin_perturb_v1.py').read().split("rnd = random.Random")[0])
from fractions import Fraction as F
H = F(1, 7)
def cd(x):
    x = x - math.floor(x); return min(x, 1 - x)
def landing(S):
    t = F(1, 7 * S[0])
    for _ in range(80):
        B = [x for x in S if cd(x * t) < H]
        if not B: return t
        t = max(F(7 * round(x * t) + 1, 7 * x) for x in B)
    return None
large = [S for S in exc if S[0] >= 10 ** 20]; small = [S for S in exc if S[0] < 10 ** 20]
R = {S: 7 * S[0] * landing(S) for S in exc}
out = open('modgap_exc_exact_v2.out', 'w'); out.write(__doc__ + "\n")
out.write("exceptions: %d (large %d, small %d)\n" % (len(exc), len(large), len(small)))
out.write("large: d_min >= 10^26 for all: %s\n" % all(S[0] >= 10 ** 26 for S in large))
out.write("large: 26 d_min < d_2 for all: %s; 30 d_min < d_2 for all: %s\n" % (all(26 * S[0] < S[1] for S in large), all(30 * S[0] < S[1] for S in large)))
out.write("large: 1 < R7 < 3/2 for all: %s; R7 > 1049/1000 for all: %s; R7 < 146/100 for all: %s; R7 > 21/20 for all: %s\n" %
          (all(1 < R[S] < F(3, 2) for S in large), all(R[S] > F(1049, 1000) for S in large), all(R[S] < F(146, 100) for S in large), all(R[S] > F(21, 20) for S in large)))
out.write("all nine: d_7 < 7 d_2: %s\n" % all(S[-1] < 7 * S[1] for S in exc))
for S in small: out.write("small exception %s: rho_2 = %s, R7 = %s\n" % (S, F(S[1], S[0]), R[S]))
out.close(); print(open('modgap_exc_exact_v2.out').read()[len(__doc__):])
