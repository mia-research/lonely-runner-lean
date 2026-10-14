r"""hp_orbit_fibre_v1 -- run the FULL fibre criterion on the dilation-orbit unit
tuples lam*(1,3,5,7), lam odd.  These have u+2o = 37/35 (a-priori test fails) but
u+o = 3/5 < 1 so the discrepancy threshold is finite.  Question: does the fibre
criterion close them anyway?"""
from math import gcd
from fractions import Fraction as F
import nr2_unit_fibre as UF

R4 = (1, 3, 5, 7)
def orbit_tuple(lam):
    d = {}
    for base in R4:
        e = lam * base
        d[e % 8] = e
    return tuple(d[r] for r in R4)

for lam in (1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23, 25):
    sp4 = orbit_tuple(lam)
    res = UF.fibre(sp4)
    g = 0
    for e in sp4:
        g = gcd(g, e)
    print(f"lam={lam:>3} {str(sp4):>22} g={g:>3}  " +
          "  ".join(f"rho0={r}:{res[r][0]}{'' if res[r][1] is None else ' '+str(res[r][1])}"
                    for r in (2, 4, 6)))
