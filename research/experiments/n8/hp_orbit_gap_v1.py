r"""hp_orbit_gap_v1 -- the dilation orbit of (1,3,5,7) contains unit 4-tuples with
gcd 3, 5, 7 ... which are NOT removed by the reduction on gcd(E_non), because the
fifth (non-unit) speed can be coprime to that gcd.  Compute |S| exactly for those
5-tuples.  If |S| < 1/2 for some primitive E_non, (H') as stated ("equivalently
|S| >= 1/2 for every non-representative primitive E_non") is refuted.
"""
import sys
from math import gcd
from fractions import Fraction as F
from nr2_core import safe_measure, boundary_audit, cell_table

R4 = (1, 3, 5, 7)

def orbit_tuple(lam):
    """lam odd: the tuple lam*(1,3,5,7) re-indexed by residue mod 8."""
    d = {}
    for base in (1, 3, 5, 7):
        e = lam * base
        d[e % 8] = e
    return tuple(d[r] for r in R4)

print("dilation orbit members and the 5-tuples they generate")
print(f"{'lam':>4} {'unit 4-tuple':>22} {'g4':>3} | rho0  e_rho0  gcd(E_non)   |S|            <1/2?")
worst = []
for lam in (1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21):
    sp4 = orbit_tuple(lam)
    g4 = 0
    for e in sp4:
        g4 = gcd(g4, e)
    for rho0 in (2, 4, 6):
        for q0 in range(0, 9):
            e0 = 8 * q0 + rho0
            if e0 in sp4:
                continue
            sp = sp4 + (e0,)
            g5 = 0
            for e in sp:
                g5 = gcd(g5, e)
            if g5 != 1:
                continue                      # removed by the REDUCTION
            S = safe_measure(sp, (1, 3, 5, 7, rho0))
            flag = "  ** < 1/2 **" if S < F(1, 2) else ""
            if S < F(1, 2):
                worst.append((lam, sp4, g4, rho0, e0, S))
            if lam > 1 and (S < F(1, 2) or q0 <= 2):
                print(f"{lam:>4} {str(sp4):>22} {g4:>3} | {rho0:>4}  {e0:>6}   {g5:>3}      "
                      f"{str(S):>14} {float(S):.5f}{flag}")
print()
print(f"primitive E_non with |S| < 1/2 found: {len(worst)}")
for w in worst:
    print("   ", w)
