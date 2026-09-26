"""Step 3 probe of E81: bands 0 and 1 are mirror images.  In R = 8 d_min t, runner j sits at rho_j R/8; at 16 - R it sits
at 2 rho_j - rho_j R/8, i.e. the reflection of its band-0 position shifted by frac(2 rho_j) (runner 0: shift 0, so the
nearest runner's pattern is exactly mirrored).  For each hard case (hard_cases_v1), at the landing instant R* in band 1:
the mirror instant 16 - R* in band 0 (blocked, since band 0 is fully blocked in a late event); the runners blocking it;
their shifts frac(2 rho_j); and their positions at R* (clear).  Exact."""
import re
from fractions import Fraction as F
from arrangement_lib import nd
from hard_cases_v1 import relay

def pos8(r, R):  # position in eighths
    return float(((r * R / 8) % 1) * 8)

Vs = []
for line in open('hard_cases_v1.out'):
    m = re.search(r'V (\[[^\]]*\])', line)
    if m: Vs.append(eval(m.group(1)))
for V in Vs[:8]:
    w, R, ds = relay(V); rho = [F(d, ds[0]) for d in ds]
    Rm = 16 - R
    block = [j for j in range(7) if nd(rho[j] * Rm / 8) < F(1, 8)]
    print(f"V {V}: R* = {float(R):.4f}, mirror 16 - R* = {float(Rm):.4f}")
    print(f"   shifts frac(2 rho_j): {[round(float((2 * r) % 1), 3) for r in rho]}")
    print(f"   blocking the mirror instant: {block}; their positions there (eighths) {[round(pos8(rho[j], Rm), 3) for j in block]}; "
          f"at R* {[round(pos8(rho[j], R), 3) for j in block]}")
    print(f"   all positions at R* (eighths): {[round(pos8(r, R), 3) for r in rho]}")
