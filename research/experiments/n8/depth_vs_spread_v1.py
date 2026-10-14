"""Does the spread bound the cascade depth or D_final?  Cascade recursion (scale_cascade_recursion_v1, unchanged rule) on
(1,2,...,7, 9 -+ delta) for shrinking delta.  d_min and d_max stay essentially fixed.  Runner 1 and runner 2 reported."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fractions import Fraction as F
from math import floor
import io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    from scale_cascade_recursion_v1 import cascade
    from full_transit_positions_v2 import first_time
print(f"{'r8':>14} | {'runner':>6} | {'d_min':>8} {'d_max':>8} | {'scales':>6} | {'D_final':>14} | {'t':>14} | t*d_min | = BSM")
for sgn in (-1, 1):
    for k in range(1, 7):
        delta = F(1, 10 ** k)
        V = [F(j) for j in range(1, 8)] + [F(9) + sgn * delta]
        for i in (0, 1):
            scale, last, steps, D = cascade(V, i)
            t = 1 / (8 * scale)
            ds = [abs(V[j] - V[i]) for j in range(8) if j != i]
            ok = (t == first_time(V, i)) if k <= 3 else "skip"
            print(f"{str(V[7]):>14} | r{i+1:>5} | {float(min(ds)):>8.4g} {float(max(ds)):>8.4g} | {steps+1:>6} | {float(scale):>14.6g} | {float(t):>14.6g} | {float(t*min(ds)):>7.4g} | {ok}")
