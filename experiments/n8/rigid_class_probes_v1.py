"""Necessity of C1 and C2 on NAMED probe tuples (not a sweep).
C1: T mod n covers all units of Z/n.   C2: every q in 2..n-1 divides some v in T."""
from fractions import Fraction as F
from math import gcd
import sys, io, contextlib
sys.path.insert(0, "experiments/n8")
with contextlib.redirect_stdout(io.StringIO()):
    from exact_phi_n_ap_v1 import lonely_set, phi

def C1(T, n): return {u for u in range(1, n) if gcd(u, n) == 1} <= {v % n for v in T}
def C2(T, n): return all(any(v % q == 0 for v in T) for q in range(2, n))
def rigid(T, n):
    pts, ivs = lonely_set(T, n)
    return (not ivs) and sorted(pts) == [F(r, n) for r in range(1, n) if gcd(r, n) == 1]

probes = [
 (5, [1,3,4,7],            "witness A"),
 (8, [1,2,3,4,5,7,12],     "witness B"),
 (8, [1,2,3,4,5,6,7],      "AP n=8"),
 (8, [1,3,5,7,9,11,13],    "all-odd  (C1 ok, C2 fails q=2)"),
 (8, [2,3,4,5,6,7,8],      "no unit 1? (2..8)"),
 (9, [1,2,3,4,5,6,7,8],    "AP n=9"),
 (9, [1,2,3,4,5,6,7,16],   "AP n=9 with 8->16"),
 (12,[1,2,3,4,5,6,7,8,9,10,11], "AP n=12"),
 (12,[1,2,3,4,5,6,7,8,9,10,23], "AP n=12 with 11->23"),
 (12,[1,2,3,4,5,6,7,8,9,10,13], "AP n=12 with 11->13 (13=1 mod 12)"),
]
print(f"{'label':34} {'C1':>5} {'C2':>5} {'C1&C2':>6} {'RIGID':>6}  {'#pts':>4} {'#ivs':>4}  consistent")
for n, T, lab in probes:
    pts, ivs = lonely_set(T, n)
    c1, c2, R = C1(T, n), C2(T, n), rigid(T, n)
    # necessity: R => C1 and R => C2 ;  sufficiency probe: C1&C2 => R
    ok = (not R or (c1 and c2))
    print(f"{lab:34} {str(c1):>5} {str(c2):>5} {str(c1 and c2):>6} {str(R):>6}  {len(pts):>4} {len(ivs):>4}  {'OK' if ok else 'NECESSITY VIOLATED'}"
          + ("" if (c1 and c2)==R else "   <-- C1&C2 != RIGID"))
