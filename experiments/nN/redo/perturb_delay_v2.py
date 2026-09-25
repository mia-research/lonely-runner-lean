"""The resonance behind the 191-move delay (perturb_delay_v1): exact event instant; unit-step perturbations;
then the family  slow = [8, 12, 38],  fast = N + (0, d, 2d, 3d) + last  (an exact AP of gap d, base N),
varying d and N, recording runner 8's cascade moves and event.  Looking for the exact ratio that sets
the delay.  Exact."""
from fractions import Fraction as F
from math import gcd
from arrangement_lib import readings
from isolated_persistence_v1 import cascade_cap
A = [8, 12, 38, 100005, 100016, 100027, 100038, 100048]
t, n = cascade_cap(readings(A, 0)); print(f"base: moves {n}, event t = {t} = {float(t):.8f};  t*8 = {t*8}, readings*t: {[str(r*t % 1) for r in readings(A,0)]}")
for idx in (3, 4, 5, 6):
    row = []
    for delta in range(-3, 4):
        V = list(A); V[idx] += delta
        if len(set(V)) < 8: row.append("dup"); continue
        Vs = sorted(V); nn = cascade_cap(readings(Vs, Vs.index(8)))[1]; row.append(str(nn))
    print(f"speed {A[idx]} moved by -3..+3: moves {row}")
print("family slow [8,12,38], fast N + (0, d, 2d, 3d) + tail 43 past the last:")
for d in (9, 10, 11, 12, 13):
    row = []
    for N in (50005, 100005, 200005):
        V = [8, 12, 38] + [N + i * d for i in range(4)] + [N + 3 * d + 10]
        nn = cascade_cap(readings(V, 0))[1]; row.append(f"N={N}:{nn}")
    print(f"   d={d}: " + "  ".join(row))
