"""Owner (2026-09-25): take arrangements that delay the isolation, perturb them, and find the exact ratio at
play.  Arrangement A = [8, 12, 38, 100005, 100016, 100027, 100038, 100048]; runner at speed 8 needs 191
cascade moves (long_cascades_v1).  Its fast readings 99997, 100008, 100019, 100030, 100040 are an AP of
gap 11 except the last step (10).  Perturb ONE speed at a time over a range; for runner 8 record the
number of cascade moves and the event time.  Exact; every other runner's event also checked."""
from fractions import Fraction as F
from arrangement_lib import readings, nd, F
from isolated_persistence_v1 import cascade_cap
A = [8, 12, 38, 100005, 100016, 100027, 100038, 100048]
def moves_of(V, k):
    t, n = cascade_cap(readings(V, k)); return n, t
base_n, base_t = moves_of(A, 0)
print(f"base: runner 8 moves {base_n}, event t = {float(base_t):.6f}")
for idx in range(3, 8):
    row = []
    for delta in range(-12, 13, 2):
        V = list(A); V[idx] += delta
        if len(set(V)) < 8: row.append("  dup"); continue
        n, t = moves_of(sorted(V), sorted(V).index(8))
        row.append(f"{n:4d}")
    print(f"speed {A[idx]} moved by -12..+12 (step 2): moves " + " ".join(row))
# the exact-AP completion and the gap
for last in (100049, 100048, 100047):
    V = A[:7] + [last]; n, t = moves_of(V, 0)
    print(f"last speed {last} (fast readings {[v - 8 for v in V[3:]]}): moves {n}, event t = {float(t):.6f}")
