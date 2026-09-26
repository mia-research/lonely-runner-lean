"""The 10 reading sets (<= 32) that no proved lemma and no rung-R1 instant isolates (E88), followed through the cascade.
For each: the cascade's isolation t* = (8k+1)/(8e) (scale reading e, lap k), R = 8 d_min t*, moves; every reading's
position in eighths at t*; and the owner's check: pairs of readings that share an eighth at the unit grid t = 1/8 and at
the bound t = 1/(8 d_min) (same slot there), which no scale in the menu separates.  Exact."""
from fractions import Fraction as F
from math import floor
from residual_cascade_v1 import cascade_flank

EX = [(3,4,5,6,7,9,32), (3,4,5,7,9,12,32), (3,4,5,7,17,18,32), (3,5,6,7,8,26,27), (3,5,6,7,8,27,30),
      (3,5,7,8,12,26,27), (3,5,7,8,12,27,30), (3,5,7,8,18,26,29), (3,5,7,8,18,29,30), (4,5,6,8,14,27,32)]
for T in EX:
    t, e, k, mv = cascade_flank(list(T)); R = 8 * T[0] * t
    pos = [round(float((8 * d * t) % 8), 3) for d in T]
    def shared(tt):
        slots = {}
        for d in T: slots.setdefault(floor(((8 * d * tt) % 8) + F(1, 2)) % 8, []).append(d)
        return {s: v for s, v in slots.items() if len(v) > 1}
    print(f"T {T}: isolation t* = {t} (scale reading {e}, lap {k}), R = {float(R):.3f}, {mv} moves")
    print(f"    positions at t* (eighths): {pos}")
    print(f"    readings sharing an eighth at t = 1/8: {shared(F(1, 8))};  at the bound 1/(8 d_min): {shared(F(1, 8 * T[0]))}")
