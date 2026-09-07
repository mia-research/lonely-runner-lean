"""Tasks 2+3: exact-rational enumeration of the cells cut on [1/8,7/8] by j/m, m in {1,3,5,7},
their unit floor states, unit bad sets, and uncovered residues. Fractions only -- no floats."""
from fractions import Fraction as F
from math import gcd
n = 8
UNITS = [1, 3, 5, 7]

def Sol(e, j, n):
    return frozenset(r for r in range(n) if (e*r - j) % n == 0)
def bad(e, t, n):
    return Sol(e, (-t) % n, n) | Sol(e, (-(t+1)) % n, n)

lo, hi = F(1, 8), F(7, 8)
pts = {lo, hi}
for m in (1, 3, 5, 7):
    j = 0
    while F(j, m) <= hi:
        if lo <= F(j, m) <= hi:
            pts.add(F(j, m))
        j += 1
pts = sorted(pts)
print("breakpoints on [1/8,7/8] (exact):", [str(p) for p in pts])
print("number of cells:", len(pts) - 1)

rows = []
for i in range(len(pts) - 1):
    a, b = pts[i], pts[i+1]
    x = (a + b) / 2                      # exact rational interior point
    ts = {e: (e*x).numerator // (e*x).denominator for e in UNITS}   # exact floor
    # confirm the floor is CONSTANT on the whole open cell by checking endpoints' limits
    for e in UNITS:
        lo_f = (e*a).numerator // (e*a).denominator
        # sup limit: floor of e*b from below
        eb = e*b
        hi_f = eb.numerator // eb.denominator - (1 if eb.denominator == 1 else 0)
        assert lo_f == ts[e] == hi_f, (a, b, e, lo_f, ts[e], hi_f)
    U = set()
    for e in UNITS:
        U |= bad(e, ts[e], n)
    unc = sorted(set(range(n)) - U)
    parities = sorted({r % 2 for r in unc})
    rows.append((a, b, ts, unc, parities))

print()
hdr = f"{'cell [a,b)':<20}{'t1 t3 t5 t7':<14}{'uncovered':<16}{'parities':<12}mixed?"
print(hdr); print("-"*len(hdr)+"----")
mixed = []
for a, b, ts, unc, par in rows:
    m = (par == [0, 1])
    if m: mixed.append((a, b, unc))
    print(f"[{a},{b})".ljust(20)
          + f"{ts[1]}  {ts[3]}  {ts[5]}  {ts[7]}".ljust(14)
          + str(unc).ljust(16) + str(par).ljust(12) + ("YES" if m else "no"))

print("\nMIXED-PARITY CELLS:", len(mixed))
for a, b, unc in mixed:
    print(f"   [{a},{b})  uncovered={unc}")

# group adjacent mixed cells into maximal windows
wins = []
for a, b, unc in mixed:
    if wins and wins[-1][1] == a and wins[-1][2] == unc:
        wins[-1] = (wins[-1][0], b, unc)
    else:
        wins.append((a, b, unc))
print("\nmaximal contiguous mixed WINDOWS (same uncovered set):", len(wins))
for a, b, unc in wins:
    print(f"   [{a},{b})  uncovered={unc}  length={b-a}")
