"""Theorem 11.3 (MANUSCRIPT_v21 l.2493-2500): statement vs its proof's second step.
Statement: for AP readings 1..7, the clear R in [1,7] u [9,15] are exactly the odd integers.
Proof step as written: readings i=1 and i=7 ALONE leave only the odd integers.
Exact rational grid, denominator 840."""
from fractions import Fraction as F
def ok(x):
    r = x % 8
    return 1 <= r <= 7
N = 840
two_only, all7 = [], []
for num in range(N, 15 * N + 1):
    R = F(num, N)
    if not (1 <= R <= 7 or 9 <= R <= 15):
        continue
    if ok(R) and ok(7 * R):
        two_only.append(R)
    if all(ok(i * R) for i in range(1, 8)):
        all7.append(R)
print("clear with all seven readings:", [str(r) for r in sorted(set(all7))])
print("pass i=1 and i=7 only:", len(two_only))
print("non-integer examples passing i=1 and i=7:", [str(r) for r in two_only if r.denominator != 1][:6])
print("R=3/2 check: i=1", ok(F(3,2)), " i=7", ok(7*F(3,2)), " i=5", ok(5*F(3,2)))
