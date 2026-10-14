"""The user's list carries an unverified claim: s_7 * R = 89 = 8*11+1, giving R <= 89/S.
Theorem 11.1 records R = c(8M+1)/a for the last setter a at lap M.  So the claim is that the
last setter is s_7 at lap 11 with c = 1.  Test it."""
from fractions import Fraction as F
import random

def clear(S, x):
    for s in S:
        y = s*x
        if abs(y - 8*round(y/8)) < 1: return False
    return True
def R_exact(S, hi=F(24)):
    c = {F(1)}
    for s in S:
        k = 0
        while F(8*k+1,1)/s <= hi:
            for num in (8*k+1, 8*k-1):
                if num > 0:
                    x = F(num,1)/s
                    if 1 <= x <= hi: c.add(x)
            k += 1
    for x in sorted(c):
        if clear(S, x): return x
    return None

print("deep cases on file:")
for d in ([2520,5750,8003,10557,13161,14580,18745],
          [158,367,505,664,827,918,1179],
          [46,107,146,194,241,268,344]):
    S=[F(x,d[0]) for x in d]; R=R_exact(S); s7=max(S)
    print(f"  R = {R} = {float(R):.6f}   s7*R = {s7*R} = {float(s7*R):.4f}"
          f"   {'= 89' if s7*R == 89 else ''}")
print()
rng = random.Random(20260919)
mx = None; over = 0; tot = 0
for _ in range(6000):
    d = sorted(rng.sample(range(1, 3000), 7))
    S = [F(x, d[0]) for x in d]
    if len(set(S)) != 7 or min(S) != 1: continue
    R = R_exact(S)
    if R is None: continue
    tot += 1
    v = max(S) * R
    if v > 89: over += 1
    if mx is None or v > mx[0]: mx = (v, d, R)
print(f"random profiles: {tot:,}")
print(f"  s7*R > 89 : {over}")
print(f"  max s7*R  : {mx[0]} = {float(mx[0]):.4f}   at R = {float(mx[2]):.4f}")
print(f"\n  89 = 8*11+1.  If s7*R <= 89 always then R <= 89/s7, which for s7 >= 7.45 gives R < 12.")
