# Derivation check: ds = {2,3,4,5,6,7,x}, 16 | x, e = x, k = x/16, so A = 8k+1 = x/2 + 1.
# Claim: no wraparound (d*A < 8x for all d in ds\{x}), so d*A mod 8x = d*A, and each lands in [x,7x].
from fractions import Fraction as F
print("A = x/2 + 1.  For d in {2,...,7}:  d*A = d*x/2 + d.")
print("no-wraparound needs  7*A = 7x/2 + 7 < 8x   <=>  7 < 9x/2  <=>  x >= 2.\n")
print(f"  {'d':>2} | d*A            | >= x ?            | <= 7x ?")
for d in [2,3,4,5,6,7]:
    print(f"  {d:>2} | {d}x/2 + {d:<8} | {d}/2 >= 1 : {'yes' if d>=2 else 'NO':3}      | {d}x/2 + {d} <= 7x  <=> {d} <= {F(14-d,2)}x  <=> x >= {float(F(2*d,14-d)):.3f}")
print("\n  d = x : x*A mod 8x = x*(A mod 8); 16|x so x/2 = 0 mod 8, hence A = 1 mod 8,")
print("          so x*A mod 8x = x, which is the LEFT ENDPOINT of [x,7x] -- admissible")
print("          because the threshold is CLOSED (>= 1/8). This is Theorem 6.16.\n")
print("So every constraint holds for x >= 2 with 16 | x.  Elementary; no case analysis.\n")

# exhaustive confirmation of the no-wraparound and membership claims
bad=0
for m in range(1,3000):
    x=16*m
    A=x//2+1
    for d in [2,3,4,5,6,7]:
        v=d*A
        if not (v < 8*x and x <= v <= 7*x): bad+=1
    if (x*A) % (8*x) != x: bad+=1
print(f"confirmation over x = 16..{16*2999} step 16: violations = {bad}")
print("\nGRADE: this is PROVED (elementary arithmetic), not EMPIRICAL.")
print("It belongs in Flanks.lean as a lemma, not in a script.")
