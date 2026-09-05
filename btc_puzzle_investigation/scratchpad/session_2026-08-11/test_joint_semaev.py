n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
lam = 0x5363AD4CC05C30E0A5261C028812645A122E22EA20816678DF02967C1B23BD72
assert pow(lam,3,n)==1

d130 = 0x33e7665705359f04f28b88cf897c603c9
d135 = 0x4123456789abcde0123456789abcdef012   # doc's SIMULATED value (not the real unknown)

def cr(d,s,j):
    val = ((-1)**s) * d * pow(lam,j,n)
    c = val // n          # floor division (works for negatives too)
    r = val - c*n         # 0 <= r < n
    return c, r

print("=== §1/§2: reproduce table and check c_sum = c1+c2+eps, eps=[r1+r2>=n] ===")
dsum = (d130 + d135) % n
ok=True
for s in [0,1]:
    for j in [0,1,2]:
        c1,r1 = cr(d130,s,j); c2,r2 = cr(d135,s,j); cs,rs = cr((d130+d135),s,j)
        eps = 1 if (r1+r2)>=n else 0
        law = (cs == c1 + c2 + eps)
        ok &= law
        print(f"  s={s} j={j}: c130={hex(c1)} c135={hex(c2)} csum={hex(cs)} eps={eps}  c_sum==c1+c2+eps: {law}")
print(f"  identity holds all branches: {ok}")

print("\n=== §3 CRUX: is c_sum (hence eps) measurable from PUBLIC data? ===")
print("  c_sum = floor((-1)^s (d130+d135) lam^j / n)  contains d135 (the unknown).")
print("  eps = [r1 + r2 >= n], r2 = d135 lam^j mod n  -- also needs d135.")
print("  => neither c_sum nor eps is computable from the public sum POINT (coords) without d135.")

print("\n=== §4-info: IF all 6 eps(s,j) were known, how much is d135 constrained? ===")
# The real eps-vector for the true d135:
def eps_vec(d):
    v=[]
    for s in [0,1]:
        for j in [0,1,2]:
            _,r1 = cr(d130,s,j); _,r2 = cr(d,s,j)
            v.append(1 if (r1+r2)>=n else 0)
    return tuple(v)
true_vec = eps_vec(d135)
print(f"  true eps-vector for simulated d135: {true_vec}")
# sample random d135 in the 135-bit range; fraction sharing the same eps-vector = selectivity
import random
random.seed(1)
lo, hi = 1<<134, 1<<135
N=200000; match=0
for _ in range(N):
    d=random.randrange(lo,hi)
    if eps_vec(d)==true_vec: match+=1
frac = match/N
import math
range_size = hi-lo
survivors = frac*range_size
print(f"  fraction of 135-bit range matching the eps-vector: {frac:.4f}  (~{match}/{N})")
print(f"  => candidates surviving all 6 eps constraints: ~{frac:.4f} * 2^134 ~ 2^{math.log2(max(survivors,1)):.1f}")
print(f"  (6 eps bits can remove at most ~6 bits; 135-bit space stays ~2^129, NOT O(1).)")

# also: are the 6 branches independent, or does s just flip? show s=1 is determined by s=0
print("\n  branch structure: eps(s=1,j) vs eps(s=0,j):")
for j in [0,1,2]:
    v0=eps_vec(d135)[j]; v1=eps_vec(d135)[3+j]
    print(f"    j={j}: eps(s=0)={v0} eps(s=1)={v1}")
