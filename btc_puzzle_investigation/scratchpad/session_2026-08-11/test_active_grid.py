# Doc 23 active-grid sieve. Reproduce the F_991 run and locate where d enters.
p=991; n=1009
# the doc's run: d=314, d_i sequence, "Sum Point Scalar" column
di   = [86,779,222,790,832,514,299,818,507,65,631,186,680,426,861]
scal = [400,84,536,95,137,828,613,123,821,379,945,500,994,740,166]
eps  = [0,1,0,1,1,0,0,1,0,0,0,0,0,0,1]
d=314

print("=== SMOKING GUN: is 'Sum Point Scalar' just (d + d_i) mod n, computed FROM the known d? ===")
ok=all((d+di[i])%n==scal[i] for i in range(len(di)))
print(f"  (d=314 + d_i) mod 1009 == doc's 'Sum Point Scalar' column: {ok}")
print(f"  e.g. d_i=779: 314+779={314+779} mod 1009 = {(314+779)%n} (doc says {scal[1]})")
# eps_i = [u_sum < d_i]  (wrap indicator) -- reproduce
ok2=all((1 if scal[i]<di[i] else 0)==eps[i] for i in range(len(di)))
print(f"  eps_i == [u_sum < d_i] (wrap indicator): {ok2}")
print("  => the run computes u_sum = d + d_i USING d=314. eps_i is derived from the KNOWN scalar.")

print("\n=== Reproduce the full bisection driven by the KNOWN d (binary search with a d-oracle) ===")
import random
random.seed(0)
lo,hi=0,n-1
count=0
# eps oracle uses d (as the run does): u_sum=(d+di)%n; eps=[u_sum<di]; constrain d
# eps=1 => d+di>=n => d>=n-di ; eps=0 => d<n-di
while hi-lo>0 and count<2000:
    di_r=random.randrange(1,n)
    u=(d+di_r)%n
    e=1 if u<di_r else 0
    if e==1: lo=max(lo, n-di_r)
    else:    hi=min(hi, n-di_r-1)
    count+=1
print(f"  bisection using d-oracle: recovered [{lo},{hi}] in {count} steps; ==314: {lo==hi==314}")

print("\n=== §3 step 2 -- the actual crux: does F(P)=chi3(x)y give the SCALAR u_0? ===")
# F gives j (mu3 index) and s (parity) only. u_0 (orbit-rep scalar) = discrete log. Demonstrate:
# many scalars share the same (j,s); F does not pin the scalar.
Fp=__import__('sympy').GF if False else None
# quick: build E(F_991), compute chi3-index j and parity-ish for all d, show (j) has ~n/3 collisions
def egcd(a,b):
    if a==0: return b,0,1
    g,x,y=egcd(b%a,a); return g,y-(b//a)*x,x
def modinv(a,m):
    g,x,_=egcd(a%m,m); return x%m
def padd(P,Q):
    if P is None: return Q
    if Q is None: return P
    x1,y1=P;x2,y2=Q
    if x1==x2 and (y1+y2)%p==0: return None
    if P==Q: l=(3*x1*x1)*modinv(2*y1,p)%p
    else: l=(y2-y1)*modinv((x2-x1)%p,p)%p
    x3=(l*l-x1-x2)%p;y3=(l*(x1-x3)-y1)%p;return (x3,y3)
# generator G with order n=1009: find one
def order_pt(P):
    Q=P;k=1
    while Q is not None:
        Q=padd(Q,P);k+=1
    return k
G=None
for gx in range(p):
    ys=[y for y in range(p) if (y*y-gx**3-7)%p==0]
    if ys:
        cand=(gx,ys[0])
        if order_pt(cand)==n: G=cand;break
beta=113
def chi3idx(x):
    t=pow(x%p,(p-1)//3,p); b=beta%p; b2=b*b%p
    return {1:0,b:1,b2:2}.get(t,None)
from collections import Counter
jc=Counter()
cur=None
for dd in range(1,n):
    cur=padd(cur,G)
    jc[chi3idx(cur[0])]+=1
print(f"  E(F_991) generator {G}; distribution of chi3-index j over all {n-1} scalars: {dict(jc)}")
print(f"  => j takes 3 values, ~{ (n-1)//3 } scalars each. F(P) gives j (and s): ~2.58 bits, NOT the scalar u_0.")
print("  step 2 ('reconstruct u_sum = (-1)^s u_0 lam^j') needs u_0 = the discrete log. Circular.")

print("\n=== §5 scaling, taken at face value ===")
import math
print(f"  M=1e6 keys -> width n/M = 2^256/1e6 ~ 2^{256-math.log2(1e6):.0f}; intersect 2^135 -> ~2^115.")
print(f"  2^115 is NOT O(1) and NOT solved; and every eps_i needs d. Doc's 'O(1) / DLP dissolved' is false.")
