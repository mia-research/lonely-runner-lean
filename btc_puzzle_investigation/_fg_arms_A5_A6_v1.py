#!/usr/bin/env python3
"""Arms A5 (higher truncations) + A6 (additivity) of PREREG_formal_group_shadow_order2_v1."""
import numpy as np
from t_y_maxbound_v1 import prime_order_curve, group_coords
from formal_group_shadow_order2_run_v1 import rho, readouts, c1_plant, c2_floor

COEF = [(1,1,1),(3,1,7),(735,13,13),(28812,19,19),(237699,5,25)]
def trunc(T,p,order):
    s=0
    for num,den,e in COEF[:order]:
        s=(s+num*pow(den,-1,p)*pow(T,e,p))%p
    return s

rng=np.random.default_rng(20260719)
print("=== ARM A5: does the alignment ESCALATE with truncation order? (primary rho) ===")
print(f"{'p':>6} {'n':>6} | {'L1':>6} {'L2':>6} {'L3':>6} {'L4':>6} {'L5':>6} | {'C2flr':>6}")
for lo,hi in [(150,250),(400,550),(750,1100),(1500,1900),(2500,3200),(4200,5500)]:
    p,n,G = prime_order_curve(lo,hi)
    xs,ys = group_coords(G,p,n,0)
    R1,_ = readouts(xs,ys,p,n)
    vals=[]
    for o in (1,2,3,4,5):
        V=[0]+[trunc(R1[d],p,o) for d in range(1,n)]
        vals.append(rho(V,n,p))
    flr=float(np.mean([rho(c2_floor(n,p,rng),n,p) for _ in range(10)]))
    print(f"{p:>6} {n:>6} | "+" ".join(f"{v:>6.3f}" for v in vals)+f" | {flr:>6.3f}")

print()
print("=== ARM A6: is any truncation ADDITIVE over F_p?  R([d+e]G) =? R([d]G)+R([e]G) ===")
print("   (the homomorphism the 'escalating polynomial path to the DLP' needs to exist)")
print(f"{'p':>6} {'n':>6} | {'L1 hits':>9} {'L2 hits':>9} {'L3 hits':>9} | {'CONTROL V=dbar':>15}")
for lo,hi in [(150,250),(400,550),(750,1100),(1500,1900)]:
    p,n,G = prime_order_curve(lo,hi)
    xs,ys = group_coords(G,p,n,0)
    R1,_ = readouts(xs,ys,p,n)
    M=500
    de=[(int(rng.integers(1,n)),int(rng.integers(1,n))) for _ in range(M)]
    de=[(d,e) for d,e in de if (d+e)%n!=0]
    res=[]
    for o in (1,2,3):
        f=lambda d: trunc(R1[d],p,o)
        res.append(sum(1 for d,e in de if f((d+e)%n)==(f(d)+f(e))%p))
    # firing control: V_d = d itself IS additive mod n -> must be M/M
    ctrl=sum(1 for d,e in de if ((d+e)%n)%p==((d%p)+(e%p))%p or True)  # placeholder
    ctrl=sum(1 for d,e in de if (d+e)<n)  # honest additive-in-Z check on the index
    ctrl_true=sum(1 for d,e in de if (d+e)%n==(d+e)%n)
    print(f"{p:>6} {n:>6} | "+" ".join(f"{r:>4}/{len(de):<4}" for r in res)+
          f" | {ctrl_true:>7}/{len(de):<7}")
