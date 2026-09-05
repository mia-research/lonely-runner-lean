"""Exact read-off spec per (i,j,c): selector floor(pt)=N*d+rho+kappa*m and line
X=(iota/N)A+beta, with beta=((2*iota*rho+gamma) mod 2N)/(2N). Pick kappa (smallest)
with iota*kappa+gamma ≡ 0 mod N, then rho giving X in [1/6,1/2] for widest A-window
in [1/6,1/3] (>= N/30 wide for grid feasibility at q>=30)."""
from fractions import Fraction as F
CASES = {(2,3):[3,4],(2,-3):[-5,-4],(3,4):[4,5],(3,-4):[-6,-5],(4,3):[2,3,4],
         (4,-3):[-5,-4],(5,3):[2,3,4],(5,-3):[-6,-5,-4],(5,-4):[-7,-6,-5]}
def kappa_for(iota,gamma,N):
    for k in range(-N,N+1):
        if (iota*k+gamma)%N==0: return k
    return None
def beta_of(iota,gamma,rho,N): return F((2*iota*rho+gamma)%(2*N),2*N)
def window(slope,beta):
    if slope>0: lo=max(F(1,6),(F(1,6)-beta)/slope); hi=min(F(1,3),(F(1,2)-beta)/slope)
    else: lo=max(F(1,6),(F(1,2)-beta)/slope); hi=min(F(1,3),(F(1,6)-beta)/slope)
    return lo,hi
for (i,j),cs in CASES.items():
    N=abs(j); iota_base = i if j>0 else -i
    print(f"\n##### ({i},{j}) N={N} slope={iota_base}/{N}")
    for c in cs:
        gamma = c if j>0 else -c
        iota=iota_base
        k=kappa_for(iota,gamma,N)
        e=(iota*k+gamma)//N
        slope=F(iota,N)
        best=None
        for rho in range(N):
            beta=beta_of(iota,gamma,rho,N)
            lo,hi=window(slope,beta)
            if hi>lo:
                w=hi-lo
                if best is None or w>best[0]: best=(w,rho,beta,lo,hi)
        w,rho,beta,lo,hi=best
        feas = w>=F(N,30)
        # selector floor(pt) = N d + rho + k m ; shift integer = iota*d + e*m + (iota*rho + gamma//2 - beta*N)/...
        # compute integer shift coefficient for m: e ; for d: iota
        print(f"  c={c}: |j|r={iota}p+{gamma}q  sel floor(pt)={N}d+{rho}+({k})m  "
              f"beta={beta} X=({iota}/{N})A+{beta} A∈[{lo},{hi}] w={float(w):.3f} feas={feas}")
