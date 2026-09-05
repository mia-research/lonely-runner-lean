"""
DECISIVE TEST OF THE MECHANISM.  Exact integers only.

Claim: Sum_{c in F_{p^k}} chi2^{(k)}( f(c) ) = -a_{p^k}(C),  C: y^2 = f(c),
       f(c) = (c^3+Ac+B) * q_R(c),  genus 3, branch locus = x(E[2]) u x([2]^-1 R) (8 pts with oo).
V = E[2] acts on P^1=E/pm preserving that locus => Jac(C) ~ E1 x E2 x E3 (three genus-1 quotients).

n odd  <=>  x^3+Ax+B irreducible  <=>  Frobenius 3-CYCLES T1,T2,T3, hence 3-cycles E1,E2,E3.
A block-permutation with no fixed block has trace 0.  Therefore:

   k=1 : Frob    is a 3-cycle  -> sum = 0
   k=2 : Frob^2  is a 3-cycle  -> sum = 0        <-- PREDICTION
   k=3 : Frob^3  is TRIVIAL    -> sum != 0       <-- FALSIFIER (must be nonzero generically)

If k=2 vanishes and k=3 does not, the 3-cycle mechanism is confirmed and nothing else explains it.
"""
import sys
sys.path.insert(0,'scratchpad/n8')
from pencil_vanishing_v1 import leg, pts, add, neg

# ---- generic F_{p^k} as F_p[w]/(mod poly), elements = tuples of length k ----
def polymulmod(a,b,mod,p,k):
    r=[0]*(2*k-1)
    for i,ai in enumerate(a):
        if ai:
            for j,bj in enumerate(b):
                if bj: r[i+j]=(r[i+j]+ai*bj)%p
    for i in range(2*k-2,k-1,-1):
        c=r[i]
        if c:
            r[i]=0
            for j in range(k): r[i-k+j]=(r[i-k+j]-c*mod[j])%p
    return tuple(r[:k])
def powmodk(a,e,mod,p,k):
    R=tuple([1]+[0]*(k-1))
    while e:
        if e&1: R=polymulmod(R,a,mod,p,k)
        a=polymulmod(a,a,mod,p,k); e>>=1
    return R
def irreducible_mod(p,k,A,B):
    """return coeff list c0..c_{k-1} of monic irreducible w^k = -(c0+c1 w+...)"""
    if k==1: return []
    if k==3: return [B,A,0]                      # w^3 + A w + B  (irreducible iff n odd)
    if k==2:
        r=next(u for u in range(2,p) if leg(u,p)==-1)
        return [(-r)%p,0]                        # w^2 = r
    raise ValueError

def run(p,A,B):
    E=pts(p,A,B); n=len(E)+1
    if n%2==0: return
    def half(R):
        m=(n+1)//2; T=None; b=R
        while m:
            if m&1: T=add(T,b,p,A)
            b=add(b,b,p,A); m>>=1
        return T
    R=E[0]; xR=R[0]
    fc=[ (A*A-4*B*xR)%p, (-(8*B+4*A*xR))%p, (-2*A)%p, (-4*xR)%p, 1 ]   # f = (c^3+Ac+B)*qR : build below
    # f(c) = (c^3+Ac+B) * qR(c);  qR coeffs above (deg 4, monic)
    cub=[B%p, A%p, 0, 1]
    f=[0]*(len(cub)+len(fc)-1)
    for i,u in enumerate(cub):
        for j,v in enumerate(fc): f[i+j]=(f[i+j]+u*v)%p
    out=[]
    for k in (1,2,3):
        mod=irreducible_mod(p,k,A,B); q=p**k; e=(q-1)//2
        tot=0
        # enumerate F_{p^k}
        def elts(k):
            if k==1:
                for a0 in range(p): yield (a0,)
            elif k==2:
                for a0 in range(p):
                    for a1 in range(p): yield (a0,a1)
            else:
                for a0 in range(p):
                    for a1 in range(p):
                        for a2 in range(p): yield (a0,a1,a2)
        one=tuple([1]+[0]*(k-1))
        for c in elts(k):
            # evaluate f at c by Horner in F_{p^k}
            val=tuple([0]*k)
            for coef in reversed(f):
                val=polymulmod(val,c,mod,p,k)
                val=((val[0]+coef)%p,)+val[1:]
            if all(x==0 for x in val): continue
            tot += 1 if powmodk(val,e,mod,p,k)==one else -1
        out.append(tot)
    print(f"p={p:3d} A={A} B={B} n={n:3d} R={R}   "
          f"sum over F_p={out[0]:5d}   F_p^2={out[1]:6d}   F_p^3={out[2]:7d}   "
          f"| k=1,2 vanish: {out[0]==0 and out[1]==0}   k=3 nonzero: {out[2]!=0}", flush=True)

for (p,A,B) in [(11,0,4),(13,0,1),(17,1,5),(19,0,3),(19,3,1),(23,1,4)]: run(p,A,B)
