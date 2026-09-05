# ---- Docs 10/11: Jacobi sum J(chi3,chi4) over F_{p^2}; claim J = -p EXACTLY; Phi12 factorization ----
import sympy as sp, cmath, math
from sympy import factorint, isprime

def jacobi_sum(p):
    q=p*p
    # build F_{p^2}=F_p[t]/(t^2 - nqr) with nqr a non-residue
    nqr=None
    for c in range(2,p):
        if pow(c,(p-1)//2,p)==p-1: nqr=c; break
    def mul(u,v):
        a,b=u;c,d=v
        return ((a*c+b*d*nqr)%p,(a*d+b*c)%p)
    els=[(a,b) for a in range(p) for b in range(p) if not(a==0 and b==0)]
    # find generator of cyclic group order q-1
    def order(u):
        r=(1,0);k=0
        while True:
            r=mul(r,u);k+=1
            if r==(1,0): return k
    g=None
    for u in els:
        if order(u)==q-1: g=u; break
    # discrete log table
    dlog={}; r=(1,0)
    for k in range(q-1):
        dlog[r]=k; r=mul(r,g)
    omega=cmath.exp(2j*math.pi/3); iu=1j
    def chi3(u): return omega**(dlog[u]%3)
    def chi4(u): return iu**(dlog[u]%4)
    # J = sum over x in F_q, x!=0,1 of chi3(x) chi4(1-x)
    one=(1,0)
    def sub(u,v): return ((u[0]-v[0])%p,(u[1]-v[1])%p)
    J=0j
    for x in els:
        if x==one: continue
        omx=sub(one,x)
        if omx==(0,0): continue
        J+=chi3(x)*chi4(omx)
    return J

for p in [43]:
    J=jacobi_sum(p)
    print(f"p={p}: J(chi3,chi4) = {J:.6f}   |J|={abs(J):.6f}  (p={p})")
    print(f"   claim J = -p = -{p}.  Re close to -p? {abs(J.real+p)<1e-6}   Im ~0? {abs(J.imag)<1e-6}")
    print(f"   |J| == p ? {abs(abs(J)-p)<1e-6}")

# Phi_12 factorization mod p (instant, exact)
from sympy import Poly, symbols, GF
x=symbols('x')
Phi12=x**4 - x**2 + 1
for p in [43,1831]:
    fl=Poly(Phi12,x,modulus=p).factor_list()
    facs=[ (sp.Poly(f,x).all_coeffs(),m) for f,m in fl[1]]
    print(f"\nPhi12 mod {p} factors:", fl[1])
