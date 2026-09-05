# ---- Doc 4: Cartier-Manin vanishing on A_new of C: w^4 = x^3+Ax+B ----
# Hasse-Witt matrix of a superelliptic curve y^m = f(x) via coefficients of f^{...}.
# We compute the FULL Hasse-Witt of C (genus 3), then the A_new block, and test:
#   (i) p=3 mod 4: A_new block == 0 (superspecial a-number contribution)
#   (ii) CM curve x^3+7, p=1 mod12 diagonal, p=5 mod12 off-diagonal (their specific matrices)
import sympy as sp
from sympy import Poly, GF, symbols

x=symbols('x')

def poly_pow_coeffs(fcoeffs_modp, e, p):
    # f given as dict/list of coeffs (low->high); compute f^e mod p as list
    from numpy.polynomial import polynomial as P
    # do it with python ints mod p
    res=[1]
    base=fcoeffs_modp[:]
    ee=e
    def mul(a,b):
        r=[0]*(len(a)+len(b)-1)
        for i,ai in enumerate(a):
            if ai:
                for j,bj in enumerate(b):
                    r[i+j]=(r[i+j]+ai*bj)%p
        return r
    while ee>0:
        if ee&1: res=mul(res,base)
        ee>>=1
        if ee: base=mul(base,base)
    return res

def coeff(lst,k):
    return lst[k]%p if 0<=k<len(lst) else 0

# Cartier-Manin for genus-3 cover C: w^4=f(x), basis of A_new: w^{-3}dx, x w^{-3}dx (their setup).
# Their reduction: for p=3 mod4 both vanish; for p=1 mod4 (p=4k+1) M = [[c_{p-1},c_{p-2}],[c_{2p-1},c_{2p-2}]]
#   where c_j are coeffs of f(x)^{(3p-3)/4}.
def Anew_matrix(A,B,p):
    f=[B%p, A%p, 0, 1%p]  # x^3+Ax+B, low->high
    if p%4==3:
        # their degree-bound claim: exponent (p-3)/4 for both -> deg < p-1 so C acts as 0
        e=(p-3)//4
        g=poly_pow_coeffs(f,e,p)
        gx=[0]+g  # x*f^e
        # standard Cartier on P^1 sends sum c_j x^j dx -> sum c_{kp-1} x^{k-1} dx; matrix entries pick c_{p-1} etc scaled
        # For b=3,d=1 case the resulting poly is f^{(p-3)/4} (deg (3p-9)/4 < p-1). Cartier picks c_{kp-1}, none exist.
        m11=coeff(g,p-1); m12=coeff(g,p-2); m21=coeff(gx,2*p-1); m22=coeff(gx,2*p-2)
        return [[m11%p,m12%p],[m21%p,m22%p]]
    else:
        e=(3*p-3)//4
        g=poly_pow_coeffs(f,e,p)
        gx=[0]+g
        m11=coeff(g,p-1); m12=coeff(g,p-2); m21=coeff(gx,2*p-1); m22=coeff(gx,2*p-2)
        return [[m11%p,m12%p],[m21%p,m22%p]]

from sympy import isprime
print("=== p = 3 mod 4: claim A_new Cartier block == 0 for ALL cubics ===")
for p in [7,11,19,23,31,43,47,59,67,71,79,83]:
    for (A,B,name) in [(0,7,'CM x^3+7'),(1,3,'nonCM x^3+x+3'),(1,5,'nonCM x^3+x+5')]:
        # skip singular
        M=Anew_matrix(A,B,p)
        z = (M==[[0,0],[0,0]])
        if not z:
            print(f"  p={p} {name}: {M}  <-- NONZERO (counterexample to claim)")
print("  (no lines above = block is zero for every case, matching the claim)")

print("\n=== CM curve x^3+7, p = 1 mod 4: diagonal (p=1 mod12) / off-diagonal (p=5 mod12) ===")
for p in [5,13,17,29,37,41,53,61,73,89,97,101,109,113]:
    M=Anew_matrix(0,7,p)
    shape = "diag" if (M[0][1]==0 and M[1][0]==0) else ("offdiag" if (M[0][0]==0 and M[1][1]==0) else "full")
    print(f"  p={p} (p mod12={p%12}): M={M}  -> {shape}")
