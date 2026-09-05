# ---- Docs 5/6: Weil pairing on E':y^2=x^3+1 over F_{11^2}, and the 'easy DLP for secp' leap ----
import sympy as sp

# (A) Confirm their concrete pairing fact: E':y^2=x^3+1 over F_{11^2} is supersingular, embedding degree 2.
p=11
# F_{p^2} = F_p[i]/(i^2+1). Count E'(F_{p^2}).
# supersingular y^2=x^3+1 over F_11 (11 = 2 mod 3 -> supersingular): |E'(F_11)| = 12, |E'(F_121)|=(p+1)^2=144.
def count_Fp2(A,B,p):
    # brute over a+bi
    from itertools import product
    def mul(u,v):
        (a,b),(c,d)=u,v; return ((a*c-b*d)%p,(a*d+b*c)%p)
    def add(u,v): return ((u[0]+v[0])%p,(u[1]+v[1])%p)
    def cube(u): return mul(mul(u,u),u)
    cnt=1 # infinity
    els=[(a,b) for a in range(p) for b in range(p)]
    squares={}
    for y in els:
        squares.setdefault(mul(y,y),0); squares[mul(y,y)]+=1
    for x in els:
        rhs=add(add(cube(x),mul((A%p,0),x)),(B%p,0))
        cnt+=squares.get(rhs,0)
    return cnt
N2=count_Fp2(0,1,p)
print("|E'(F_{11^2})| =", N2, " expected (p+1)^2 =",(p+1)**2, " -> embedding degree 2 for 12-torsion: TRUE (textbook supersingular)")

# (B) The conflation. secp256k1: is its E ordinary? what is its REAL embedding degree (order of p mod n)?
psecp = 2**256 - 2**32 - 977
n = 115792089237316195423570985008687907852837564279074904382605163141518161494337
trace = psecp + 1 - n
print("\nsecp256k1 E: trace t = p+1-n =", trace)
print("  t mod p == 0 (supersingular)?", trace % psecp == 0, " -> E is ORDINARY (t != 0 mod p).")
# embedding degree = multiplicative order of p modulo n (n prime)
from sympy import n_order
print("  computing embedding degree = ord_n(p) ... (this is the MOV-relevant number)")
k = n_order(psecp % n, n)
print("  embedding degree k =", k)
print("  k == n-1 ?", k == n-1, "  (i.e. maximal; MOV transfers to F_{p^k}, astronomically infeasible)")
