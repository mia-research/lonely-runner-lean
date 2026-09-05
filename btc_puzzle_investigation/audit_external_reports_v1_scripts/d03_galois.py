import sympy as sp
from sympy import legendre_symbol, Poly, symbols, Rational, sqrt, discriminant, factorint
import cmath, math

p=43; A=0; Bc=7
# EC over F_43: y^2 = x^3+7
def pts():
    L=[]
    for x in range(p):
        r=(x**3+Bc)%p
        for y in range(p):
            if (y*y)%p==r: L.append((x,y))
    L.append(None)
    return L
def add(P,Q):
    if P is None: return Q
    if Q is None: return P
    x1,y1=P; x2,y2=Q
    if x1==x2 and (y1+y2)%p==0: return None
    if P==Q:
        m=(3*x1*x1+A)*pow(2*y1,-1,p)%p
    else:
        m=(y2-y1)*pow((x2-x1)%p,-1,p)%p
    x3=(m*m-x1-x2)%p; y3=(m*(x1-x3)-y1)%p
    return (x3,y3)
P=pts()
order=len(P)
print("cardinality |E(F_43)| =", order)
# find generator of prime-order group
G=None
for Q in P:
    if Q is None: continue
    # order of Q
    R=Q; k=1
    while R is not None:
        R=add(R,Q); k+=1
    if k==31:
        G=Q; break
print("generator G=",G,"order 31")
# orbit d=1..30
orb={}
R=None
for d in range(1,31):
    R=add(R,G)
    orb[d]=R
# y_d and chi2(y_d)=legendre(y_d,43). y=0 -> chi=0 (none here since order prime)
n=31
def chi2(v):
    v%=p
    if v==0: return 0
    return legendre_symbol(v,p)
chis={d:int(chi2(orb[d][1])) for d in range(1,31)}

# V(a) = sum_{d=1}^{30} chi2(y_d) * exp(2pi i a d / n)
import numpy as np
def V(a):
    s=0j
    for d in range(1,31):
        s+= chis[d]*cmath.exp(2j*math.pi*a*d/n)
    return s
remax=max(abs(V(a).real) for a in range(1,31))
print("max |Re V(a)| over a=1..30:", remax, " (doc: purely imaginary)")
# W(a)=V(a)^2 real & negative
W=[ (V(a)**2).real for a in range(1,31)]
Wi=[ (V(a)**2).imag for a in range(1,31)]
print("max |Im W(a)|:", max(abs(w) for w in Wi))
# unique roots (rounded)
uniq=sorted(set(round(w,6) for w in W))
print("num distinct W-values (rounded):", len(uniq))
from collections import Counter
cnt=Counter(round(w,6) for w in W)
print("multiplicities:", sorted(cnt.values()))
print("the 5 roots:", uniq)

# Build Q5 from the 5 unique roots and compare to doc's polynomial
T=symbols('T')
roots5=uniq
Q5=sp.prod([T-Rational(str(r)) for r in roots5])
Q5e=sp.expand(Q5)
print("\nQ5 (numeric roots, expanded):", Q5e)
doc_Q5 = T**5+155*T**4+6138*T**3+92070*T**2+555861*T+1060975
print("doc Q5:", sp.expand(doc_Q5))
# roots of doc_Q5 numerically to compare
dr=sp.nroots(doc_Q5)
print("doc Q5 roots:", [complex(x) for x in dr])
print("our W roots :", roots5)
# discriminant perfect square?
disc=sp.discriminant(doc_Q5,T)
print("\ndisc(doc Q5) =", disc, " isqrt^2==disc?", sp.sqrt(disc)==sp.Integer(int(sp.sqrt(disc))) if disc>0 else "neg")
print("sqrt(disc)=", sp.sqrt(disc))
# Galois: is doc_Q5 irreducible over Q, and cyclic?
print("doc Q5 irreducible over Q?", sp.Poly(doc_Q5,T).is_irreducible)
