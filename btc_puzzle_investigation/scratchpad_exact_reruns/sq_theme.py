import math
from math import isqrt
import cmath

print("="*70)
print("ITEM 2 — Sym^3(H^1_new) perfect square, forced by the verified eigenvalues")
print("="*70)
p = 43
# class-B new part N_a = T^4 + p T^2 + p^2  (verified in ANALYSIS_L3; roots sqrt(p)*{6th roots})
# roots:
import numpy as np
roots = np.roots([1,0,p,0,p*p])
# classify each root by sign of Re(r^3): r^3 = p^1.5 * u^3, u^3 = +1 (zeta3-type) or -1 (zeta6-type)
cls = []
for r in roots:
    r3 = (r**3).real
    cls.append('+' if r3 > 0 else '-')   # '+' => u^3=+1 (zeta3 type), '-' => u^3=-1 (zeta6 type)
print("N_a roots (|r|=sqrt(p)=%.4f):"%math.sqrt(p))
for r,c in zip(roots,cls):
    print("   %+.4f %+.4fi   u^3=%s"%(r.real, r.imag, c))
nz3 = cls.count('+'); nz6 = cls.count('-')
print("  zeta3-type (u^3=+1):",nz3,"  zeta6-type (u^3=-1):",nz6)

# Sym^3 eigenvalues = products of 3 roots with repetition (20 of them). Frob^3: cube each.
from itertools import combinations_with_replacement
idx=list(range(4))
frob3=[]; kclass={0:0,1:0,2:0,3:0}
for (i,j,k) in combinations_with_replacement(idx,3):
    s = roots[i]*roots[j]*roots[k]          # Sym^3 eigenvalue (Frob), |s|=p^1.5
    f3 = s**3                                # Frob^3 eigenvalue = base-change to F_{p^3}
    frob3.append(f3)
    kk = sum(1 for t in (i,j,k) if cls[t]=='-')  # number of zeta6-type factors
    kclass[kk]+=1
print("\nSym^3 dim =",len(frob3),"(expect 20)")
print("collapse classes by #zeta6-factors k:",kclass,"  (claim: 4,6,6,4)")
val = p**4 * math.sqrt(p)   # p^{9/2}
plus  = sum(1 for f in frob3 if f.real >  val/2 and abs(f.imag)<1e-3)
minus = sum(1 for f in frob3 if f.real < -val/2 and abs(f.imag)<1e-3)
maximag = max(abs(f.imag) for f in frob3)
print("Frob^3 eigenvalues: +p^{9/2} count = %d, -p^{9/2} count = %d, max|Im| = %.2e"%(plus,minus,maximag))
print("=> char poly of Frob^3 on Sym^3 = (T^2 - p^9)^%d = [ (T^2-p^9)^%d ]^2  -> PERFECT SQUARE: %s"
      %(plus, plus//2, plus==10 and minus==10))

print()
print("="*70)
print("ITEM 3 (deg-5, C2) — recompute disc(Q5) EXACTLY, no float")
print("="*70)
# Q5 from ADDENDUM_4 C2:
import sympy as sp
T=sp.symbols('T')
Q5 = T**5 + 155*T**4 + 6138*T**3 + 92070*T**2 + 555861*T + 1060975
D5 = sp.discriminant(Q5, T)
r = isqrt(int(D5))
print("disc(Q5) =", D5)
print("claimed  = 56858430668800^2 =", 56858430668800**2)
print("match:", int(D5)==56858430668800**2, " | exact isqrt^2==disc (perfect square):", r*r==int(D5), " isqrt=",r)

print()
print("="*70)
print("ITEM 3 (deg-23) — WHY the float '0.0 distance' certification is INVALID at 379 digits")
print("="*70)
# a genuine perfect square vs a near-miss non-square, both ~379 digits:
base = 28894*10**375 + 7   # ~379-digit odd integer
sq   = base*base           # a true perfect square
non  = sq + 1              # definitely NOT a perfect square (consecutive to a square)
for name,x in [("true square", sq), ("square+1 (non-square)", non)]:
    fs = math.sqrt(x)          # float sqrt
    frac = fs - round(fs)      # 'distance to nearest integer' as the external check computes it
    exact_ok = isqrt(x)**2 == x
    print("%-24s float 'dist to int' = %.6f  | exact isqrt certifies square: %s"%(name, frac, exact_ok))
print("=> float 'distance 0.0' cannot distinguish a perfect square from square+1 at this scale;")
print("   only exact isqrt(disc)**2==disc is a valid certification (no-float rule).")
