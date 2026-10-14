# The memo's a(P), b(P) comparison, checked exactly, then identified.
#   a(P) = log((8P+1)/(8P-1))   max move charge from a setter at lap P
#   b(P) = log((8P+7)/(8P+1))   growth required before that runner may return
import math
from fractions import Fraction as F
print("[1] b(P) > a(P) for P >= 1?   cross-multiplying: (8P+7)(8P-1) > (8P+1)^2  <=>  32P > 8  <=> P > 1/4")
for P in (1,2,3,5,10,100):
    a=math.log((8*P+1)/(8*P-1)); b=math.log((8*P+7)/(8*P+1))
    print(f"   P={P:4d}: a={a:.6f}  b={b:.6f}  b>a {b>a}   ratio a/b = {a/b:.6f}")
print()
print("[2] is a(P)/b(P) MONOTONE, with the worst case at P=1?  (the memo flags this as unchecked)")
rs=[(P, math.log((8*P+1)/(8*P-1))/math.log((8*P+7)/(8*P+1))) for P in range(1,4001)]
mono=all(rs[i][1] >= rs[i+1][1] for i in range(len(rs)-1))
print(f"   decreasing over P=1..4000 : {mono}")
print(f"   rho(1) = {rs[0][1]:.6f}   rho(10) = {rs[9][1]:.6f}   rho(4000) = {rs[-1][1]:.6f}   limit 1/3 = {1/3:.6f}")
print(f"   so c_* = sup rho = rho(1) = log(9/7)/log(5/3) = {math.log(9/7)/math.log(5/3):.6f}")
print()
print("[3] IDENTIFICATION.  With s = 8P (the reading), expand for large P:")
for P in (10,100,1000):
    a=math.log((8*P+1)/(8*P-1)); b=math.log((8*P+7)/(8*P+1)); s=8*P
    print(f"   P={P:5d}: a={a:.8f} vs 2/s={2/s:.8f}   b={b:.8f} vs 6/s={6/s:.8f}")
print("   => a(P) ~ 2/s and b(P) ~ 6/s.  These ARE inequalities (i) and (iii) of LONG_RETURN_CIRCLE_v1.")
print()
print("[4] THE COEFFICIENT.  Each runner's return intervals are DISJOINT and tile the run, so")
print("    sum_i b(P_i^x) <= L_N for each x, and over 7 runners sum_x sum_i b <= 7 L_N -- and that")
print("    is TIGHT when all seven set throughout.  Then S_N <= A + 7*c_* L_N.")
for c,lab in ((math.log(9/7)/math.log(5/3),"c_* at P=1"), (1/3,"c_* asymptotic")):
    print(f"    {lab:18s} c_*={c:.4f}  ->  7*c_* = {7*c:.4f}   {'CLOSES' if 7*c<1 else 'FAILS (needs < 1)'}")
print(f"    multiplicity needed for closure at c_*={math.log(9/7)/math.log(5/3):.4f}: mu < {1/(math.log(9/7)/math.log(5/3)):.3f}")
