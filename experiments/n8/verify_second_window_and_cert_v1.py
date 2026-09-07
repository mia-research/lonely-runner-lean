from math import lcm, gcd
from fractions import Fraction as F
n=8
def Sol(e,j,m): return frozenset(r for r in range(m) if (e*r-j)%m==0)
def bad(e,t,m): return Sol(e,(-t)%m,m)|Sol(e,(-(t+1))%m,m)

print("=== second window x in [2/7, 2/5), exact ===")
for e in (1,3,5,7,2,4,6):
    a,b=e*F(2,7), e*F(2,5)
    fa=a.numerator//a.denominator
    fb=b.numerator//b.denominator - (1 if b.denominator==1 else 0)
    print(f"  e={e}: [{a},{b})  floor const? {fa==fb}  t={fa if fa==fb else (fa,fb)}")
U=set()
for e,t in ((1,0),(5,1),(7,2)): U|=bad(e,t,n)
print("  units 1,5,7 (t const):", sorted(U))
for t3 in (0,1):
    UU=U|bad(3,t3,n); print(f"   with t_3={t3}: union={sorted(UU)} uncovered={sorted(set(range(8))-UU)}")
print("  non-unit at its constant floor:",
      {rho:(f"t={ (rho*F(2,7)).numerator//(rho*F(2,7)).denominator }",
            sorted(bad(rho,(rho*F(2,7)).numerator//(rho*F(2,7)).denominator,n))) for rho in (2,4,6)})
print("  window length = 2/5-2/7 = 4/35 (same as the first); L>=24 => >=2 integers")

print("\n=== non-unit floor is CONSTANT on window 1 too, so the survivor is explicit ===")
for rho in (2,4,6):
    a,b=rho*F(3,5), rho*F(5,7)
    fa=a.numerator//a.denominator; fb=b.numerator//b.denominator-(1 if b.denominator==1 else 0)
    B=sorted(bad(rho,fa,n))
    print(f"  rho={rho}: t={fa} (const: {fa==fb}) bad={B} -> uncovered after rho = {sorted({3,6}-set(B))}")

print("\n=== explicit certificate, E = {1,2,3,5,7,8,16} ===")
E=[1,2,3,5,7,8,16]; L=1
for e in E: L=lcm(L,e)
N=n*L
print(f"  L={L}  N={N}  window=[{F(3*L,5)},{F(5*L,7)}) = [{int(F(3*L,5))},{int(F(5*L,7))})")
found=None
for b in range(int(F(3*L,5)), int(F(5*L,7))):
    if F(3*L,5) <= b:
        for r in range(n):
            k=L*r+b
            if 1<=k<N and all(L <= (e*k)%N <= (n-1)*L for e in E):
                found=(b,r,k); break
    if found: break
b,r,k=found
print(f"  first window fibre b={b}, residue r={r}, witness k = L*r+b = {k}")
print(f"  t_e for e in E_non: " + ", ".join(f"t_{e}={(e*b)//L}" for e in (1,3,5,7,2)))
print(f"  positions (e*k mod N)/L, must lie in [1,7]:")
for e in E:
    v=(e*k)%N; print(f"     e={e:>3}: {v:>6} = {F(v,L)} L   in[1,7]: {L<=v<=(n-1)*L}")
print("  => x_0(E) > 0 with explicit witness. gcd(E)=", gcd(gcd(gcd(1,2),3),1))
