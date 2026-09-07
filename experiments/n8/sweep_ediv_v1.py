"""Does SAFE (as defined, E_non only) actually deliver a witness k?
Derivation being tested: with k = L*r + b (a bijection {0..n-1}x{0..L-1} -> {0..N-1}),
 e*k mod N = L*(((e*r)+t_e) mod n) + u_e,  t_e=floor(eb/L), u_e = eb mod L.
So for e in E_non the obstruction is exactly bad(e,t_e,n); for e in E_div (n|e) the
condition is r-INDEPENDENT and constrains b alone -- and B_div encodes only e=n.
Sweep E_div = {8*m1, 8*m2} to see how often the window contains NO usable b."""
from math import gcd, lcm
from fractions import Fraction as F
n = 8
def Sol(e,j,m): return frozenset(r for r in range(m) if (e*r-j)%m==0)
def bad(e,t,m): return Sol(e,(-t)%m,m)|Sol(e,(-(t+1))%m,m)

# 0) verify the parametrisation identity on a real tuple, exactly
E0=[1,3,5,7,2,8,24]; L0=1
for e in E0: L0=lcm(L0,e)
N0=n*L0
okid=True
for r in range(n):
    for b in range(0,L0, 7):
        k=L0*r+b
        for e in E0:
            t=(e*b)//L0; u=(e*b)%L0
            if (e*k)%N0 != (L0*(((e*r)+t)%n)+u)%N0: okid=False
print("[identity] e*k mod N == L*(((e*r)+t_e) mod n) + u_e  for k=L*r+b :", okid)

rows=[]
worst=[]
for rho in (2,4,6):
    for m1 in range(1,25):
        for m2 in range(m1+1,25):
            E=[1,3,5,7,rho,8*m1,8*m2]
            if len(set(E))!=7: continue
            L=1
            for e in E: L=lcm(L,e)
            if L%n or L<=2*n: continue
            a,bE=F(3*L,5),F(5*L,7)
            bs=[x for x in range(int(a),int(bE)+2) if a<=x<bE]
            nsafe=0; nwit=0
            for b in bs:
                U=set()
                for e in (1,3,5,7,rho):
                    U|=bad(e,(e*b)//L,n)
                if U!=set(range(n)): nsafe+=1
                if all(L <= (e*b)%(n*L) <= (n-1)*L for e in (8*m1,8*m2)): nwit+=1
            rows.append((rho,m1,m2,L,len(bs),nsafe,nwit))
            if nwit==0 or nsafe!=len(bs): worst.append((rho,m1,m2,L,len(bs),nsafe,nwit))

print(f"\nswept {len(rows)} admissible tuples (rho in 2,4,6 ; E_div={{8m1,8m2}}, m<=24)")
print(" SAFE holds for EVERY b in the window in all of them:",
      all(r[5]==r[4] for r in rows))
print(" tuples where the window contains NO b passing the E_div runners:",
      sum(1 for r in rows if r[6]==0))
mn=min(rows,key=lambda r:r[6]/r[4])
print(f" tightest usable-b fraction: rho={mn[0]} E_div={{{8*mn[1]},{8*mn[2]}}} L={mn[3]}"
      f"  window has {mn[4]} integers, {mn[6]} of them usable ({mn[6]}/{mn[4]})")
lo=sorted(rows,key=lambda r:r[6])[:8]
print("\n smallest usable-b counts:")
for r in lo:
    print(f"   rho={r[0]} E_div={{{8*r[1]},{8*r[2]}}} L={r[3]}: window integers={r[4]}, SAFE={r[5]}, usable={r[6]}")
