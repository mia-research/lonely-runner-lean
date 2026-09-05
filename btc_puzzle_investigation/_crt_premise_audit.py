import csv
from math import gcd
def best_nk(v,b,NMAX=256):
    A=1<<(b-1); num=v-A; best=None
    for n in range(1,NMAX+1):
        kk=(2*n*num+A)//(2*A); kk=0 if kk<0 else (n if kk>n else kk)
        for c in (kk-1,kk,kk+1):
            if 0<=c<=n:
                key=(abs(n*num-c*A),n,c)
                if best is None or key<best: best=key
    _,n,k=best; g=gcd(k,n) if n else 1
    return (n//g,k//g) if g>1 else (n,k)

rows=[(int(r["bits"]),int(r["private_key"],16),int(r["X"],16),int(r["Y"],16))
      for r in csv.DictReader(open("puzzles_verified.csv")) if int(r["bits"])>=20]

# --- moduli size: how much can CRT even pin? ---
print("[moduli] M_X=(n-1)//2, M_Y=(n+1)//2  (n = fraction denominator <=256):")
for n in (80,135,255):
    MX,MY=(n-1)//2,(n+1)//2
    prod=MX*MY
    print(f"  n={n:>3}: M_X={MX} M_Y={MY} gcd={gcd(MX,MY)} product={prod} (~{prod.bit_length()} bits pinned of ~{n} needed)")

# --- THE PREMISE: does 'a_X derived from X' as a_X = X mod M_X satisfy k ≡ a_X (mod M_X)? ---
print("\n[premise test] does  (private_key mod M_X) == (X mod M_X) ?  (and Y version)")
hitX=hitY=0; both=0; expX=0.0; tot=0
for P,d,X,Y in rows:
    n,k=best_nk(d,P)
    MX,MY=(n-1)//2,(n+1)//2
    if MX<2 or MY<2 or gcd(MX,MY)!=1: continue
    tot+=1
    okX = (d % MX)==(X % MX)
    okY = (d % MY)==(Y % MY)
    hitX+=okX; hitY+=okY; both+=(okX and okY)
    expX += 1.0/MX
print(f"  keys tested: {tot}")
print(f"  k≡X (mod M_X): {hitX}/{tot} match   (expected by chance ≈ {expX:.2f})")
print(f"  k≡Y (mod M_Y): {hitY}/{tot} match")
print(f"  BOTH satisfied simultaneously: {both}/{tot}")

# --- also try a_X = X mod M_X with n even 'special handling', and Y-parity variants ---
print("\n[variants] other plausible 'derivations' of a_X from X, match-rate vs k mod M_X:")
import random; rnd=random.Random(0)
def rate(fn):
    h=t=0
    for P,d,X,Y in rows:
        n,k=best_nk(d,P); MX=(n-1)//2
        if MX<2: continue
        t+=1; h+= (d%MX)==(fn(X,Y,MX)%MX)
    return h,t
for name,fn in [("X",lambda X,Y,M:X),("X+Y",lambda X,Y,M:X+Y),("X*Y",lambda X,Y,M:X*Y),
                ("X-Y",lambda X,Y,M:X-Y),("random",lambda X,Y,M:rnd.randrange(M))]:
    h,t=rate(fn); print(f"  a_X={name:>6}: {h}/{t}")

# --- D-recursion with range=2^(P-1): reconstructs? term counts (claim: 3-6) ---
def d_recursion(target,base,R,mx=20):
    cur=base; cs=[]
    for _ in range(mx):
        e=target-cur
        if e==0: break
        D=abs(R//e)
        if D==0: break
        cur+= (1 if e>0 else -1)*(R//D); cs.append(D)
    return cs,cur==target
print("\n[D-recursion range=2^(P-1)] reconstruct + term counts (claim 3-6):")
oks=0; from collections import Counter; tc=Counter()
for P,d,X,Y in rows:
    n,k=best_nk(d,P); A=1<<(P-1); base=A+(A*k)//n
    cs,ok=d_recursion(d,base,A); oks+=ok; tc[len(cs)]+=1
print(f"  reconstructs {oks}/{len(rows)}; term-count dist {dict(sorted(tc.items()))}")
