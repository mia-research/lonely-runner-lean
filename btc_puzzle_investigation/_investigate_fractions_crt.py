import csv
from math import gcd
from fractions import Fraction

def best_nk(v, b, NMAX=256):
    """best simple fraction k/n of position u=(v-A)/A, v in [A,2A), n<=NMAX."""
    A=1<<(b-1); num=v-A; best=None
    for n in range(1,NMAX+1):
        k=(2*n*num+A)//(2*A); k=0 if k<0 else (n if k>n else k)
        for kk in (k-1,k,k+1):
            if 0<=kk<=n:
                key=(abs(n*num-kk*A),n,kk)
                if best is None or key<best: best=key
    _,n,k=best; g=gcd(k,n) if n else 1
    return (n//g,k//g) if g>1 else (n,k)

def crt_check(k,n):
    if n%2==0: return None
    Mx=(n-1)//2; My=(n+1)//2
    if Mx==0 or gcd(Mx,My)!=1: return None
    ax=k%Mx; ay=k%My
    # reconstruct
    g,u,v=ext(Mx,My)
    kk=(ax*v*My+ay*u*Mx)%(Mx*My)
    return Mx,My,ax,ay,kk,(kk==k%(Mx*My))
def ext(a,b):
    if b==0: return a,1,0
    g,x,y=ext(b,a%b); return g,y,x-(a//b)*y

rows=sorted([(int(r["bits"]),int(r["private_key"],16),int(r["X"],16),int(r["Y"],16),r["puzzle"])
             for r in csv.DictReader(open("puzzles_verified.csv"))])

print("SIMPLE FRACTIONS of the position (offset within band), all keys:")
print(f"{'pz':>3} {'P':>3} {'k/n':>10} {'n odd?':>6}  {'CRT: Mx,My':>12} {'ax,ay':>10} {'recon k?':>8}")
from collections import Counter
fracs=Counter()
for P,d,X,Y,pz in rows:
    if P<3: continue
    n,k=best_nk(d,P)
    fracs[(k,n)]+=1
    cr=crt_check(k,n)
    if cr:
        Mx,My,ax,ay,kk,ok=cr
        print(f"{pz:>3} {P:>3} {f'{k}/{n}':>10} {'odd' if n%2 else 'EVEN':>6}  {f'{Mx},{My}':>12} {f'{ax},{ay}':>10} {str(ok):>8}")
    else:
        print(f"{pz:>3} {P:>3} {f'{k}/{n}':>10} {'EVEN' if n%2==0 else 'n<3':>6}  {'--':>12}")

print(f"\nMOST COMMON fractions across all keys: {fracs.most_common(10)}")
