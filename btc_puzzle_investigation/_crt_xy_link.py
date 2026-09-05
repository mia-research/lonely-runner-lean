import csv
from math import gcd
def best_nk(v,b,NMAX=256):
    A=1<<(b-1); num=v-A; best=None
    for n in range(1,NMAX+1):
        k=(2*n*num+A)//(2*A); k=0 if k<0 else (n if k>n else k)
        for kk in (k-1,k,k+1):
            if 0<=kk<=n:
                key=(abs(n*num-kk*A),n,kk)
                if best is None or key<best: best=key
    _,n,k=best; g=gcd(k,n) if n else 1
    return (n//g,k//g) if g>1 else (n,k)
rows=sorted([(int(r["bits"]),int(r["private_key"],16),int(r["X"],16),int(r["Y"],16),r["puzzle"])
             for r in csv.DictReader(open("puzzles_verified.csv"))])
# Does a_X = k mod M_X come from the PUBLIC X?  test several derivations.
print("Testing whether public (X,Y) reproduce the CRT residues (a_X,a_Y) of the fraction k:")
print(f"{'pz':>3} {'P':>3} {'k/n':>9} {'aX,aY':>8} | {'X%Mx':>6} {'Y%My':>6} {'X%n':>5} {'Y%n':>5}  match?")
hits={'X%Mx':0,'Y%My':0,'X%n=k':0,'Y%n=k':0}; tot=0
for P,d,X,Y,pz in rows:
    if P<8: continue
    n,k=best_nk(d,P)
    if n%2==0 or n<3: continue
    Mx=(n-1)//2; My=(n+1)//2
    ax=k%Mx; ay=k%My
    xMx=X%Mx; yMy=Y%My; xn=X%n; yn=Y%n
    tot+=1
    hits['X%Mx']+= (xMx==ax); hits['Y%My']+=(yMy==ay)
    hits['X%n=k']+=(xn==k);  hits['Y%n=k']+=(yn==k)
    m=[]
    if xMx==ax: m.append("X%Mx=aX")
    if yMy==ay: m.append("Y%My=aY")
    if xn==k: m.append("X%n=k")
    if yn==k: m.append("Y%n=k")
    print(f"{pz:>3} {P:>3} {f'{k}/{n}':>9} {f'{ax},{ay}':>8} | {xMx:>6} {yMy:>6} {xn:>5} {yn:>5}  {' '.join(m)}")
print(f"\nmatches over {tot} odd-n keys: {hits}")
print("(random expectation for X%Mx==aX is ~1/Mx per key, tiny)")
