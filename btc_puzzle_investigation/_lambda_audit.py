import math, csv
from math import gcd, log

# ---- 7. Curve prime: is it really secp256k1's p? ----
p_claim = 2**256 - 2**32 - 2**9 - 2**8 - 2**7 - 2**6 - 2**4 - 1
p_secp  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
print(f"[7] p matches secp256k1: {p_claim==p_secp}  (tail = -{2**32+2**9+2**8+2**7+2**6+2**4+1} = -(2^32+977))")

# ---- 4. CRT moduli: literal labels vs intended ----
print("\n[4] CRT moduli coprimality check:")
for n in (5, 8, 13, 127):
    lit = gcd(2**(n-1), 2**(n+1))            # literal: 2^{n-1}, 2^{n+1}
    fix = gcd(2**n - 1, 2**n + 1)            # intended: 2^n - 1, 2^n + 1
    print(f"  n={n:>3}: gcd(2^(n-1),2^(n+1))={lit}  (NOT 1) | gcd(2^n-1,2^n+1)={fix}  (=1)")
print("  => literal labels violate 'Require gcd=1'; intent is Mersenne/Fermat 2^n-1, 2^n+1")

# ---- 1. Thermodynamic ranking on real keys' (n,k) ----
def mult_order(k,n):
    if n<=1 or gcd(k,n)!=1: return None
    o,x=1,k%n
    while x!=1: x=(x*k)%n; o+=1
    return o
def T_EC(k,n,a=0.7,b=0.3):
    o=mult_order(k,n)
    return None if o is None else a*log(o)+b*(k/n)
print("\n[1] Thermodynamic ranking T_EC = 0.7*ln(ord_n(k)) + 0.3*(k/n):")
for (k,n) in [(1,2),(2,3),(5,8),(64,127),(3,7)]:
    o=mult_order(k,n); print(f"  (k={k},n={n}): ord={o}  T_EC={T_EC(k,n):.3f}" if o else f"  (k={k},n={n}): ord undefined (gcd!=1)")

# ---- 2+3. base_key + D-recursion (k-update form) reconstruct a real key? ----
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
def reconstruct(P, target, range_size):
    A=1<<(P-1); n,k=best_nk(target,P); base=A+(A*k)//n
    cur=base; e=target-cur; sig=[]
    while e!=0 and len(sig)<80:
        D=range_size//abs(e)
        if D==0: break
        corr=range_size//D; s=1 if e>0 else -1
        cur=cur+s*corr; sig.append((D,s)); e=target-cur
    return cur==target, sig, (n,k)
print("\n[2+3] base_key + D-recursion (k-update) reconstruction on real keys:")
rows=sorted([(int(r["bits"]),int(r["private_key"],16),r["puzzle"]) for r in csv.DictReader(open("puzzles_verified.csv"))])
for rs_name,rs in (("range=2^P",None),("range=2^(P-1)",None)):
    ok=0
    for P,d,pz in rows:
        R=(1<<P) if rs_name=="range=2^P" else (1<<(P-1))
        good,sig,nk=reconstruct(P,d,R)
        ok+=good
    print(f"  {rs_name}: reconstructs {ok}/{len(rows)} real keys")

# ---- 6. Gauss-Wantzel: which n have phi(n)=2^r ----
def phi(m):
    r=m; x=m; pp=2; ps=set()
    while pp*pp<=x:
        if x%pp==0:
            ps.add(pp)
            while x%pp==0: x//=pp
        pp+=1
    if x>1: ps.add(x)
    for q in ps: r-=r//q
    return r
gw=[n for n in range(2,60) if (phi(n)&(phi(n)-1))==0]
print(f"\n[6] Gauss-Wantzel n (phi(n)=2^r, n<60): {gw}")
print(f"     (= products of Fermat primes 3,5,17,257,65537 times 2^k = constructible n)")

# ---- 5. CRT reconstruction demo (corrected moduli) ----
def crt(aX,aY,MX,MY):
    # u*MX+v*MY=1
    def egcd(a,b):
        if b==0: return (a,1,0)
        g,x,y=egcd(b,a%b); return (g,y,x-(a//b)*y)
    g,u,v=egcd(MX,MY)
    return (aX*v*MY + aY*u*MX) % (MX*MY)
n=13; MX,MY=2**n-1,2**n+1; secret=1234567 % (MX*MY)
aX,aY=secret%MX, secret%MY
rec=crt(aX,aY,MX,MY)
print(f"\n[5] CRT reconstruct (n=13, MX=2^13-1, MY=2^13+1): secret={secret} rec={rec} match={rec==secret}")
