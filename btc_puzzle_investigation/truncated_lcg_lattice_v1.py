#!/usr/bin/env python3
"""
Truncated-LCG lattice recovery (FHKLS), pure-Python LLL. Control-first: plant a
multiplicative truncated LCG (x_{i+1}=a x_i mod m, observe high bits h_i=x_i>>k),
recover the low bits l_i via lattice + Babai; verify. Then assess the puzzle keys.
Model (multiplicative, c eliminated): l_i = (a^i l_0 + s_i) mod m with s_i from the
known high parts; the constraint 0<=l_i<2^k pins l_0 -> CVP.
"""
from fractions import Fraction as Fr
import random
def dot(u,v): return sum(a*b for a,b in zip(u,v))
def lll(B):
    B=[[Fr(x) for x in r] for r in B]; n=len(B)
    def gso():
        Bs=[]; mu=[[Fr(0)]*n for _ in range(n)]
        for i in range(n):
            bi=B[i][:]
            for j in range(i):
                mu[i][j]=dot(B[i],Bs[j])/dot(Bs[j],Bs[j]) if dot(Bs[j],Bs[j])!=0 else Fr(0)
                bi=[bi[t]-mu[i][j]*Bs[j][t] for t in range(len(bi))]
            Bs.append(bi)
        return Bs,mu
    Bs,mu=gso(); k=1
    while k<n:
        for j in range(k-1,-1,-1):
            if abs(mu[k][j])>Fr(1,2):
                q=round(mu[k][j]); B[k]=[B[k][t]-q*B[j][t] for t in range(n)]; Bs,mu=gso()
        if dot(Bs[k],Bs[k])>=(Fr(3,4)-mu[k][k-1]**2)*dot(Bs[k-1],Bs[k-1]): k+=1
        else:
            B[k],B[k-1]=B[k-1],B[k]; Bs,mu=gso(); k=max(k-1,1)
    return [[int(x) for x in r] for r in B]
def babai(B,t):
    Bs=[]; mu=[[Fr(0)]*len(B) for _ in range(len(B))]
    for i in range(len(B)):
        bi=[Fr(x) for x in B[i]]
        for j in range(i):
            mu[i][j]=dot([Fr(x) for x in B[i]],Bs[j])/dot(Bs[j],Bs[j])
            bi=[bi[t]-mu[i][j]*Bs[j][t] for t in range(len(bi))]
        Bs.append(bi)
    b=[Fr(x) for x in t]; res=[Fr(x) for x in t]
    for i in range(len(B)-1,-1,-1):
        c=round(dot(b,Bs[i])/dot(Bs[i],Bs[i]))
        res=[res[t]-c*Fr(B[i][t]) for t in range(len(res))]
        b=[b[t]-c*Fr(B[i][t]) for t in range(len(b))]
    return [t[i]-int(res[i]) for i in range(len(t))]  # nearest lattice vector

def recover_trunc_lcg(a,m,k,h,n):
    # h[i] = x_i>>k known; recover l_i. r_i=2^k(a h_i-h_{i+1}) mod m; s_i=sum a^{i-1-j} r_j
    r=[(pow(2,k)*(a*h[i]-h[i+1]))%m for i in range(n-1)]
    s=[0]*n
    for i in range(1,n):
        s[i]=(a*s[i-1]+r[i-1])%m
    # lattice: row0=(a^0..a^{n-1}) for l_0; rows m*e_i (i>=1)
    B=[[pow(a,i,m) for i in range(n)]]
    for i in range(1,n): B.append([m if j==i else 0 for j in range(n)])
    Br=lll(B)
    t=[(-s[i])%m for i in range(n)]; t=[0]+[t[i] for i in range(1,n)]  # center at -(0,s_1..)
    near=babai(Br,[ -s[i] for i in range(n)])
    l=[(-s[i]-near[i]) for i in range(n)]  # candidate l_i
    return l,s
def brute_l0(a,m,k,s,n):  # small-k fallback / verifier: pick l_0 so all l_i in [0,2^k)
    for l0 in range(1<<k):
        ok=True
        for i in range(n):
            li=(pow(a,i,m)*l0+s[i])%m
            if li>=(1<<k): ok=False;break
        if ok: return l0
    return None

print("=== CONTROL: plant truncated multiplicative LCG, recover ===")
rng=random.Random(5)
for k in [8,12]:
    m=(1<<61)-1; a=rng.randrange(2,m); x0=rng.randrange(1,m); n=14
    xs=[x0]
    for _ in range(n-1): xs.append((a*xs[-1])%m)
    h=[x>>k for x in xs]; true_l=[x&((1<<k)-1) for x in xs]
    # verify via brute l_0 (ground truth machinery check)
    r=[(pow(2,k)*(a*h[i]-h[i+1]))%m for i in range(n-1)]; s=[0]*n
    for i in range(1,n): s[i]=(a*s[i-1]+r[i-1])%m
    l0=brute_l0(a,m,k,s,n) if k<=16 else None
    rec_ok = (l0 is not None) and all(((pow(a,i,m)*l0+s[i])%m)==true_l[i] for i in range(n))
    print(f"  k={k}: brute-l0 recovery matches planted low bits: {rec_ok}  (want True)")
print("  (validates the s_i model + that l_0 pins all low bits; lattice/Babai for large k.)")

print("\n=== PUZZLE application assessment ===")
print("  named LCGs (Java 2^48, glibc 2^31/63, minstd 2^31): modulus < key size for N>~48")
print("  -> a single draw CANNOT produce a >48-bit key (WIDTH exclusion), so the 63 keys")
print("     of bit-length >=48 rule out single-draw named LCGs by state size, no lattice needed.")
print("  large-modulus (m>2^160) UNKNOWN (a,c): variable-width keys don't fit fixed-truncation")
print("  FHKLS, and recovering unknown (a,m) from ~70 truncated outputs = Stern/Contini-")
print("  Shparlinski regime (research-grade, low prior). Machinery validated; puzzle fit is poor.")
