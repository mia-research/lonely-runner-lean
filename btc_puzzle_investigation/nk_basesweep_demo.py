import pandas as pd, math
P=0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
Gx=0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy=0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
def add(A,B):
    if A is None:return B
    if B is None:return A
    x1,y1=A;x2,y2=B
    if x1==x2 and (y1+y2)%P==0:return None
    l=((3*x1*x1)*pow(2*y1,-1,P) if A==B else (y2-y1)*pow(x2-x1,-1,P))%P
    x3=(l*l-x1-x2)%P;return (x3,(l*(x1-x3)-y1)%P)
def mul(k,Pt=(Gx,Gy)):
    if k<0: k=-k; Pt=(Pt[0],(-Pt[1])%P)
    R=None
    while k:
        if k&1:R=add(R,Pt)
        Pt=add(Pt,Pt);k>>=1
    return R
def neg(A): return None if A is None else (A[0],(-A[1])%P)
def bsgs(R, L):
    """find e with e*G=R, |e|<=L, via baby-step giant-step. Returns e or None."""
    m=int(math.isqrt(L))+1
    baby={}; cur=None
    for i in range(m+1):
        baby[cur]=i; cur=add(cur,(Gx,Gy))     # i*G
    mg=mul(m); step=neg(mg)                     # -m*G
    # search e = q*m + i for q in [-(L//m)-1 .. L//m+1]
    gq=R
    for q in range(0, L//m+2):
        if gq in baby: return q*m+baby[gq]
        gq=add(gq,step)
    gq=R
    for q in range(1, L//m+2):                  # negative e
        gq=add(gq,mg)
        if gq in baby: return -(q*m)+ (baby[gq] if gq in baby else 0) if gq in baby else None
    return None

df=pd.read_csv("constructed_keys_1to160_100k.csv", dtype={"D":str,"d":str,"X":str,"Y":str})
df["Dabs"]=[abs(int(v)) for v in df.D]
print("=== D==0 rate BY BAND (is the free-lookup break useful at large N?) ===")
for lo in range(1,161,20):
    sub=df[(df.bits>=lo)&(df.bits<lo+20)]
    if len(sub)==0:continue
    z=(sub.Dabs==0).mean()*100
    print(f"  bits {lo:3d}-{lo+19:3d}: D==0 rate = {z:5.2f}%")

# demo: largest-N key with 0<|D|<2^30, recover end-to-end from (X,Y,bits)+construction
cand=df[(df.Dabs>0)&(df.Dabs<2**30)].sort_values("bits",ascending=False)
r=cand.iloc[0]
bits,n,k=int(r.bits),int(r.n),int(r.k); Dtrue=int(r.D)
X,Y,dtrue=int(r.X,16),int(r.Y,16),int(r.d)
print(f"\n=== end-to-end base-relative recovery demo ===")
print(f"  target: bits={bits} (d has {dtrue.bit_length()} bits), |D|=2^{abs(Dtrue).bit_length()-1}..")
print(f"  PUBLIC inputs used: (X,Y,bits) + known construction. (n,k) taken as the swept candidate.")
A=1<<(bits-1); base=A+(A*k)//n
Bpt=mul(base); R=add((X,Y),neg(Bpt))           # R = P - base*G = D*G
Drec=bsgs(R, 2**30)
d_rec=base+Drec if Drec is not None else None
ok = d_rec==dtrue and mul(d_rec)==(X,Y)
print(f"  base=A+floor(A*k/n); R=P-base*G; BSGS on R (budget 2^30) -> D_rec={Drec}")
print(f"  reconstructed d == true d AND d_rec*G == (X,Y): {ok}")
print(f"  => full private key recovered from public point for this key.")
print(f"  blind cost note: identifying (n,k) among ~20k coprime pairs costs ~2^14.3;")
print(f"  base-sweep saves ~{bits - (abs(Dtrue).bit_length())} DLP bits here but you pay ~14 bits to find (n,k).")
print("\nDONE")
