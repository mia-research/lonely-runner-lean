p = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
n = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
Gx = 0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798
Gy = 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8
def inv(a,m): return pow(a,-1,m)
def add(P,Q):
    if P is None: return Q
    if Q is None: return P
    x1,y1=P; x2,y2=Q
    if x1==x2 and (y1+y2)%p==0: return None
    if P==Q: l=(3*x1*x1)*inv(2*y1,p)%p
    else: l=(y2-y1)*inv((x2-x1)%p,p)%p
    x3=(l*l-x1-x2)%p; y3=(l*(x1-x3)-y1)%p; return (x3,y3)
def neg(P): return None if P is None else (P[0],(-P[1])%p)
def mul(k,P):
    R=None;Q=P;k%=n
    while k>0:
        if k&1: R=add(R,Q)
        Q=add(Q,Q); k>>=1
    return R
def oncurve(P): return (P[1]*P[1]-P[0]**3-7)%p==0

d130=0x33e7665705359f04f28b88cf897c603c9
x130=0x633cbe3ec02b9401c5effa144c5b4d22f87940259634858fc7e59b1c09937852
y130=0xb078a17cc1558a9a4fa0b406f194c9a2b71d9a61424b533ceefe27408b3191e3
x135=0x145d2611c823a396ef6712ce0f712f09b9b4f3135e3e0aa3230fb9b6d08d1e16
y135=0x667a05e9a1bdd6f70142b66558bd12ce2c0f9cbc7001b20c8a6a109c80dc5330
P130=(x130,y130); P135=(x135,y135)

print("§1 verify:")
print(f"  P130 on curve: {oncurve(P130)}   P135 on curve: {oncurve(P135)}")
print(f"  [d130]G == P130: {mul(d130,(Gx,Gy))==P130}")

Psum=add(P130,P135); Pdiff=add(P130,neg(P135))
xsum_doc=0x2e9978d9a0dda3c682b1ab3ac029661e143dbd36e4fc4b296134e7c1781a7486
xdiff_doc=0x50b5600ae8cc45cd35bbe801a02c81a3db9bcd7a08bbf78bb91c4f51cf55ad06
print("\n§2 verify sum/diff coords:")
print(f"  x(sum)  matches doc: {Psum[0]==xsum_doc}")
print(f"  x(diff) matches doc: {Pdiff[0]==xdiff_doc}")

# §3 Semaev S3
def S3(x1,x2,x3,B=7):
    t1=((x1-x2)**2 * x3*x3)%p
    t2=(2*((x1+x2)*(x1*x2%p)%p + 2*B)*x3)%p
    t3=((x1*x2%p)**2 - 4*B*(x1+x2))%p
    return (t1-t2+t3)%p
print("\n§3 Semaev S3 roots:")
print(f"  S3(x130,x135,x_sum)  == 0: {S3(x130,x135,Psum[0])==0}")
print(f"  S3(x130,x135,x_diff) == 0: {S3(x130,x135,Pdiff[0])==0}")

# §4 Vieta
A_c=((x130-x135)**2)%p
B_c=(-2*((x130+x135)*(x130*x135%p)%p + 14))%p
C_c=((x130*x135%p)**2 - 28*(x130+x135))%p
sig1=(-B_c*inv(A_c,p))%p
sig2=(C_c*inv(A_c,p))%p
print("\n§4 Vieta:")
print(f"  sigma1 == x_sum+x_diff: {sig1==(Psum[0]+Pdiff[0])%p}")
print(f"  sigma2 == x_sum*x_diff: {sig2==(Psum[0]*Pdiff[0])%p}")

print("\n§5 CRUX: is c_sum measurable from PUBLIC coords?")
print("  c_sum = floor((-1)^s (d130+d135) lam^j / n)  -> needs d_sum = d130 + d135 = the UNKNOWN d135.")
print("  §3/§4 give x_sum, x_diff (public, from adding public points) -- they contain NO scalar info.")
print("  'measuring c_sum from the sum POINT coordinates' is unsupported: c_sum is a scalar carry,")
print("  not a coordinate. The ONLY candidate public route to the carry/eps is doc 19 §4A (untested).")
