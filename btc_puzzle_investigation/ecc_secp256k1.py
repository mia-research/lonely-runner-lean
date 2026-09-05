#!/usr/bin/env python3
"""
Exact secp256k1 scalar multiplication (Jacobian, integer-only) so we can construct
keys d -> P=d·G across the FULL bit range (the 100k set stops ~130-160 bits).
Validated against the real solved keys before any use.
"""
P  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
Gx = 0x79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798
Gy = 0x483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8
N_ORDER = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

def _dbl(Xx,Yy,Zz):
    if Yy==0: return (0,1,0)
    A=(Xx*Xx)%P; B=(Yy*Yy)%P; C=(B*B)%P
    D=(2*(((Xx+B)*(Xx+B)-A-C)))%P
    E=(3*A)%P; F=(E*E)%P
    X3=(F-2*D)%P
    Y3=(E*(D-X3)-8*C)%P
    Z3=(2*Yy*Zz)%P
    return (X3,Y3,Z3)

def _add(P1,P2):
    X1,Y1,Z1=P1; X2,Y2,Z2=P2
    if Z1==0: return P2
    if Z2==0: return P1
    Z1Z1=(Z1*Z1)%P; Z2Z2=(Z2*Z2)%P
    U1=(X1*Z2Z2)%P; U2=(X2*Z1Z1)%P
    S1=(Y1*Z2*Z2Z2)%P; S2=(Y2*Z1*Z1Z1)%P
    if U1==U2:
        if S1!=S2: return (0,1,0)
        return _dbl(X1,Y1,Z1)
    H=(U2-U1)%P; r=(S2-S1)%P
    HH=(H*H)%P; HHH=(H*HH)%P; V=(U1*HH)%P
    X3=(r*r-HHH-2*V)%P
    Y3=(r*(V-X3)-S1*HHH)%P
    Z3=(Z1*Z2*H)%P
    return (X3,Y3,Z3)

def scalar_mul(k, base=(Gx,Gy)):
    """affine (x,y) = k·base, exact. base affine."""
    R=(0,1,0); Q=(base[0],base[1],1)
    while k>0:
        if k&1: R=_add(R,Q)
        Q=_dbl(*Q); k>>=1
    Xx,Yy,Zz=R
    if Zz==0: return None
    zi=pow(Zz,P-2,P); zi2=(zi*zi)%P
    return ((Xx*zi2)%P, (Yy*zi2*zi)%P)

if __name__=="__main__":
    import csv
    ok=bad=0
    for r in csv.DictReader(open("puzzles_verified.csv")):
        d=int(r["private_key"],16); x,y=scalar_mul(d)
        if x==int(r["X"],16) and y==int(r["Y"],16): ok+=1
        else: bad+=1
    print(f"validation vs real solved keys: {ok} OK, {bad} MISMATCH")
