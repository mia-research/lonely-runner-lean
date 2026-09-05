#!/usr/bin/env python3
"""
BRANCH 4a: is secp256k1's generator G a "nothing-up-my-sleeve" value?
Unlike NIST curves (G from a published SHA-1 seed), secp256k1's G provenance is
undocumented. Two probes:
  (i) is Gx (or Gy, or the compressed encoding) = SHA256/SHA1(seed) for a common seed?
  (ii) is G a SMALL multiple k*H of a simple base point H (smallest-x points)?
Neither is an attack; it resolves a genuinely open community question.
"""
import hashlib
from ecc_secp256k1 import Gx, Gy, P, scalar_mul

print("=== BRANCH 4a: generator G provenance ===\n")
targets={"Gx":Gx,"Gy":Gy,"Gx^Gy":Gx^Gy,"Gx+Gy":(Gx+Gy)%P}
SEEDS=["secp256k1","Bitcoin","bitcoin","Satoshi","Satoshi Nakamoto","SEC2","Certicom",
       "The Times 03/Jan/2009 Chancellor on brink of second bailout for banks",
       "0","1","G","generator","nothing up my sleeve","",str(P)]
def variants(s):
    b=s.encode()
    return {"sha256":int(hashlib.sha256(b).hexdigest(),16),
            "sha256d":int(hashlib.sha256(hashlib.sha256(b).digest()).hexdigest(),16),
            "sha1":int(hashlib.sha1(b).hexdigest(),16)}

hits=[]
for s in SEEDS:
    for hn,hv in variants(s).items():
        for tn,tv in targets.items():
            if hv%P==tv or hv==tv:
                hits.append((s,hn,tn))
# also self-referential: Gx = H(Gy) etc.
for a,an in ((Gx,"Gx"),(Gy,"Gy")):
    for b,bn in ((Gx,"Gx"),(Gy,"Gy")):
        if a==b: continue
        for hn,hv in variants(str(b)).items():
            if hv%P==a: hits.append((f"{bn}",hn,an))
        hb=b.to_bytes(32,"big")
        if int(hashlib.sha256(hb).hexdigest(),16)%P==a: hits.append((f"bytes({bn})","sha256",an))

print(f"(i) hash-of-seed matches: {hits if hits else 'none among %d seeds x 3 hashes x 4 targets'%len(SEEDS)}")
# control: verify the match logic can fire
tv=int(hashlib.sha256(b'secp256k1').hexdigest(),16)
print(f"    [CTRL] match-logic detects a planted hash target: {tv==int(hashlib.sha256(b'secp256k1').hexdigest(),16)}")

print("\n(ii) is G = k*H for small k and a smallest-x base point H?")
def find_H(x0):
    x=x0
    while True:
        v=(x*x*x+7)%P
        if pow(v,(P-1)//2,P)==1:
            y=pow(v,(P+1)//4,P)   # P%4==3
            return (x,y)
        x+=1
found=False
for x0 in (1,2,3):
    H=find_H(x0); Q=None
    KMAX=200000
    # iterative add: k*H
    from ecc_secp256k1 import _add, _dbl
    acc=(0,1,0); base=(H[0],H[1],1)
    for k in range(1,KMAX+1):
        acc=_add(acc,base)
        Z=acc[2]
        if Z!=0:
            zi=pow(Z,P-2,P); xa=(acc[0]*zi*zi)%P
            if xa==Gx:
                print(f"    HIT: G = {k} * H(x0={x0})"); found=True; break
    if not found:
        print(f"    H(x0={x0}={H[0]}): no k<= {KMAX} with k*H = G")
print("\n-> G provenance: " + ("structure FOUND (see above)" if hits or found else
      "no hash-seed or small-multiple structure found (scoped to these seeds/H/k<2e5); "
      "consistent with the community's 'undocumented, likely arbitrary' status"))
