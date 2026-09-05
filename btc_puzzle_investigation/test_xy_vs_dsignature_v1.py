#!/usr/bin/env python3
"""
Does (X,Y) leak the USER'S EXACT D-signature terms?  Now that the recursion is
the correct one (d_recursion, N=2^bits on the full key), test each D-term D_i for
leakage with the validated pipeline (MI + exclusion, permutation-validated, real
controls). Uses cached keys (bits 64-130, have X,Y,d).
"""
import knd_common as K

def d_recursion(N, error):
    sig=[]; e=abs(error)
    while e>0:
        D=N//e
        if D==0: break
        sig.append(D); e=abs(e-N//D)
    return sig

c=K.load_decomp(64); X=c["X"];Y=c["Y"];DS=c["d"];BITS=c["bits"];M=len(X)
# D-signature per key (user's exact recursion, N=2^bits on the full private key)
SIG=[d_recursion(1<<BITS[i], DS[i]) for i in range(M)]
Lens=[len(s) for s in SIG]
from collections import Counter
print(f"keys: {M}  D-signature length dist: {dict(sorted(Counter(Lens).items()))}")

def term(i, l):  # D_i mod l, or a sentinel bucket if the signature is shorter
    return [ (SIG[j][i] % l) if len(SIG[j])>i else l for j in range(M)]

print("\n(X,Y) -> D-signature term D_i  (perm-validated; controls at floor):")
for l in (7,13):
    dd=[d%l for d in DS]
    import random; rnd=random.Random(1)
    pf=dd[:]; pp=[dd[j] if rnd.random()<0.4 else rnd.randrange(l) for j in range(M)]
    _,cf=K.perm_p(pf,dd,K.gtest_z,B=200); _,cp=K.perm_p(pp,dd,K.gtest_z,B=200)
    print(f" l={l}  [controls] d%l:p={cf:.3f}  40%-signal:p={cp:.3f}")
    feats={"Xmod":[x%l for x in X],"XYmod":[(X[j]*Y[j])%l for j in range(M)],
           "v_l":[((Y[j]%l)**2-(X[j]%l)**3-7)%l for j in range(M)]}
    for i in range(1,6):   # D_0 is trivially 1 for full-key; test D_1..D_5
        tb=term(i,l)
        cells=[]
        for fn,fa in feats.items():
            z=K.gtest_z(fa,tb); mr,_=K.min_resid(fa,tb)
            mark=""
            if abs(z)>2.5 or mr<-3.5:
                _,pz=K.perm_p(fa,tb,K.gtest_z,B=300); mark=f"[p={pz:.3f}]"
            cells.append(f"{fn}:z={z:+.1f}/mr={mr:+.1f}{mark}")
        print(f"   D_{i}: " + "  ".join(cells))
