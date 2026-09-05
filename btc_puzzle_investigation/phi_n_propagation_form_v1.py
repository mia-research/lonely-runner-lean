#!/usr/bin/env python3
"""
#3  Propagation-shaped targets (best available; the exact functional form is the
user's to supply). The documented D-term recursion IS a recursive-error process:
  err0 = d - base,  D_1 = floor(A/|err0|),  term = sign·floor(A/D_1),  iterate.
Propagation/bidirectional targets that a coarse<->fine coupling would populate:
  - D_1     (first/coarsest recursion term)      -> mod q
  - D_terms (recursion depth)
  - D mod n (fine residual relative to the COARSE denominator n = the ratio form)
  - sign(err0) already tested (null).
Test (X,Y) features {X mod q, (X*Y) mod q, v_l point-vs-curve} against them with
the permutation-validated pipeline (+ n-vs-k positive control). If the user's
model names a different shape, swap the target — the harness is identical.
"""
import knd_common as K
c=K.load_decomp(64)
X=c["X"];Y=c["Y"];NS=c["n"];KS=c["k"];DS=c["d"];DD=c["D"];BITS=c["bits"];M=len(X)

def d1_and_terms(d,N,res):
    A=1<<(N-1); e=res; run=d-res  # run=base
    if e==0: return 0,0
    D1=A//abs(e); terms=0; cur=run
    while e!=0 and terms<64:
        Di=A//abs(e)
        if Di==0: break
        cur += (1 if e>0 else -1)*(A//Di); e=d-cur; terms+=1
    return D1,terms

D1=[];DT=[];DmodN=[]
for i in range(M):
    a,b=d1_and_terms(DS[i],BITS[i],DD[i]); D1.append(a); DT.append(b)
    DmodN.append(DD[i]%NS[i] if NS[i]>0 else 0)

def report(featname, fa, q):
    line=[]
    for tn,tb in (("D1modq",[v%q for v in D1]),("D_terms",[min(t,6) for t in DT]),
                  ("DmodN",[v%q for v in DmodN]),("dmodq",[v%q for v in DS])):
        _,pz=K.perm_p(fa,tb,K.gtest_z,B=300,worse="ge")
        _,pm=K.perm_p(fa,tb,lambda a,b:K.min_resid(a,b)[0],B=300,worse="le")
        flag="*" if min(pz,pm)<0.01 else " "
        line.append(f"{tn}:MIp={pz:.2f}/exl={pm:.2f}{flag}")
    print(f"  {featname:12s} q={q}: " + "  ".join(line))

print(f"N>=64 keys: {M}")
print("(X,Y) feature  vs  propagation/recursion targets  (perm p: MI / exclusion):")
for q in (5,7,16):
    report("X modq",     [x%q for x in X], q)
    report("(X*Y)modq",  [(X[i]*Y[i])%q for i in range(M)], q)
    vl=[((Y[i]%q)**2-(X[i]%q)**3-7)%q for i in range(M)] if q in (5,7) else [x%q for x in X]
    if q in (5,7): report("v_l(pt-curve)", vl, q)
    print()

# dmodq is the KEY target — summarise whether ANYTHING hit d
print("KEY CHECK: did any (X,Y) feature predict d itself? (see dmodq columns above)")
print("\nPOSITIVE CONTROL n vs k mod 7 (exclusion):")
_,p=K.perm_p([v%7 for v in NS],[v%7 for v in KS],lambda a,b:K.min_resid(a,b)[0],B=300,worse="le")
print(f"  perm p={p:.3f}")
