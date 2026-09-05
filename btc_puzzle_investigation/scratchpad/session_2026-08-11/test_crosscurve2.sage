import sys
p=43
def cover_trace_seq(A,B):
    seq=[]
    for k in [1,2,3]:
        Fq=GF(p**k); q=p**k; g=gcd(4,q-1); e=(q-1)//g
        Cc=1
        for x in Fq:
            rhs=x^3+Fq(A)*x+Fq(B)
            if rhs==0: Cc+=1
            elif rhs^e==1: Cc+=g
        Ee=EllipticCurve(Fq,[A,B]).cardinality()
        seq.append(Ee-Cc)
    a1,a2,a3=seq
    e1=a1; e2=(a1*e1-a2)//2; e3=(a3-a2*e1+a1*e2)//3
    return e1,e2,e3

curves=[("CM  y2=x3+7",0,7),("nonCM y2=x3+x+3",1,3),("nonCM y2=x3+x+5",1,5)]
print(f"p={p}. Cover A_new coeffs + census e2=e1^2+p, e3=-p*e1:", flush=True)
for name,A,B in curves:
    e1,e2,e3=cover_trace_seq(A,B)
    print(f"  {name:20s}: e1={e1} e2={e2} e3={e3} | e2=e1^2+p:{e2==e1^2+p} e3=-p*e1:{e3==-p*e1} | e1=0:{e1==0} e3=0:{e3==0}", flush=True)

print("\nCensus over family (vary constant a=1..8), e2(a)=e1(a)^2+p ?", flush=True)
for name,A in [("CM A=0",0),("nonCM A=1",1)]:
    hits=0;tot=0;nz=0;miss=[]
    for a in range(1,9):
        e1,e2,e3=cover_trace_seq(A,a); tot+=1
        if e1!=0: nz+=1
        if e2==e1^2+p: hits+=1
        else: miss.append((a,e1,e2))
    print(f"  {name}: census {hits}/{tot}, #(e1!=0)={nz}, misses={miss}", flush=True)

print("\nPart II: GLV (beta x,y) on curve? (exists iff A=0)", flush=True)
Fp=GF(p); beta=[Fp(b) for b in range(2,p) if Fp(b)^3==1 and Fp(b)!=1][0]
for name,A,B in curves:
    E=EllipticCurve(Fp,[A,B]); P=E.gens()[0]
    on=(P[1]^2==(beta*P[0])^3+A*(beta*P[0])+B)
    print(f"  {name:20s}: GLV exists: {on} (A={A})", flush=True)
