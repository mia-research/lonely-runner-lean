#!/usr/bin/env python3
"""
Finding 3 — the CLEAN test (2026-07-11), controlling every confound the earlier
attempts tripped on:
  * SAME sample set for both families (split rational primes / their Z[omega] gens)
  * SAME 1/sqrt(p) envelope kept (as in the finding: a_chi = chi/sqrt(p))
  * NULL = random-character null: replace chi-values with random unit-modulus
    numbers, keeping the identical envelope and samples. This isolates GENUINE
    cross-character structure from the shared envelope.
Verdict: real top eig > random-char null  <=>  genuine character common mode.
If real ~ null for BOTH Dirichlet and CM, the 'common mode' is the envelope, and
Finding 3's '3 vs 1' is not a sextic effect.  If CM real > CM null but Dirichlet
real ~ Dirichlet null, Finding 3 is REAL.
"""
import numpy as np, math
rng=np.random.default_rng(1)

def sieve(L):
    bs=bytearray([1])*(L+1); bs[0:2]=b'\x00\x00'
    for i in range(2,int(L**.5)+1):
        if bs[i]: bs[i*i::i]=bytearray(len(bs[i*i::i]))
    return [i for i in range(L+1) if bs[i]]
P=sieve(300000)
def fq2_mul(x,y,q):
    a,b=x; c,d=y; return ((a*c-b*d)%q,(a*d+b*c-b*d)%q)
def fq2_pow(x,e,q):
    r=(1,0)
    while e:
        if e&1: r=fq2_mul(r,x,q)
        x=fq2_mul(x,x,q); e>>=1
    return r
def fq2_gen(q):
    o=q*q-1; f=set(); m=o; d=2
    while d*d<=m:
        while m%d==0: f.add(d); m//=d
        d+=1
    if m>1: f.add(m)
    for a in range(q):
        for b in range(1,q):
            if all(fq2_pow((a,b),o//x,q)!=(1,0) for x in f): return (a,b)
def fq2_dlog(g,o,q):
    t={}; cur=(1,0)
    for e in range(o): t[cur]=e; cur=fq2_mul(cur,g,q)
    return t

# common samples: split primes with Z[omega] generator (a,b), norm p
eis=[]
for p in P:
    if p<=7 or p%3!=1: continue
    for b in range(1,int((4*p/3)**.5)+2):
        dd=4*p-3*b*b
        if dd<0: break
        s=int(dd**.5)
        if s*s==dd and (s+b)%2==0: eis.append((a:=(s+b)//2,b,p)); break
    if len(eis)>=500: break
sp=[p for (_,_,p) in eis]                 # the SAME rational primes for Dirichlet

def spectrum_and_null(cols, env, reps=120):
    """cols: list of complex feature-vectors over samples (pre-envelope).
    env: per-sample 1/sqrt(p) weight. Returns real top eig and random-char null top."""
    F=(np.array(cols).T)*env[:,None]
    def topeig(M):
        M=M-M.mean(0,keepdims=True); nr=np.linalg.norm(M,axis=0,keepdims=True); nr[nr==0]=1; M=M/nr
        return np.sort(np.linalg.eigvalsh((M.conj().T@M).real))[::-1][0]
    real=topeig(F)
    d=len(cols); n=len(env)
    nulls=[]
    for _ in range(reps):
        # random unit-modulus characters, SAME envelope + samples
        R=np.exp(2j*np.pi*rng.random((n,d)))*env[:,None]
        nulls.append(topeig(R))
    return real, np.mean(nulls), np.std(nulls)

env=np.array([1/math.sqrt(p) for p in sp])
qs_cm=[q for q in P if 10<q<200 and q%3==2][:8]
qs_dir=[q for q in P if 10<q<200 and q%3==1][:8]

# Dirichlet chars of the rational primes sp
dcols=[]
for q in qs_dir:
    f=set(); m=q-1; d=2
    while d*d<=m:
        while m%d==0: f.add(d); m//=d
        d+=1
    if m>1: f.add(m)
    g=next(x for x in range(2,q) if all(pow(x,(q-1)//e,q)!=1 for e in f))
    ind={}; cur=1
    for e in range(q-1): ind[cur%q]=e; cur=cur*g%q
    for j in range(1,q-1):
        dcols.append([np.exp(2j*np.pi*j*ind[p%q]/(q-1)) if p%q else 0 for p in sp])

# CM non-norm chars of pi mod inert q
ccols=[]
for q in qs_cm:
    o=q*q-1; g=fq2_gen(q); tab=fq2_dlog(g,o,q); ns=q+1; js=[]
    for j in range(1,o):
        if j%ns!=0: js.append(j)
        if len(js)>=q-1: break
    for j in js:
        ccols.append([np.exp(2j*np.pi*j*tab[(a%q,b%q)]/o) if (a%q,b%q)!=(0,0) else 0 for (a,b,_) in eis])

print("SAME samples (500 split primes), SAME 1/sqrt(p) envelope, RANDOM-CHARACTER null:\n")
for name,cols in (("Dirichlet(mu2)",dcols),("CM nonnorm(mu6)",ccols)):
    real,nm,ns=spectrum_and_null(cols,env)
    z=(real-nm)/ns if ns>0 else 0
    print(f"[{name:16}] d={len(cols):3}  real top eig={real:.3f}  "
          f"random-char null={nm:.3f}±{ns:.3f}  z={z:+.2f}  "
          f"-> {'GENUINE character mode' if z>3 else 'envelope only (= null)'}")
print("\nIf both z<=3: the 'common mode' is the 1/sqrt(p) envelope, NOT sextic.")
print("If CM z>3 and Dirichlet z<=3: Finding 3 REAL; retract dismissal.")
