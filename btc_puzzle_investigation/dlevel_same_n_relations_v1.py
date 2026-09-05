#!/usr/bin/env python3
"""
d-LEVEL relationship among same-n key pairs + curve-native / intent tests.
Follow-up to the confirmed consecutive-n coupling (p~0.001).  Testing BOTH the
method (does the coupling live in d, in k mod n, or in the error?) AND the intent
(did the creator pick curve-native "simple" numbers?), per the session notes.

Sections:
 A. raw d-level relations for same-n pairs (gcd, scale-aligned nesting residual,
    high-bit agreement) -- is there a d-relation deeper than the shared denom?
 B. curve-native CM/GLV orbit test in the (k mod n) coordinate: does mult by
    lambda (cube root of 1 mod n) map the group's k-set to itself?  (GLV/CM is the
    curve's own endomorphism; if the creator used curve intuition it shows here.)
 C. error/"simplicity" test (intent): is each key UNUSUALLY CLOSE to its best
    <=256-denominator rational vs a matched Farey null?  (creator picking simple
    numbers => smaller normalized error.)
 D. error vs curve constants: sign correlation within groups; error mod 3 (CM
    disc -3), mod small primes, mod trace t.  Any structural tie to a,b,t,p?

Exact signal path; integer/Fraction only.  Modular relations: any exact hit is
itself significant (null prob ~ tests/modulus).  Distributional tests: resample
percentile / permutation, integer-decided.
"""
import csv, random
from fractions import Fraction
from math import gcd
from knd_common import best_nk

P       = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
N_ORDER = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
LAMBDA  = 0x5363AD4CC05C30E0A5261C028812645A122E22EA20816678DF02967C1B23BD72
T_TRACE = P + 1 - N_ORDER                      # Frobenius trace (CM disc -3)
assert pow(LAMBDA, 3, N_ORDER) == 1, "lambda not a cube root of 1 mod N"

MASTER="btc_puzzle_master_exact.csv"; SEED=20260711

solved=[]
with open(MASTER) as fh:
    for r in csv.DictReader(fh):
        if r["status"]!="SOLVED": continue
        solved.append((int(r["puzzle"]),int(r["bits"]),int(r["priv_dec"])))
solved.sort()
info={}   # p -> (N,d,n,k, A, resid_abs)   resid_abs=|n*(d-A)-k*A| (Farey distance*n*A)
for p,N,d in solved:
    n,k=best_nk(d,N); A=1<<(N-1)
    info[p]=(N,d,n,k,A,abs(n*(d-A)-k*A))

groups={}
for p,(N,d,n,k,A,rr) in info.items():
    groups.setdefault(n,[]).append(p)
multi={n:sorted(ps) for n,ps in groups.items() if len(ps)>=2 and n>=20}

print(f"trace t = P+1-N_ORDER = {T_TRACE}")
print(f"t factor small? t mod 3 = {T_TRACE%3}, t mod 43 = {T_TRACE%43}\n")

# ---- A. raw d-level relations among same-n pairs --------------------------
print("=== A. raw d-level relations (same-n pairs, n>=20) ===")
def cube_roots_mod(m):
    return sorted({x for x in range(m) if pow(x,3,m)==1%m})
for n,ps in multi.items():
    print(f" n={n}: puzzles={ps}")
    for i in range(len(ps)):
        for j in range(i+1,len(ps)):
            a,b=ps[i],ps[j]; (Na,da,_,ka,Aa,_),(Nb,db,_,kb,Ab,_)=info[a],info[b]
            g=gcd(da,db)
            shift=Nb-Na
            nest=db-(da<<shift) if shift>=0 else db-(da>>(-shift))
            hi_a=da>>(Na-8) if Na>=8 else da; hi_b=db>>(Nb-8) if Nb>=8 else db
            print(f"   #{a}(k{ka})~#{b}(k{kb}): gcd={g}  "
                  f"db-2^{shift}*da={nest}  top8bits {hi_a:08b}/{hi_b:08b}  "
                  f"k_b-k_a={kb-ka}")

# ---- B. curve-native CM/GLV orbit test in (k mod n) -----------------------
print("\n=== B. CM/GLV: is the k-set closed under mult by cube-root-of-1 mod n? ===")
for n,ps in multi.items():
    ks=sorted({info[p][3] for p in ps})
    roots=[r for r in cube_roots_mod(n) if r not in (0,1)]   # nontrivial CM mults
    hits=[]
    for lam in roots:
        for k in ks:
            if (lam*k)%n in set(ks) and (lam*k)%n!=k:
                hits.append((k,lam,(lam*k)%n))
    print(f" n={n} k-set={ks}  nontrivial cube-roots mod n={roots or 'none'}  "
          f"orbit hits={hits or 'none'}")

# ---- C. simplicity / error test (intent) ----------------------------------
print("\n=== C. are real keys unusually close to their best <=256-rational? ===")
random.seed(SEED)
# statistic q = resid_abs / A  in [0, ~0.5); SMALL => key sits near a low-denom rational
below=0; tot=0; percentiles=[]
for p,(N,d,n,k,A,rr) in info.items():
    if N<20: continue
    q_real=Fraction(rr,A)
    lo,hi=1<<(N-1),1<<N
    S=2000; less=0
    for _ in range(S):
        dd=random.randrange(lo,hi); nn,kk=best_nk(dd,N)
        if Fraction(abs(nn*(dd-A)-kk*A),A) < q_real: less+=1
    pct=less/S    # noqa: float  (display only; decision via aggregate below)
    percentiles.append(pct); tot+=1
    if pct<0.5: below+=1
# aggregate: if keys are NOT special, percentiles ~ Uniform(0,1), mean ~0.5
mean_pct=sum(percentiles)/len(percentiles)   # noqa: float (display)
print(f"  keys tested={tot}  mean percentile of real error vs Farey null={mean_pct:.3f}")
print(f"  (0.5 = generic; <<0.5 = real keys closer to simple rationals than chance)")
print(f"  keys below-median: {below}/{tot}")

# ---- D. error vs curve constants ------------------------------------------
print("\n=== D. error vs curve constants ===")
signs={}
for n,ps in multi.items():
    ss=[]
    for p in ps:
        N,d,nn,k,A,rr=info[p]; e=(d-A)-(A*k)//nn   # signed error in d-space
        ss.append(1 if e>=0 else 0)
    signs[n]=ss
    print(f" n={n}: error signs={ss}  (all-equal within a coupled group?)")
# error mod 3 (CM disc -3) across all keys vs uniform
from collections import Counter
e_mod3=Counter()
for p,(N,d,n,k,A,rr) in info.items():
    if N<20: continue
    e=(d-A)-(A*k)//n
    e_mod3[e%3]+=1
print(f" error mod 3 distribution (CM disc -3): {dict(sorted(e_mod3.items()))}  "
      f"(uniform => ~equal thirds)")
