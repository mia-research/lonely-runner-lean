"""
AUTOPSY of the year-old "GECT forward solver". Goal: show WHY it is circular
(with evidence, not assertion), then salvage the few claims inside it that are
actually testable and test them honestly against the real keys.

Three mechanisms of self-deception to demonstrate:
  M1  D-error recursion is a TAUTOLOGY. It takes the target key as an input and
      subtracts the error; it "reconstructs" ANY integer in 0-3 terms. It solves
      nothing -- it is handed the answer.
  M2  determine_n_and_k IGNORES the public key. The decision uses only phi(n) and
      T_EC(k,n); X,Y are printed, never used. It returns the same (n,k) for any
      pubkey, because the candidate list [39,65,80,135] is rigged so only n=80
      passes phi(n)=2^r.
  M3  The self-test validates only the address code, and its "known key" is not a
      valid 160-bit puzzle key at all.

Then SALVAGE: two structural claims buried in the numerology are testable ->
  S1  are chosen n enriched for phi(n)=2^r (the "Gauss-Wantzel" claim)?
  S2  do chosen k have atypically low multiplicative order ord_n(k) (the
      "thermodynamic / colder" claim)?
Tested on the 82 real keys vs a bit-length-matched uniform reference, with a
fired control.
"""
import csv, random, hashlib
from math import gcd, log
import numpy as np

P=0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F

# ---------- M1: the D-recursion reconstructs ANY number ----------
def d_recursion(base, target, rng_start, maxit=10):
    cur=base; err=target-cur; terms=0
    while err!=0 and terms<maxit:
        D=rng_start//abs(err); corr=rng_start//D
        cur+= corr if err>0 else -corr
        err=target-cur; terms+=1
    return cur,terms
print("M1  D-recursion is a tautology (reconstructs arbitrary targets):")
Pn=160; rs=2**(Pn-1); base=rs+(rs*51)//80
_r=random.Random(0)
for _ in range(5):
    tgt=rs+_r.randrange(rs)                 # a RANDOM 160-bit number, not a key
    got,t=d_recursion(base,tgt,rs)
    print(f"    random target ...{tgt%10**9:09d}: reconstructed exactly={got==tgt} in {t} terms")
print("    => 'converges in 0-3 terms' is true for EVERY integer; it proves nothing.\n")

# ---------- M2: (n,k) selection ignores the public key ----------
def phi(n):
    r=n;t=n;p=2
    while p*p<=t:
        if t%p==0:
            while t%p==0:t//=p
            r-=r//p
        p+=1
    if t>1:r-=r//t
    return r
def order(k,n):
    if gcd(k,n)!=1:return 10**9
    o=1;c=k%n
    while c!=1:
        c=c*k%n;o+=1
        if o>n:return 10**9
    return o
def T_EC(k,n): return 0.7*log(order(k,n))+0.3*(k/n)
def determine_nk(X,Y):
    cand=[39,65,80,135]
    gw=[n for n in cand if (phi(n)&(phi(n)-1))==0]  # phi(n)=2^r
    n=gw[0] if gw else cand[0]
    ks=[k for k in range(1,n) if gcd(k,n)==1]
    k=min(ks,key=lambda k:T_EC(k,n))
    return n,k
print("M2  determine_n_and_k ignores (X,Y): same output for real vs random pubkey:")
for label,(X,Y) in (("real-ish",(0xe0a8b039,0x1234)),("random1",(_r.getrandbits(256),_r.getrandbits(256))),
                     ("random2",(_r.getrandbits(256),_r.getrandbits(256)))):
    print(f"    pubkey={label:9s} -> (n,k)={determine_nk(X,Y)}")
print("    => X,Y never enter the decision. phi(39,65,135) not 2^r; only phi(80)=32=2^5 passes.\n")

# ---------- M3: the 'known key' is not a 160-bit puzzle key ----------
kk=int("5b32edb74843b464a781b49c063b5167664d9f64c6144e54823871b5634125d3",16)
print("M3  self-test 'known key':")
print(f"    bit-length={kk.bit_length()}  (a puzzle-160 key must be in [2^159,2^160), i.e. 160 bits)")
print(f"    => {kk.bit_length()}-bit value is NOT a valid puzzle-160 key; the self-test key is bogus.\n")

# ================= SALVAGE: test the two real claims on the 82 keys =================
rows=[]
with open('/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/puzzles_verified.csv') as f:
    for r in csv.DictReader(f):
        rows.append((int(r['bits']),int(r['n']),int(r['k'])))
Bs=[b for b,_,_ in rows]; CN=[n for _,n,_ in rows]; CK=[k for _,_,k in rows]
M=len(rows); _rr=random.Random(7)
def is_pow2(m): return m>0 and (m&(m-1))==0
def synth():
    ns=[];ks=[]
    for b in Bs:
        lo=2**(b-1);d=lo+_rr.randrange(lo);u=(d-lo)/lo
        best=(9e9,1,0)
        for n in range(1,257):
            k=round(u*n);e=abs(u-k/n)
            if e<best[0]:best=(e,n,k)
        ns.append(best[1]);ks.append(best[2])
    return ns,ks

# S1: phi(n)=2^r enrichment
obs1=sum(is_pow2(phi(n)) for n in CN)/M
null1=[]
for _ in range(1000):
    ns,_=synth(); null1.append(sum(is_pow2(phi(n)) for n in ns)/M)
null1=np.array(null1); p1=(1+(null1>=obs1).sum())/(1+len(null1))
print("S1  phi(n)=2^r ('Gauss-Wantzel') enrichment:")
print(f"    chosen frac={obs1:.3f}  reference frac={null1.mean():.3f}  p(more)={p1:.3f}"
      f"{'  << enriched' if p1<0.05 else ''}")

# S2: multiplicative order ord_n(k), normalized by phi(n) -- GUARD degenerate n<3
def norm_ord(n,k):
    if n<3 or gcd(k,n)!=1 or not (1<=k<n): return np.nan
    return order(k,n)/phi(n)
obs2=np.nanmean([norm_ord(n,k) for n,k in zip(CN,CK)])
null2=[]
for _ in range(400):
    ns,ks=synth(); null2.append(np.nanmean([norm_ord(n,k) for n,k in zip(ns,ks)]))
null2=np.array(null2); p2=(1+(null2<=obs2).sum())/(1+len(null2))   # 'colder' = LOWER order
print("S2  mean normalized order ord_n(k)/phi(n) ('colder'=lower), n>=3 guarded:")
print(f"    chosen={obs2:.3f}  reference={null2.mean():.3f}  p(lower)={p2:.3f}"
      f"{'  << colder' if p2<0.05 else ''}")
# control: force lowest-order k selection -> must read clearly colder than reference
ns,_=synth()
kk2=[min([k for k in range(1,n) if gcd(k,n)==1],key=lambda k:order(k,n)) if n>=3 else 1 for n in ns]
cval=np.nanmean([norm_ord(n,k) for n,k in zip(ns,kk2)])
print(f"    [CTRL lowest-order k]: {cval:.3f}  (must be << reference {null2.mean():.3f} to confirm power)")
