# Integer arrangement R (7 distinct positive integers, subject slowest). Test: is R lonely at some t = k/M,
# M = 2^max(v+1,3), v = max 2-adic valuation of a reading, k odd?  (grid through D = 1, refined 2-adically)
import itertools, random, sys
def nu(r):
    n=0
    while r%2==0: r//=2; n+=1
    return n
def clear(r,k,M):          # ||r k / M|| >= 1/8   <=>   (r k mod M) in [M/8, 7M/8]
    x=(r*k)%M
    return 8*x>=M and 8*x<=7*M
def two_adic_ok(R):
    v=max(nu(r) for r in R); M=2**max(v+1,3)
    return any(all(clear(r,k,M) for r in R) for k in range(1,M,2))
def lonely_any(R,maxden=None):
    # exact: lonely set periodic of period 1; test t=k/M for M = 8*m, m up to bound
    for m in range(1,200):
        M=8*m
        for k in range(1,M):
            if all(clear(r,k,M) for r in R): return True
    return False
bad=[];n=0
N=int(sys.argv[1])
for R in itertools.combinations(range(1,N+1),7):
    n+=1
    if not two_adic_ok(R): bad.append(R)
print("N",N,"arrangements",n,"2-adic grid fails",len(bad))
for R in bad[:15]: print(R, "lonely at some k/8m, m<200:", lonely_any(R))
random.seed(1); badr=[]
for _ in range(20000):
    R=tuple(sorted(random.sample(range(1,400),7)))
    if not two_adic_ok(R): badr.append(R)
print("random up to 400: fails",len(badr),"of 20000")
for R in badr[:10]: print(R, lonely_any(R))
