import csv, random, math
from collections import Counter
keys={}
with open("/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/puzzles_verified.csv") as f:
    for r in csv.DictReader(f): keys[int(r["puzzle"])]=int(r["private_key"],16)
puz=sorted(k for k in keys if k>=20)   # need >=20 bits to have low-16 meaningful
def lcg_fit(seq,m):
    # does seq[i+1] = a*seq[i]+c mod m hold for consistent (a,c)? derive from first consec triple, test rest
    best=0
    for s in range(len(seq)-2):
        x0,x1,x2=seq[s],seq[s+1],seq[s+2]
        d0=(x1-x0)%m
        if math.gcd(d0,m)!=1: continue
        a=((x2-x1)*pow(d0,-1,m))%m; c=(x1-a*x0)%m
        ok=sum(1 for i in range(len(seq)-1) if (seq[i+1]-(a*seq[i]+c))%m==0)
        best=max(best,ok)
    return best/(len(seq)-1)
def tests(vals,L):
    m=2**L; seq=[v%m for v in vals]
    # lag-1 autocorr
    n=len(seq); mn=sum(seq)/n
    num=sum((seq[i]-mn)*(seq[i+1]-mn) for i in range(n-1))
    den=sum((x-mn)**2 for x in seq)
    ac=num/den if den else 0
    # chi-square uniformity over 8 bins
    b=[0]*8
    for v in seq: b[v*8//m]+=1
    chi=sum((x-n/8)**2/(n/8) for x in b)
    return lcg_fit(seq,m), ac, chi
print("Structure in the PRESERVED low bits of consecutive solved keys (the wallet's raw output):\n")
for L in (12,16,20):
    real=[keys[p] for p in puz]
    lr,ar,cr=tests(real,L)
    # control: random keys, same count
    random.seed(0); ctrl=[random.getrandbits(64) for _ in puz]
    lc,acc,cc=tests(ctrl,L)
    print(f" low-{L} bits ({len(real)} keys):")
    print(f"   best LCG fit:  real={lr*100:4.1f}%   random-control={lc*100:4.1f}%   (100% = perfect LCG)")
    print(f"   lag-1 autocorr: real={ar:+.3f}   random-control={acc:+.3f}")
    print(f"   chi2 (df=7):    real={cr:5.1f}   random-control={cc:5.1f}   (~random if <14)")
