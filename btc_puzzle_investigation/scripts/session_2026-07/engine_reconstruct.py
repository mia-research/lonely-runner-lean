"""
Reconstruct-the-deterministic-engine attempt on the 82 verified keys ONLY.
Tests the assumption that residual/low bits are 'noise' by hunting for the
linear/deterministic structure a weak generator (LFSR/LCG/counter/single-master)
would leave. Data: btc_puzzle_investigation/puzzles_verified.csv.
"""
import csv, math
from math import gcd

rows=[]
with open('/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/puzzles_verified.csv') as f:
    for r in csv.DictReader(f):
        rows.append((int(r['puzzle']),int(r['bits']),int(r['private_key'],16)))
rows.sort()
keys=[k for _,_,k in rows]; bits=[b for _,b,_ in rows]
seq=[p for p,_,_ in rows]

# ---------- Berlekamp-Massey linear complexity over GF(2) ----------
def berlekamp_massey(s):
    n=len(s); C=[0]*n; B=[0]*n; C[0]=1; B[0]=1; L=0; m=1
    for i in range(n):
        d=s[i]
        for j in range(1,L+1): d^=C[j]&s[i-j]
        if d==0:
            m+=1
        elif 2*L<=i:
            T=C[:]
            for j in range(n-m):
                if j+m<n: C[j+m]^=B[j]
            L=i+1-L; B=T; m=1
        else:
            for j in range(n-m):
                if j+m<n: C[j+m]^=B[j]
            m+=1
    return L

print("=== [1] Berlekamp-Massey linear complexity of low-bit COLUMNS (n=82) ===")
print("    random sequence expects ~n/2 = 41.  Much lower => LFSR/deterministic.")
import random as _r
for bit in range(8):
    col=[(k>>bit)&1 for k in keys]
    L=berlekamp_massey(col)
    print(f"    bit{bit}: ones={sum(col):2d}/82   linear_complexity={L}")
# random baseline
_r.seed(0)
base=[berlekamp_massey([_r.randint(0,1) for _ in range(82)]) for _ in range(200)]
print(f"    [random baseline] LC mean={sum(base)/len(base):.1f}  min={min(base)}  (over 200 trials)")

# ---------- single-master SUFFIX: do keys share a common low-bit tail? ----------
print("\n=== [2] single-master SUFFIX test: shared low bits between key pairs ===")
def shared_suffix(a,b):
    t=0
    while ((a^b)>>t)&1==0 and t<64: t+=1
    return t
import itertools
ss=[shared_suffix(keys[i],keys[j]) for i,j in itertools.combinations(range(len(keys)),2)]
print(f"    pairwise shared-suffix bits: mean={sum(ss)/len(ss):.2f} max={max(ss)}  (random ~1.0; big => common master tail)")

# ---------- LCG recovery on the position sequence (consecutive run 1..70) ----------
print("\n=== [3] LCG recovery from consecutive positions (puzzles 1..70) ===")
run=[k for p,b,k in rows if p<=70]
runb=[b for p,b,k in rows if p<=70]
# common integer representation: scale position u to width B
for B in (16,24,32,40):
    s=[ (( (k-2**(b-1))*(1<<B))//(2**(b-1)) ) for k,b in zip(run,runb)]  # floor(u*2^B)
    dd=[s[i+1]-s[i] for i in range(len(s)-1)]
    zz=[dd[i+1]*dd[i-1]-dd[i]*dd[i] for i in range(1,len(dd)-1)]
    g=0
    for z in zz: g=gcd(g,z)
    # a modulus near 2^B (within a few bits) would be a hit
    hit = g!=0 and abs(g).bit_length()>=B-3 and abs(g).bit_length()<=B+2
    print(f"    B={B}: recovered gcd/modulus bit-length={ (abs(g).bit_length() if g else 0) }  "
          f"{'<== plausible LCG modulus!' if hit else '(no consistent modulus)'}")

# ---------- residual 'noise' autocorrelation (position, consecutive) ----------
print("\n=== [4] is the position 'noise' actually white? (consecutive 1..70) ===")
u=[(k-2**(b-1))/2**(b-1) for k,b in zip(run,runb)]
mu=sum(u)/len(u); uc=[x-mu for x in u]; den=sum(x*x for x in uc)
worst=max(range(1,10), key=lambda L: abs(sum(uc[i]*uc[i+L] for i in range(len(uc)-L))/den))
acf=sum(uc[i]*uc[i+worst] for i in range(len(uc)-worst))/den
print(f"    strongest autocorr over lags1-9: lag{worst} r={acf:+.3f}  (white 95% band +/-{2/math.sqrt(len(u)):.3f})")
