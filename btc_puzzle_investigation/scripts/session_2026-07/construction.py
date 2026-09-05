"""
Focus on the CONSTRUCTION of an N-bit key = forced top bit + (N-1) random low bits.
Extract the low-bit residuals r_N = d_N - 2^(N-1), reconstruct the consumed-bit
STREAM in puzzle order (the alignment my earlier bit-column BM missed), and test
whether that stream is a single deterministic PRNG output (Berlekamp-Massey linear
complexity + frequency/runs). Small puzzles = start of the stream, fully used.
"""
import csv, math

rows=[]
with open('/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/puzzles_verified.csv') as f:
    for r in csv.DictReader(f): rows.append((int(r['puzzle']),int(r['bits']),int(r['private_key'],16)))
rows.sort()
d={p:k for p,b,k in rows}

# ---- [0] single-master low-bit mask hypothesis: is d_N mod 2^(N-1) consistent? ----
print("=== [0] single-master test: are low bits shared across keys? ===")
Mbits={}  # inferred bit -> value, detect conflict
conflict=None
for p in range(1,71):
    if p not in d: continue
    r=d[p]-2**(p-1)
    for bit in range(p-1):
        b=(r>>bit)&1
        if bit in Mbits and Mbits[bit]!=b and conflict is None:
            conflict=(bit,p)
        Mbits.setdefault(bit,b)
print(f"    first bit-conflict between keys: {conflict}  -> low bits are INDEPENDENT per key (no shared master)")

# ---- [1] reconstruct consumed-bit stream in puzzle order ----
def stream(order_lsb_first):
    bits=[]
    for p in range(1,71):
        if p not in d: continue
        r=d[p]-2**(p-1); w=p-1
        seq=[(r>>b)&1 for b in range(w)]           # LSB..MSB
        if not order_lsb_first: seq=seq[::-1]
        bits+=seq
    return bits

def berlekamp_massey(s):
    n=len(s); C=[0]*n; B=[0]*n; C[0]=1; B[0]=1; L=0; m=1
    for i in range(n):
        dd=s[i]
        for j in range(1,L+1): dd^=C[j]&s[i-j]
        if dd==0: m+=1
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

def runs_test(s):
    n=len(s); ones=sum(s); pi=ones/n
    if abs(pi-0.5)>= (2/math.sqrt(n)): return None,pi  # freq fails, runs undefined
    R=1+sum(1 for i in range(1,n) if s[i]!=s[i-1])
    exp=2*n*pi*(1-pi)+1; var=2*n*pi*(1-pi)*(2*n*pi*(1-pi)-1)/(n-1) if n>1 else 1
    z=(R-exp)/math.sqrt(var) if var>0 else 0
    return z,pi

print("\n=== [1] consumed-bit STREAM tests (puzzles 1..70 in order) ===")
for lsb in (True,False):
    s=stream(lsb); L=berlekamp_massey(s); z,pi=runs_test(s)
    print(f"    order={'LSB-first' if lsb else 'MSB-first'}: len={len(s)}  ones-frac={pi:.3f}  "
          f"linear_complexity={L} (random~{len(s)//2})  runs-z={z if z is None else round(z,2)}")

# random baseline for stream linear complexity
import random as _r
_r.seed(0)
base=[berlekamp_massey([_r.randint(0,1) for _ in range(2415)]) for _ in range(20)]
print(f"    [random baseline] LC mean={sum(base)/len(base):.0f} over len-2415 sequences")

# ---- [2] show the residuals explicitly for small puzzles ----
print("\n=== [2] low-bit residuals r_N = d_N - 2^(N-1) (the 'random' part) ===")
for p in range(1,17):
    if p in d:
        r=d[p]-2**(p-1); print(f"    N={p:2d}: d={d[p]:5d}  top-bit + r={r:<5d} = {r:0{max(1,p-1)}b}")
