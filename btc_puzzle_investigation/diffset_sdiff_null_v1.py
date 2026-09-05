import csv, sys, time, random
import gmpy2
from gmpy2 import mpz

P  = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
Pg = mpz(P)
assert P % 4 == 3
# --- forced-identity sanity: chi2(-1) = -1  (P == 3 mod 4) ---
assert gmpy2.jacobi(mpz(P-1), Pg) == -1, "chi2(-1) should be -1"

CTRL = "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/constructed_keys_1to160_100k.csv"

# real bit-length multiset (public puzzle indices; NOT the test target). 82 distinct values.
REAL_BITS = list(range(1,71)) + [75,80,85,90,95,100,105,110,115,120,125,130]
assert len(REAL_BITS)==82 and len(set(REAL_BITS))==82

# load control pools: bits -> list of mpz X (hex, no 0x prefix)
pools = {}
with open(CTRL) as f:
    r = csv.DictReader(f)
    for row in r:
        b = int(row['bits'])
        xh = row['X'].strip()
        if not xh: raise SystemExit("empty X in control")
        x = int(xh, 16)
        if not (0 < x < P): raise SystemExit(f"control X out of range at bits={b}")
        pools.setdefault(b, []).append(mpz(x))
# freeze pool order (row order) then we index by rng
for b in REAL_BITS:
    if b not in pools: raise SystemExit(f"no control keys for bits={b}")

ORDER = sorted(REAL_BITS)                      # FROZEN ordering: ascending bit-length
poolsz = [len(pools[b]) for b in ORDER]
print("pool sizes along frozen order (bits: size):")
print({b: len(pools[b]) for b in ORDER})
print("forced positions (pool size 1):", [b for b in ORDER if len(pools[b])==1])
print("low-choice (<=512):", [(b,len(pools[b])) for b in ORDER if len(pools[b])<=512])

# --- numerical proof of the forced parts on CONTROL data (8 random x) ---
rng0 = random.Random(12345)
samp = [pools[b][rng0.randrange(len(pools[b]))] for b in ORDER[:8]]
ordered_sum = 0; qr_ordered = 0
for a in range(8):
    for c in range(8):
        if a==c: continue
        d = (samp[a]-samp[c]) % P
        j = gmpy2.jacobi(d, Pg)
        ordered_sum += j
        if j==1: qr_ordered += 1
print(f"[forced check n=8] ordered-pair signed sum = {ordered_sum} (must be 0); "
      f"#QR over ordered pairs = {qr_ordered} (must be C(8,2)=28)")

def sdiff(xs):
    s = 0; zc = 0
    n = len(xs)
    for a in range(n):
        xa = xs[a]
        for c in range(a+1, n):
            d = (xa - xs[c]) % P
            if d == 0:
                zc += 1; continue
            s += gmpy2.jacobi(d, Pg)
    return s, zc

def run(N, seed, fix_low=None):
    rng = random.Random(seed)
    vals = []; ztot = 0; distinct_fail = 0
    for _ in range(N):
        xs = []
        for b in ORDER:
            if fix_low is not None and b in fix_low:
                xs.append(fix_low[b])
            else:
                pl = pools[b]
                xs.append(pl[rng.randrange(len(pl))])
        if len(set(map(int,xs))) != len(xs): distinct_fail += 1
        s, zc = sdiff(xs)
        ztot += zc
        vals.append(s)
    return vals, ztot, distinct_fail

if __name__ == "__main__":
    N = int(sys.argv[1]) if len(sys.argv)>1 else 200
    seed = int(sys.argv[2]) if len(sys.argv)>2 else 20260726
    t=time.time()
    vals, ztot, dfail = run(N, seed)
    dt=time.time()-t
    vals_sorted = sorted(vals)
    import statistics as st
    mean = sum(vals)/len(vals)
    sd = (sum((v-mean)**2 for v in vals)/(len(vals)-1))**0.5
    def nr(p):   # nearest-rank percentile -> integer order statistic (1-based rank ceil(p/100*N))
        import math
        rank = max(1, math.ceil(p/100.0*len(vals_sorted)))
        return vals_sorted[rank-1]
    print(f"\nN={N} seed={seed} time={dt:.1f}s  z=0 events={ztot} distinct_fail={dfail}")
    print(f"parity all-odd? {all(v%2==1 or v%2==-1 for v in vals)}  min={min(vals)} max={max(vals)}")
    print(f"null mean={mean:.3f}  sd={sd:.3f}  (analytic sqrt(3321)={3321**0.5:.3f})")
    print(f"percentiles nearest-rank: 0.5%={nr(0.5)} 2.5%={nr(2.5)} 50%={nr(50)} 97.5%={nr(97.5)} 99.5%={nr(99.5)}")
    # frozen two-sided alpha=0.05 region via order statistics
    L = vals_sorted[249]     # 250th smallest
    U = vals_sorted[9750] if N>=10000 else vals_sorted[int(round(0.9751*N))-1]
    if N>=10000:
        below = sum(1 for v in vals if v < L); above = sum(1 for v in vals if v > U)
        print(f"FROZEN alpha=0.05 region: L=v[250th]={L}  U=v[9751st]={U}")
        print(f"   tail counts: #(null<L)={below}  #(null>U)={above}  (each ~<=250 target)")
