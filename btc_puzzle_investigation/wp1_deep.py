"""WP1 deep test (the deferred one): the n*Q identity with a REAL DL-distance,
not the coarse min_x proxy that failed. Identity (verified by WP1):
    n*Q - (n+k)*A = r*G,   A=2^(N-1)*G,   r = n*D - (2^(N-1)*k mod n)
Key questions:
  1. How does |r| (the detectable DL-distance) SCALE with N?
  2. Is it below the plain-kangaroo cost 2^(N/2)?  If not, the identity gives
     NO leverage and the WP1 distinguisher provably cannot beat plain search.
Exact integers; r computed straight from the exact (n,k,D) columns."""
import csv, math
from collections import defaultdict
from puzzle_kangaroo_distributed import P, G, add, mul

def neg(Pt): return None if Pt is None else (Pt[0], (-Pt[1]) % P)
def sub(a,b): return add(a, neg(b))

# --- 1. verify the point identity on a sample (curve ops) ---
print("=== 1. verify identity  n*Q - (n+k)*A = r*G  on a sample ===")
ok=0; tot=0
rows_by_bits=defaultdict(list)
with open('constructed_keys_1to160_100k_exact.csv') as f:
    for row in csv.DictReader(f):
        N=int(row['bits'])
        try:
            n=int(row['n_exact']); k=int(row['k_exact']); D=int(row['D_exact']); d=int(row['d'])
        except: continue
        rows_by_bits[N].append((d,n,k,D))
for N in [16,24,32,48,64]:
    for (d,n,k,D) in rows_by_bits[N][:3]:
        A=mul(1<<(N-1)); Q=mul(d)
        r = n*D - ((1<<(N-1))*k % n)
        lhs = sub(mul(n,Q), mul((n+k)%(1<<300), A))  # n*Q-(n+k)*A
        rhs = mul(r % (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141), G) if r>=0 else neg(mul(-r,G))
        tot+=1; ok+= (lhs==rhs)
print(f"  identity holds on {ok}/{tot} sampled keys")

# --- 2. scaling of |r| vs N (from exact columns, no curve ops) ---
print("\n=== 2. |r| bit-length vs N  (detectable DL-distance) ===")
print(f"  {'N':>4} {'median |r| bits':>16} {'N/2 (kangaroo)':>15} {'leverage?':>10}")
slope_pts=[]
for N in sorted(rows_by_bits):
    if N<8 or len(rows_by_bits[N])<20: continue
    rb=[]
    for (d,n,k,D) in rows_by_bits[N]:
        r = n*D - ((1<<(N-1))*k % n)
        rb.append(abs(r).bit_length())
    rb.sort(); med=rb[len(rb)//2]
    if N in (16,24,32,48,64,80,100,120,140,160):
        lev = "YES" if med < N/2 else "no"
        print(f"  {N:>4} {med:>16} {N/2:>15.1f} {lev:>10}")
    slope_pts.append((N, med))

# linear fit median|r|_bits ~ slope*N
xs=[n for n,_ in slope_pts]; ys=[b for _,b in slope_pts]
mx=sum(xs)/len(xs); my=sum(ys)/len(ys)
slope=sum((x-mx)*(y-my) for x,y in zip(xs,ys))/sum((x-mx)**2 for x in xs)
print(f"\n  fit: median |r| bits ~ {slope:.3f} * N   (kangaroo exponent = 0.500)")
print(f"  => {'r-search BEATS kangaroo (LEVERAGE!)' if slope<0.5 else 'r-search is LARGER than plain kangaroo 2^(N/2) => NO leverage'}")

# --- 3. how often is |r| within a laptop-feasible bound (2^40)? ---
print("\n=== 3. fraction of keys with |r| < 2^40 (bounded-DL recoverable) per band ===")
for N in (24,32,48,64,80,100,120):
    if N not in rows_by_bits: continue
    frac=sum(1 for (d,n,k,D) in rows_by_bits[N]
             if abs(n*D-((1<<(N-1))*k%n)).bit_length()<40)/len(rows_by_bits[N])
    print(f"  N={N:>4}: {frac*100:5.1f}%  (these are already trivially small keys)")
