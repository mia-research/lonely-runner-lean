"""ADVERSARIAL kill: rerun the identical timestamp-window search against RANDOM
target keys (same intervals). If random targets produce the same rate of '2-hit'
configs as the real keys did, the ts=1421348975 hit is chance, not an engine."""
import csv, random

known={}
with open('/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/puzzles_verified.csv') as f:
    for r in csv.DictReader(f): known[int(r['puzzle'])]=int(r['private_key'],16)
CHECK=[p for p in known if 8<=p<=45]; NMAX=45
B_TIME=1421345234

def gen(seed):
    rng=random.Random(seed); out={1:1}
    for i in range(2,NMAX+1): out[i]=(1<<(i-1))|rng.randrange(0,1<<(i-1))
    return out
def scan(target):
    c2=0; best=0; bestcfg=None
    for seed in range(B_TIME-4000,B_TIME+4001):
        s=gen(seed); hits=[p for p in CHECK if s[p]==target[p]]
        if len(hits)>=2: c2+=1
        if len(hits)>best: best=len(hits); bestcfg=(seed,hits)
    return c2,best,bestcfg

# real targets
c2,best,cfg=scan(known)
print(f"REAL targets:  configs with >=2 hits = {c2}   best config = {cfg} ({best} hits)")

# null targets: random keys in the same intervals
rng=random.Random(0)
print("NULL targets (random keys, same intervals):")
tot=[]
for t in range(8):
    nt={p:(1<<(p-1))|rng.randrange(0,1<<(p-1)) for p in known}
    c2n,bestn,cfgn=scan(nt)
    tot.append(c2n)
    print(f"  trial{t}: configs with >=2 hits = {c2n}   best = {bestn} hits {cfgn}")
print(f"\nnull mean #(>=2-hit configs) = {sum(tot)/len(tot):.1f}")
print("VERDICT: real is at the null rate  ->  ts=1421348975 hit is CHANCE, no engine recovered"
      if c2<=max(tot)+1 else "real EXCEEDS null -> investigate")
