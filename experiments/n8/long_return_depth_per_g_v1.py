import math, random
n = 8
def circ(x):
    f = x - math.floor(x); return min(f, 1-f)
def run(ds, maxsteps=600):
    m=min(ds); t=1.0/(n*m); rows=[]
    for _ in range(maxsteps):
        iw=[d for d in ds if circ(d*t)<1.0/n]
        if not iw: return rows, True
        best=None
        for d in iw:
            N=round(d*t); nxt=(N+1.0/n)/d
            if nxt>t and (best is None or nxt>best[0]): best=(nxt,d,N)
        if best is None: return rows, False
        nxt,d,N=best
        rows.append((d,(d*t-N)+1.0/n)); t=nxt
    return rows, False
def min_delta_at(ds,g):
    rows,arr=run(ds)
    if not arr: return None
    last={}; best=None
    for i,(d,dl) in enumerate(rows):
        if d in last and i-last[d]-1==g:
            if best is None or dl<best: best=dl
        last[d]=i
    return best

rng=random.Random(17)
# STEP 1: harvest seeds -- arrangements that actually exhibit a return at each g
seeds={g:[] for g in range(1,7)}
scanned=0
while scanned < 120000 and any(len(v)<25 for v in seeds.values()):
    ds=sorted(rng.uniform(1,40) for _ in range(7)); scanned+=1
    for g in range(1,7):
        if len(seeds[g])<25:
            v=min_delta_at(ds,g)
            if v is not None: seeds[g].append((v,ds))
print(f"arrangements scanned for seeds: {scanned}")
print(f"seeds found per g: {{{', '.join(f'{g}: {len(seeds[g])}' for g in range(1,7))}}}")
print()
# STEP 2: refine each seed
print(f"{'g':>3} {'seeds':>6} {'best random':>14} {'after refining':>16}")
for g in range(1,7):
    if not seeds[g]:
        print(f"{g:>3} {0:>6} {'-':>14} {'-':>16}"); continue
    rand_best=min(v for v,_ in seeds[g])
    overall=None
    for v0,ds0 in sorted(seeds[g])[:12]:
        ds,cur=list(ds0),v0
        for scale in (1e-2,1e-4,1e-6,1e-8,1e-10):
            for _ in range(4000):
                i=rng.randrange(7); c=list(ds); c[i]+=rng.gauss(0,scale)
                if c[i]<=0: continue
                c=sorted(c); v=min_delta_at(c,g)
                if v is not None and v<cur: ds,cur=c,v
        if overall is None or cur<overall: overall=cur
    print(f"{g:>3} {len(seeds[g]):>6} {rand_best:>14.3e} {overall:>16.3e}")
