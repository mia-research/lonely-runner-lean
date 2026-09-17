import math, random
n = 8
def circ(x):
    f = x - math.floor(x); return min(f, 1-f)

def run(ds, maxsteps=400):
    m = min(ds); t = 1.0/(n*m); seq=[]
    for step in range(maxsteps):
        inway=[d for d in ds if circ(d*t) < 1.0/n]
        if not inway: return seq, True
        best=None
        for d in inway:
            N=round(d*t); nxt=(N+1.0/n)/d
            if nxt>t and (best is None or nxt>best[0]): best=(nxt,d,N)
        if best is None: return seq, False
        nxt,d,N=best
        seq.append((d,N,(d*t-N)+1.0/n)); t=nxt
    return seq, False

def min_delta_ge4(ds):
    seq, arrived = run(ds)
    if not arrived: return None          # only count cascades that actually arrive
    last={}; best=None
    for idx,(d,N,delta) in enumerate(seq):
        if d in last and idx-last[d]-1 >= 4:
            if best is None or delta<best: best=delta
        last[d]=idx
    return best

ds = [3.687981, 16.495804, 22.081819, 26.56833, 30.110766, 36.378981, 38.828022]
cur = min_delta_ge4(ds)
print(f"start delta : {cur:.4e}")
rng = random.Random(11)
for scale in (1e-3, 1e-5, 1e-7, 1e-9, 1e-11):
    for _ in range(40000):
        i = rng.randrange(7)
        cand = list(ds); cand[i] += rng.gauss(0, scale)
        if cand[i] <= 0: continue
        cand = sorted(cand)
        v = min_delta_ge4(cand)
        if v is not None and v < cur: ds, cur = cand, v
    print(f"  after refining at scale {scale:.0e} : delta = {cur:.4e}")
print()
print(f"final delta : {cur:.4e}   (cascade ARRIVES; only arriving cascades were counted)")
print(f"double precision floor is ~1e-16, so this is {abs(math.log10(cur))-16:.0f} orders clear of noise"
      if cur>0 else "")
