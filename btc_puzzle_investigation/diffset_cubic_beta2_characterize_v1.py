#!/usr/bin/env python3
# Characterize the beta^2 (class 2) excess in E3(real). Frozen design:
# PREREG_diffset_cubic_beta2_characterization_v1.md. Exact integer path; matched MT null;
# MC-corrected via null of max|z|. Descriptive, no verdict.
import csv, random, statistics
from gmpy2 import mpz, powmod

P    = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
BETA = 0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee
E3EXP=(P-1)//3
BASE = "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation"
random.seed(20260727)

def cc(z):
    r=int(powmod(mpz(z%P),E3EXP,P)); return 0 if r==1 else (1 if r==BETA else 2)
def band(b): return 0 if b<=40 else (1 if b<=80 else 2)   # L,M,H
BN={(0,0):'LL',(1,1):'MM',(2,2):'HH',(0,1):'LM',(0,2):'LH',(1,2):'MH'}

def analyze(xs, bands):
    n=len(xs); bkt={k:0 for k in BN.values()}; pk=[0]*n; tot=[0,0,0]
    for j in range(n):
        bj=bands[j]; xj=xs[j]
        for k in range(j+1,n):
            cl=cc(xj-xs[k]); tot[cl]+=1
            if cl==2:
                bkt[BN[tuple(sorted((bj,bands[k])))]]+=1
                pk[j]+=1; pk[k]+=1
    return tot, bkt, pk, statistics.pvariance(pk)

# ---- real ----
real=[]
with open(f"{BASE}/solved_puzzles_xy.csv") as f:
    for r in csv.DictReader(f): real.append((int(r["bits"]),int(r["X"],16)))
real.sort(key=lambda t:t[0])
bands=[band(b) for b,_ in real]; xs=[x for _,x in real]; bits=[b for b,_ in real]
BSIZE={k:0 for k in BN.values()}
for j in range(82):
    for k in range(j+1,82): BSIZE[BN[tuple(sorted((bands[j],bands[k])))]]+=1
tot,bkt,pk,disp=analyze(xs,bands)
print(f"REAL (a,b,c)={tuple(tot)}  beta2=class2={tot[2]} (excess {tot[2]-1107:+d})", flush=True)
print(f"bucket sizes: {BSIZE}", flush=True)
print(f"REAL beta2 per bucket (frac): "+"  ".join(f"{k}={bkt[k]}/{BSIZE[k]}({bkt[k]/BSIZE[k]:.3f})" for k in ['LL','MM','HH','LM','LH','MH']), flush=True)
print(f"REAL per-key beta2: mean={statistics.mean(pk):.2f} var(disp)={disp:.2f} max={max(pk)}", flush=True)
top=sorted(range(82),key=lambda i:-pk[i])[:5]
print(f"REAL top-5 beta2 keys (bit,count,z vs Bin(81,1/3) m27 sd4.24): "
      +", ".join(f"(b{bits[i]},{pk[i]},{(pk[i]-27)/4.243:+.1f})" for i in top), flush=True)

# ---- null (MT, bit-matched) ----
pool={}
with open(f"{BASE}/constructed_keys_1to160_100k.csv") as f:
    for r in csv.DictReader(f):
        bb=int(r["bits"]); pool.setdefault(bb,[]).append(int(r["X"],16))
NT=3000
nb={k:[] for k in BN.values()}; nd=[]; nmax=[]
for _ in range(NT):
    cx=[random.choice(pool[b]) for b in bits]
    _,bb,pp,dp=analyze(cx,bands)
    for k in BN.values(): nb[k].append(bb[k])
    nd.append(dp); nmax.append(max(pp))
# per-bucket null mean/sd, real z, percentile
print(f"\nNULL (MT, {NT} resamples) — per-bucket beta2:", flush=True)
means={};sds={}
for k in ['LL','MM','HH','LM','LH','MH']:
    m=statistics.mean(nb[k]); s=statistics.pstdev(nb[k]); means[k]=m; sds[k]=s
    z=(bkt[k]-m)/s if s>0 else 0
    pct=sum(1 for v in nb[k] if v<=bkt[k])/NT*100
    print(f"  {k}: real={bkt[k]}  null {m:.1f}±{s:.1f}  z={z:+.2f}  pctile={pct:.1f}", flush=True)
# MC-corrected: null of max|z| across 6 buckets
def maxz(counts):
    return max(abs((counts[k]-means[k])/sds[k]) if sds[k]>0 else 0 for k in BN.values())
null_maxz=sorted(maxz({k:nb[k][i] for k in BN.values()}) for i in range(NT))
real_maxz=maxz(bkt)
p_maxz=sum(1 for v in null_maxz if v>=real_maxz)/NT
print(f"\nMC-corrected bucket test: real max|z|={real_maxz:.2f}  null max|z| 95%={null_maxz[int(0.95*NT)]:.2f}  p(max|z|)={p_maxz:.3f}", flush=True)
# dispersion (concentration) test
nd.sort(); dpct=sum(1 for v in nd if v<=disp)/NT*100
print(f"\nCONCENTRATION: real per-key var={disp:.2f}  null var {statistics.mean(nd):.2f} (97.5%={nd[int(0.975*NT)]:.2f})  real pctile={dpct:.1f}", flush=True)
# hottest-key test (MC)
nmax.sort(); mk_p=sum(1 for v in nmax if v>=max(pk))/NT
print(f"HOTTEST KEY: real max per-key={max(pk)}  null max-per-key 95%={nmax[int(0.95*NT)]}  p={mk_p:.3f}", flush=True)
print(f"\nVERDICT-FREE READ: "
      f"buckets {'DIFFUSE (max|z| within null)' if p_maxz>0.05 else 'a bucket exceeds MC null'};  "
      f"per-key {'DIFFUSE (dispersion+hottest within null)' if dpct<97.5 and mk_p>0.05 else 'concentrated'}", flush=True)
