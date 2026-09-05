#!/usr/bin/env python3
# Executes PREREG_spectral_decomp_v1.md
# Pairwise cubic-character matrix C (82x82), SVD, σ_max vs null -- BOTH cells (secp, E').
# Asks: is E3's null on E' a TRUE null, or hiding coherent structure in a non-uniform mode?

import csv, json, random, time
import numpy as np
try:
    from gmpy2 import mpz, powmod
    def chi3(z):
        r = int(powmod(mpz(z % P), (P-1)//3, P))
        return 0 if r==1 else (1 if r==BETA else (2 if r==BETA2 else -1))
    FAST=True
except Exception:
    def chi3(z):
        r = pow(z % P, (P-1)//3, P)
        return 0 if r==1 else (1 if r==BETA else (2 if r==BETA2 else -1))
    FAST=False

BASE = "/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation"
P    = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F
BETA = 0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee
BETA2= pow(BETA,2,P)
# map class -> complex cube root: 0 -> 1, 1 -> ω, 2 -> ω²
W  = np.exp(2j*np.pi/3)
CL2Z = np.array([1.0+0j, W, W*W], dtype=complex)

def C_matrix(xs):
    """82x82 complex matrix C[i,j] = χ₃(X_i - X_j) as cube root of unity, 0 on diagonal."""
    n = len(xs)
    C = np.zeros((n,n), dtype=complex)
    for i in range(n):
        xi = xs[i]
        for j in range(i+1, n):
            cl = chi3((xi - xs[j]) % P)
            if cl < 0:
                raise ValueError("χ₃ undefined (z=0)")
            z = CL2Z[cl]
            C[i,j] = z
            C[j,i] = np.conj(z)   # χ₃(-1)=1 ⇒ C[j,i] = conj(C[i,j]) (real-equivalent Hermitian)
    return C

def sigma_max(C):
    return float(np.linalg.svd(C, compute_uv=False)[0])

def allones_proj(C):
    """|1ᵀ C 1| / n² : the all-ones projection (ties to E3)."""
    n = C.shape[0]
    v = np.ones(n) / np.sqrt(n)
    return abs(v @ C @ v)

def sigma_max_orth(C):
    """σ_max of C after projecting out the all-ones mode."""
    n = C.shape[0]
    u = np.ones(n) / np.sqrt(n)
    # project C onto the orthogonal complement: C⊥ = C - u (uᵀ C) - (C u) uᵀ ... no:
    # we want the operator on u⊥. Use P = I - u uᵀ, compute P C P, take its σ_max.
    P = np.eye(n) - np.outer(u, u)
    Cp = P @ C @ P
    return float(np.linalg.svd(Cp, compute_uv=False)[0])

# ---- real 82, both cells ----
real=[]
with open(f"{BASE}/solved_puzzles_xy.csv") as f:
    for r in csv.DictReader(f): real.append((int(r["bits"]), int(r["X"],16)))
real.sort(key=lambda t:t[0])
xs_secp=[x for _,x in real]
real_E=[]
with open(f"{BASE}/solved_puzzles_xy_Eprime.csv") as f:
    for r in csv.DictReader(f): real_E.append((int(r["bits"]), int(r["X_Eprime"],16)))
real_E.sort(key=lambda t:t[0])
xs_Eprime=[x for _,x in real_E]
real_bits=[bb for bb,_ in real]
assert len(xs_secp)==82 and len(xs_Eprime)==82

# ---- constructed pools, both cells ----
def load_pool(col):
    pool={}
    fname = "constructed_keys_Eprime_100k.csv" if col=="X_Eprime" else "constructed_keys_1to160_100k.csv"
    with open(f"{BASE}/{fname}") as f:
        for r in csv.DictReader(f):
            if not r[col]: continue
            pool.setdefault(int(r["bits"]),[]).append(int(r[col],16))
    return pool
pool_secp   = load_pool("X")
pool_Eprime = load_pool("X_Eprime")
for b in real_bits:
    assert b in pool_secp and len(pool_secp[b])>0
    assert b in pool_Eprime and len(pool_Eprime[b])>0

def build_null(pool, N=10000, seed=20260730):
    random.seed(seed)
    sigs=[]; ones=[]; orth=[]
    for _ in range(N):
        xs=[random.choice(pool[b]) for b in real_bits]
        C=C_matrix(xs)
        sigs.append(sigma_max(C))
        ones.append(allones_proj(C))
        orth.append(sigma_max_orth(C))
    return np.array(sigs), np.array(ones), np.array(orth)

# ===== FREEZE NULLS (both cells) -- reuse if frozen npy exists =====
import os
def load_or_build(path, pool, tag):
    if os.path.exists(path):
        arr = np.load(path)
        print(f"  loaded existing {tag} null from {os.path.basename(path)}", flush=True)
        return arr[:,0], arr[:,1], arr[:,2]
    print(f"  building {tag} null (10000 resamples, seed 20260730, fast={FAST})...", flush=True)
    t0=time.time()
    out = build_null(pool)
    print(f"  {tag} null built in {time.time()-t0:.1f}s", flush=True)
    return out
print(f"=== NULLS (both cells) ===", flush=True)
sigs_s, ones_s, orth_s = load_or_build(f"{BASE}/spectral_decomp_frozen_null_secp_v1.npy",   pool_secp,   "secp")
sigs_E, ones_E, orth_E = load_or_build(f"{BASE}/spectral_decomp_frozen_null_Eprime_v1.npy", pool_Eprime, "E'")
print(f"  secp: σ_max mean={sigs_s.mean():.2f} (MP pred ~{2*np.sqrt(82):.2f})", flush=True)
print(f"  E'  : σ_max mean={sigs_E.mean():.2f} (MP pred ~{2*np.sqrt(82):.2f})", flush=True)

def region(arr):
    s=np.sort(arr); n=len(s)
    return float(s[249]), float(s[9750]), float(s.mean())  # alpha ~ 0.05 (NO int cast -- sigma is continuous)
Ls,Us,ms = region(sigs_s); LE,UE,mE = region(sigs_E)
print(f"\nfrozen regions (σ_max, alpha~0.05):", flush=True)
print(f"  secp: [L,U]=[{Ls},{Us}]  mean={ms:.2f}", flush=True)
print(f"  E'  : [L,U]=[{LE},{UE}]  mean={mE:.2f}", flush=True)

# save (only if not already frozen)
if not os.path.exists(f"{BASE}/spectral_decomp_frozen_null_secp_v1.npy"):
    np.save(f"{BASE}/spectral_decomp_frozen_null_secp_v1.npy",   np.stack([sigs_s,ones_s,orth_s],axis=1))
if not os.path.exists(f"{BASE}/spectral_decomp_frozen_null_Eprime_v1.npy"):
    np.save(f"{BASE}/spectral_decomp_frozen_null_Eprime_v1.npy", np.stack([sigs_E,ones_E,orth_E],axis=1))

# ===== REAL 82, both cells =====
print(f"\n=== REAL 82 ===", flush=True)
C_s = C_matrix(xs_secp);   sm_s=sigma_max(C_s);   ao_s=allones_proj(C_s);   so_s=sigma_max_orth(C_s)
C_E = C_matrix(xs_Eprime); sm_E=sigma_max(C_E);   ao_E=allones_proj(C_E);   so_E=sigma_max_orth(C_E)

def decide(val, arr, L, U):
    ge=sum(1 for v in arr if v>=val); le=sum(1 for v in arr if v<=val)
    p=min((ge+1)/(len(arr)+1),(le+1)/(len(arr)+1))*2
    pct=le/len(arr)*100
    if L is None or U is None:
        d="n/a (diagnostic)"
    else:
        d="REJECT-HIGH" if val>U else ("REJECT-LOW" if val<L else "FAIL-TO-REJECT")
    return d,p,pct,ge,le

print(f"\n--- secp ---", flush=True)
for name,val,arr,L,U in [("σ_max",sm_s,sigs_s,Ls,Us),("σ_max_⊥",so_s,orth_s,None,None),("|1ᵀC1|/n",ao_s,ones_s,None,None)]:
    d,p,pct,ge,le = decide(val,arr,L,U)
    print(f"  {name:10s} real={val:.3f}  null_mean={np.mean(arr):.3f}  pct={pct:5.1f}  p={p:.4f}  {d}", flush=True)
print(f"\n--- E' ---", flush=True)
for name,val,arr,L,U in [("σ_max",sm_E,sigs_E,LE,UE),("σ_max_⊥",so_E,orth_E,None,None),("|1ᵀC1|/n",ao_E,ones_E,None,None)]:
    d,p,pct,ge,le = decide(val,arr,L,U)
    print(f"  {name:10s} real={val:.3f}  null_mean={np.mean(arr):.3f}  pct={pct:5.1f}  p={p:.4f}  {d}", flush=True)

# ===== CONTROLS =====
print(f"\n=== CONTROLS ===", flush=True)
# planted-coherent: pick k=10 random keys, force their mutual χ₃ to ω
def planted_C(pool, k=10, force_class=1):
    xs=[random.choice(pool[b]) for b in real_bits]
    C=C_matrix(xs)
    idx=list(range(82)); random.shuffle(idx); block=idx[:k]
    z=CL2Z[force_class]
    for a_i in range(k):
        for b_i in range(a_i+1,k):
            C[block[a_i],block[b_i]]=z
            C[block[b_i],block[a_i]]=np.conj(z)
    return C
random.seed(12345)
# planted power sweep: find minimum detectable block size k, then verify power>=0.9 at some k
print(f"  planted power vs block size k (target power>=0.9 at some k):", flush=True)
for cell,(pool,arr,U) in [("secp",(pool_secp,sigs_s,Us)),("E'",(pool_Eprime,sigs_E,UE))]:
    line=f"    {cell}: "
    for k in [10, 20, 30, 40, 50]:
        rej=0; N=300
        for _ in range(N):
            if sigma_max(planted_C(pool,k=k))>U: rej+=1
        line += f"k={k}:{rej/N:.2f}  "
    print(line, flush=True)

# ===== DECISION MATRIX =====
d_s,_,_,_,_ = decide(sm_s,sigs_s,Ls,Us)
d_E,_,_,_,_ = decide(sm_E,sigs_E,LE,UE)
print(f"\n########## FOUR-WAY DECISION ##########", flush=True)
print(f"  secp σ_max: {d_s}   (real {sm_s:.2f} vs null mean {ms:.2f})", flush=True)
print(f"  E'   σ_max: {d_E}   (real {sm_E:.2f} vs null mean {mE:.2f})", flush=True)
print(f"\nE3 cross-reference: secp E3=13125 (REJECT-HIGH, p~0.033); E' E3=3711 (FAIL-TO-REJECT, p~0.66)", flush=True)

# save meta
meta={"secp":{"sigma_max":sm_s,"sigma_max_orth":so_s,"allones":ao_s,"null_mean":ms,
              "L":Ls,"U":Us,"decision":d_s},
      "Eprime":{"sigma_max":sm_E,"sigma_max_orth":so_E,"allones":ao_E,"null_mean":mE,
                "L":LE,"U":UE,"decision":d_E},
      "P":P,"BETA":BETA,"seed":20260730,"N_null":10000,
      "Eprime_a":1,"Eprime_b":1,
      "Eprime_j":"44822744220896591776866187745298544975459348902828605434628742196609871486028"}
with open(f"{BASE}/spectral_decomp_meta_v1.json","w") as f: json.dump(meta,f,indent=2)
print(f"\nwrote spectral_decomp_meta_v1.json", flush=True)
