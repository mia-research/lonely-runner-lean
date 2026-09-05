#!/usr/bin/env python3
"""S2 re-test — p-scaling of the sub-Rayleigh mean|U| deficit.
Executes PREREG_subrayleigh_deficit_scaling_v1.md (frozen SHA 93c95471...).

Signal path EXACT: EC group law over F_p in Python int; point coords exact int in [0,p);
character/index arithmetic exact int mod n / mod p. Sanctioned float carve-out: unit-modulus
roots of unity read from a table indexed by the EXACT integer (Sec.8). Anchored by E1 (exact
Parseval integer identity) and the common-mode-cancellation argument.
"""
import numpy as np, math, sys, json, time

# ---------------- exact EC over F_p, y^2 = x^3 + 7 ----------------
def ec_add(P, Q, p):
    if P is None: return Q
    if Q is None: return P
    x1,y1 = P; x2,y2 = Q
    if x1==x2 and (y1+y2)%p==0: return None
    if P==Q:
        # slope = (3 x1^2) / (2 y1)   -- exact modular inverse
        num = (3*x1*x1) % p
        den = (2*y1) % p
    else:
        num = (y2-y1) % p
        den = (x2-x1) % p
    lam = (num * pow(den, p-2, p)) % p          # exact mod-inverse (p prime)
    x3 = (lam*lam - x1 - x2) % p
    y3 = (lam*(x1-x3) - y1) % p
    return (x3, y3)

def prime_factors(n):
    f=set(); d=2; m=n
    while d*d<=m:
        while m%d==0: f.add(d); m//=d
        d+=1
    if m>1: f.add(m)
    return f

def canonical_generator(p, n):
    fac = prime_factors(n)
    # iterate points in (x, then y) order; first point of order n
    for x in range(p):
        rhs = (x*x*x + 7) % p
        # y with y^2 = rhs
        for y in range(p):
            if (y*y)%p == rhs:
                P = (x,y)
                # order n  <=>  (n/l)P != O for all primes l|n   (group cyclic order n)
                if all(scalar_mul(P, n//l, p) is not None for l in fac):
                    # and nP == O
                    if scalar_mul(P, n, p) is None:
                        return P
                break  # only need the smaller y; if it isn't order n, next x
    raise RuntimeError("no generator found")

def scalar_mul(P, k, p):
    R=None; Q=P
    while k>0:
        if k&1: R=ec_add(R,Q,p)
        Q=ec_add(Q,Q,p); k>>=1
    return R

def all_points(p, n):
    """[(x_d,y_d) for d=1..n-1], exact ints, via repeated addition of canonical G."""
    G = canonical_generator(p, n)
    pts=[]; P=G
    for d in range(1, n):
        pts.append(P)          # P = [d]G
        P = ec_add(P, G, p)
    assert P is None, "n*G must be O"     # after loop P=[n]G=O
    return G, pts

# ---------------- the M functional (mean|U|) ----------------
def compute_MU(pts, g, p):
    """M = mean_{b,c}|U(b,c)|, U=fft2(W), W[x,y]=g weighting the point (x,y).
       Returns (mean|U|, sum|U|^2). g is a complex array indexed by d-1."""
    W = np.zeros((p,p), dtype=np.complex128)
    xs = np.fromiter((x for x,_ in pts), dtype=np.int64, count=len(pts))
    ys = np.fromiter((y for _,y in pts), dtype=np.int64, count=len(pts))
    np.add.at(W, (xs, ys), g)          # points distinct => simple scatter
    U = np.fft.fft2(W)
    aU = np.abs(U)
    return aU.mean(), float((aU*aU).sum())

def char_weight(n):
    """g(d)=exp(2pi i (a0 d)/n), a0=1, index EXACT int d (=d since 1<=d<=n-1)."""
    d = np.arange(1, n)
    return np.exp(2j*np.pi*(d % n)/n)

def null_weight(pts, n, seed):
    """Hermitian matched null: g(n-d)=conj(g(d)). Index d = position+1."""
    rng = np.random.default_rng(seed)
    g = np.zeros(n-1, dtype=np.complex128)      # index i = d-1, d=1..n-1
    for d in range(1, n):
        i = d-1
        if g[i] != 0: continue
        j = (n-d) - 1
        if d == n-d:                            # fixed point (n even): real +-1
            g[i] = rng.choice([-1.0, 1.0])
        else:
            phi = rng.uniform(0, 2*np.pi)
            g[i] = np.exp(1j*phi)
            g[j] = np.conj(g[i])
    return g

# ---------------- per-prime driver ----------------
def run_prime(p, n, K, seed0=None, want_null_samples=False):
    G, pts = all_points(p, n)
    gc = char_weight(n)
    M_char, ss_char = compute_MU(pts, gc, p)
    Ms = np.empty(K)
    for k in range(1, K+1):
        gk = null_weight(pts, n, seed=p*10**6 + k)
        Ms[k-1], _ = compute_MU(pts, gk, p)
    mu = Ms.mean(); sd = Ms.std(ddof=1)
    D = (mu - M_char)/mu
    z = (M_char - mu)/sd
    SE_D = sd/(mu*math.sqrt(K))
    out = dict(p=p, n=n, G=G, M_char=M_char, ss_char=ss_char,
               mu=mu, sdM=sd, D=D, z=z, SE_D=SE_D,
               parseval_target=p*p*(n-1),
               parseval_relerr=abs(ss_char-p*p*(n-1))/(p*p*(n-1)))
    if want_null_samples: out["null_M"]=Ms.tolist()
    return out

PRIMES = [151,193,211,241,277,349,397,433,523,619,691,823,937,1093,1249,
   1471,1693,1987,2281,2671,3169,3607,4177,4861,5647,6571,7639,8893,10357,12043]
ORDERS = [133,219,199,259,273,313,397,397,489,669,651,829,973,1137,1303,
   1501,1729,2037,2203,2569,3073,3577,4303,4771,5529,6411,7699,9037,10173,12261]
def Kfor(p): return 300 if p<500 else 200 if p<2000 else 100 if p<5000 else 50

# ---------------- full sweep (incremental JSONL) ----------------
if __name__=="__main__" and len(sys.argv)>1 and sys.argv[1]=="full":
    outpath = "subrayleigh_deficit_scaling_v1_results.jsonl"
    done=set()
    try:
        for line in open(outpath): done.add(json.loads(line)["p"])
    except FileNotFoundError: pass
    fh=open(outpath,"a",buffering=1)
    for p,n in zip(PRIMES,ORDERS):
        if p in done:
            print(f"p={p} already done, skip", flush=True); continue
        t0=time.time()
        try:
            r=run_prime(p,n,K=Kfor(p))
            r["K"]=Kfor(p); r["secs"]=round(time.time()-t0,1)
            r["G"]=list(r["G"])
            fh.write(json.dumps(r)+"\n")
            print(f"p={p:>6} n={n:>6} K={Kfor(p):>3}  D={r['D']:+.3e} z={r['z']:+6.2f} "
                  f"E1relerr={r['parseval_relerr']:.1e}  ({r['secs']}s)", flush=True)
        except MemoryError:
            print(f"p={p} MemoryError — SKIPPED (see DEVIATIONS compute fallback)", flush=True)
        except Exception as e:
            print(f"p={p} ERROR {type(e).__name__}: {e}", flush=True)
    fh.close(); print("=== full sweep done ===", flush=True)
    sys.exit(0)

# ---------------- smoke test at p=151 ----------------
if __name__=="__main__" and (len(sys.argv)<2 or sys.argv[1]=="smoke"):
    print("=== SMOKE TEST — p in {151,211,349}, K=200 ===")
    for p,n in [(151,133),(211,199),(349,313)]:
        t0=time.time()
        r=run_prime(p,n,K=200,want_null_samples=True)
        # E1: Parseval exact integer identity
        print(f"\np={p} n={n}  G={r['G']}  ({time.time()-t0:.1f}s)")
        print(f"  E1 Parseval  sum|U|^2={r['ss_char']:.1f}  target={r['parseval_target']}  "
              f"relerr={r['parseval_relerr']:.2e}  {'PASS' if r['parseval_relerr']<1e-6 else 'FAIL'}")
        print(f"  M_char={r['M_char']:.6f}  mu_null={r['mu']:.6f}  sdM={r['sdM']:.3e}")
        print(f"  D={r['D']:+.6e}  z={r['z']:+.3f}  SE_D={r['SE_D']:.3e}")
        # planted control at delta=1e-3 on a fresh null spectrum: |V|=(1-delta)|U0|
        Ms=np.array(r['null_M'])
        for delta in [5e-4,1e-3,2e-3]:
            M_plant=(1-delta)*r['mu']              # a target deficit of exactly delta vs the same mu
            zp=(M_plant-r['mu'])/r['sdM']
            print(f"    planted delta={delta:.0e}: implied z={zp:+.2f} "
                  f"({'FIRES' if abs(zp)>=3 else 'weak'})")
