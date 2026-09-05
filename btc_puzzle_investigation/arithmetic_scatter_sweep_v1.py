#!/usr/bin/env python3
"""
delta-sweep for PREREG_subrayleigh_deficit_arithmetic_scatter_v5.md over the FROZEN schedule
(PREREG_..._v5_SCHEDULE.txt, SHA a4b4f005...). Measures ONLY delta per curve (the spectral
statistic); the frozen §3 statistics/controls run in a separate analysis stage AFTER this.

Signal path EXACT: reuses the FROZEN instrument's ec_add/compute_MU/char_weight/null_weight
verbatim (subrayleigh_deficit_scaling_v1.py) so every delta is method-identical to the scaling
run. The ONLY generalization is the curve constant c (twist): y^2 = x^3 + c, c = 7*g^k mod p.
Sanctioned float carve-out: the p×p FFT magnitude only (Sec.8). complex128 only.

Resumable: one JSONL row per (role,p,k); re-running skips completed rows. Memory-hygienic.
Phases run PRIMARY-first: 1=surface (all cyclic twists at >=4-cyclic primes; feeds f-hat + H2),
2=trajectory (base curve k=0 at base-cyclic primes; feeds H1 residual). H3 is a separate script.
"""
import numpy as np, math, sys, json, time, gc, hashlib
import subrayleigh_deficit_scaling_v1 as INSTR   # FROZEN signal-path functions

OUT = "arithmetic_scatter_sweep_v1_results.jsonl"
SCHED = "PREREG_subrayleigh_deficit_arithmetic_scatter_v5_SCHEDULE.txt"
DATA  = "cyclicity_screen_v1_data.txt"

def Kfor(p):  # identical to the frozen instrument
    return 300 if p<500 else 200 if p<2000 else 100 if p<5000 else 50

# ---- twist-aware curve construction (only generalization vs the frozen instrument) ----
def canonical_generator_c(p, n, c):
    fac = INSTR.prime_factors(n)
    for x in range(p):
        rhs = (x*x*x + c) % p
        for y in range(p):
            if (y*y) % p == rhs:
                P = (x, y)
                if all(INSTR.scalar_mul(P, n//l, p) is not None for l in fac) \
                   and INSTR.scalar_mul(P, n, p) is None:
                    return P
                break
    raise RuntimeError(f"no order-{n} generator for c={c} at p={p}")

def all_points_c(p, n, c):
    G = canonical_generator_c(p, n, c)
    pts=[]; P=G
    for d in range(1, n):
        pts.append(P); P = INSTR.ec_add(P, G, p)
    assert P is None, "n*G must be O"
    return G, pts

def measure_delta(p, n, c, K):
    """delta for y^2=x^3+c over F_p, method-identical to INSTR.run_prime. Null seed scheme
    shared with the instrument (p*10**6+k) so a c=7 curve reproduces the frozen run byte-for-byte."""
    G, pts = all_points_c(p, n, c)
    gc0 = INSTR.char_weight(n)
    M_char, ss_char = INSTR.compute_MU(pts, gc0, p)
    Ms = np.empty(K)
    for k in range(1, K+1):
        gk = INSTR.null_weight(pts, n, seed=(p*10**6 + c*97 + k))  # c-salted so twists get independent nulls
        Ms[k-1], _ = INSTR.compute_MU(pts, gk, p)
    mu = Ms.mean(); sd = Ms.std(ddof=1)
    res = dict(n=n, c=c, G=list(G), M_char=M_char, ss_char=ss_char,
               mu=mu, sdM=sd, D=(mu-M_char)/mu, z=(M_char-mu)/sd,
               SE_D=sd/(mu*math.sqrt(K)), K=K,
               parseval_relerr=abs(ss_char-p*p*(n-1))/(p*p*(n-1)))
    del pts, gc0
    return res

# ---- schedule / screen parsing ----
def load_schedule():
    S={}
    for line in open(SCHED):
        line=line.strip()
        if line.startswith("SURFACE_PRIMES="): S["surface"]=[int(x) for x in line.split("=",1)[1].split(",") if x]
        if line.startswith("TRAJECTORY_PRIMES="): S["traj"]=[int(x) for x in line.split("=",1)[1].split(",") if x]
    return S

def load_screen():
    from collections import defaultdict
    perp=defaultdict(list)
    for line in open(DATA):
        if line.startswith("#"): continue
        left,right=line.split("|"); p=int(left.split()[0])
        k,c,n,a,M,cyc=map(int,right.split())
        perp[p].append(dict(k=k,c=c,n=n,a=a,M=M,cyc=cyc))
    return perp

def done_set():
    d=set()
    try:
        for line in open(OUT):
            r=json.loads(line); d.add((r["p"],r["k"]))
    except FileNotFoundError: pass
    return d

def emit(fh, roles, p, k, r):
    row=dict(roles=roles,p=p,k=k,**r); fh.write(json.dumps(row)+"\n"); fh.flush()
    return row

def main():
    sched=load_schedule(); perp=load_screen(); done=done_set()
    # Each distinct curve (p,k) is measured ONCE; the analysis assigns roles. A base curve that is
    # both a surface prime's k=0 (H2 slope) and a trajectory k=0 (residual) is the SAME delta -> one measurement.
    surf=set(sched["surface"]); traj=set(sched["traj"])
    work={}   # (p,k) -> (p, twist_dict, roles)
    for p in sched["surface"]:
        for t in perp[p]:
            if t["cyc"]:
                key=(p,t["k"]); work.setdefault(key,[p,t,[]]); work[key][2].append("surface")  # f-hat(k!=0)+H2(all)
    for p in sched["traj"]:
        t0=[t for t in perp[p] if t["k"]==0]
        if t0 and t0[0]["cyc"]:
            key=(p,0); work.setdefault(key,[p,t0[0],[]]); work[key][2].append("trajectory")
    # PRIMARY-first deterministic order: by (p, k)
    ordered=[work[k] for k in sorted(work.keys())]
    todo=[w for w in ordered if (w[0],w[1]["k"]) not in done]
    total=len(ordered); remaining=len(todo)
    print(f"[sweep] distinct curve-measurements={total}  done={total-remaining}  remaining={remaining}",flush=True)

    fh=open(OUT,"a",buffering=1)
    t_start=time.time()
    for i,(p,t,roles) in enumerate(todo):
        K=Kfor(p); t0=time.time()
        try:
            r=measure_delta(p,t["n"],t["c"],K); r["secs"]=round(time.time()-t0,1); r["a"]=t["a"]; r["M"]=t["M"]
            emit(fh,sorted(set(roles)),p,t["k"],r)
            el=time.time()-t_start; rate=(i+1)/el
            eta=(remaining-(i+1))/rate/3600 if rate>0 else 0
            print(f"[{i+1}/{remaining}] p={p:>5} k={t['k']} a={t['a']:+5d} roles={'+'.join(sorted(set(roles)))[:12]} "
                  f"D={r['D']:+.3e} z={r['z']:+6.2f} E1={r['parseval_relerr']:.0e} "
                  f"({r['secs']}s)  ETA~{eta:.1f}h",flush=True)
        except MemoryError:
            print(f"    p={p} k={t['k']} MemoryError — SKIPPED",flush=True)
        except Exception as e:
            print(f"    p={p} k={t['k']} ERROR {type(e).__name__}: {e}",flush=True)
        gc.collect()
    fh.close(); print(f"[sweep] PHASE done in {(time.time()-t_start)/3600:.2f}h",flush=True)

if __name__=="__main__":
    main()
