#!/usr/bin/env python3
"""Complete the scatter sweep for p=11959 (the single missing prime)."""
import numpy as np, math, json, time, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import subrayleigh_deficit_scaling_v1 as INSTR

OUT = "arithmetic_scatter_sweep_v1_results.jsonl"

# p=11959 cyclic twists from cyclicity screen
# k=0 c=7 n=11991 cyclic=1
# k=2 c=63 n=11757 cyclic=1
# k=3 c=189 n=11929 cyclic=1
# k=5 c=1701 n=12163 cyclic=1
twists = [(0, 7, 11991), (2, 63, 11757), (3, 189, 11929), (5, 1701, 12163)]
p = 11959
K = 50  # Kfor(11959)

results = []
for k, c, n in twists:
    t0 = time.time()
    fac = INSTR.prime_factors(n)
    G = None
    for x in range(p):
        rhs = (x*x*x + c) % p
        for y in range(p):
            if (y*y) % p == rhs:
                P = (x, y)
                if all(INSTR.scalar_mul(P, n//l, p) is not None for l in fac) \
                   and INSTR.scalar_mul(P, n, p) is None:
                    G = P
                break
        if G:
            break
    if G is None:
        print(f"  p={p} k={k}: NO GENERATOR FOUND", flush=True)
        continue
    pts = []
    P = G
    for d in range(1, n):
        pts.append(P)
        P = INSTR.ec_add(P, G, p)
    gc0 = INSTR.char_weight(n)
    M_char, ss_char = INSTR.compute_MU(pts, gc0, p)
    Ms = np.empty(K)
    for j in range(1, K+1):
        gk = INSTR.null_weight(pts, n, seed=(p*10**6 + c*97 + j))
        Ms[j-1], _ = INSTR.compute_MU(pts, gk, p)
    mu = Ms.mean()
    sd = Ms.std(ddof=1)
    D = (mu - M_char) / mu
    SE_D = sd / (mu * math.sqrt(K))
    elapsed = time.time() - t0
    print(f"  p={p} k={k} c={c} n={n}: D={D:.6e} SE_D={SE_D:.3e} ({elapsed:.1f}s)",
          flush=True)
    row = {
        "role": "none", "p": p, "k": k, "c": c, "n": n,
        "G": list(G), "M_char": M_char, "ss_char": ss_char,
        "mu": float(mu), "sdM": float(sd), "D": float(D),
        "z": float((M_char - mu) / sd), "SE_D": float(SE_D), "K": K,
        "parseval_relerr": float(abs(ss_char - p*p*(n-1)) / (p*p*(n-1)))
    }
    results.append(row)
    del pts

# Append to existing results
with open(OUT, "a") as f:
    for r in results:
        f.write(json.dumps(r) + "\n")

total = sum(1 for _ in open(OUT))
print(f"Appended {len(results)} rows. Total now: {total}", flush=True)
