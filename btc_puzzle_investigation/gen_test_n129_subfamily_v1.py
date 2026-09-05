#!/usr/bin/env python3
"""
n=129 sub-family test  (banked live thread, 2026-07-11)
-------------------------------------------------------
Claim from session: solved-key best-approx denominators n cluster on a small
generating set more than the Farey measure allows -- concretely, puzzles
58/59/60 (three CONSECUTIVE puzzle indices) all had n=129.  If real, that is a
GENERATION-level (n,k) sub-family = a region-forbidding constraint (the kind that
actually cuts the kangaroo search), not a distribution marginal.

This test:
  (0) EXACT-decomposition sanity: recompute n for every solved key from priv_dec
      via knd_common.best_nk (pure int, no-float rule) and print the n=129 run.
  (1) Matched Farey baseline: for each solved puzzle, the null draws d uniformly
      in that puzzle's exact bit-range [2^(N-1), 2^N) and takes best_nk.  This is
      the CORRECT baseline (real keys follow the Farey measure, not uniform-n).
  (2) Statistics vs the null (exact permutation/resample p-values):
        - consecutive-index n-collisions  (the 58/59/60 signal)
        - total same-n pairs              (any clustering)
        - max n-multiplicity              (a dominant denominator)
      Reported on the full solved set AND on the N>=20 subset (where n has real
      freedom; low-bit puzzles force small n in both data and null, so they wash
      out of the p-value -- but we separate them to be sure the signal isn't just
      the tiny-range end).

No floating point in the signal path: best_nk and all counts are exact ints;
p-values are integer resample fractions.
"""
import csv, random
from collections import Counter
from knd_common import best_nk

MASTER = "btc_puzzle_master_exact.csv"
POOL   = 4000     # per-bit-length Farey sample pool
R      = 200000   # resamples for the null
SEED   = 20260711

# ---- load solved keys (exact) --------------------------------------------
solved = []   # (puzzle, bits, d)
with open(MASTER) as fh:
    for r in csv.DictReader(fh):
        if r["status"] != "SOLVED":
            continue
        solved.append((int(r["puzzle"]), int(r["bits"]), int(r["priv_dec"]),
                       r.get("n_exact", "")))
solved.sort()

# ---- (0) exact decomposition + sanity vs stored n_exact ------------------
obs = []      # (puzzle, bits, n)
mismatches = 0
for p, N, d, n_stored in solved:
    n, k = best_nk(d, N)
    obs.append((p, N, n))
    if n_stored not in ("", None):
        digits = n_stored.split(".")[0].strip()   # exact int parse, no float
        if digits.lstrip("-").isdigit() and int(digits) != n:
            mismatches += 1

print(f"solved keys: {len(obs)}   bit range: "
      f"{min(N for _,N,_ in obs)}..{max(N for _,N,_ in obs)}")
print(f"exact-vs-stored n_exact mismatches: {mismatches}")

# the claimed run
run = [(p, n) for (p, N, n) in obs if p in (58, 59, 60)]
print("puzzles 58/59/60 exact n:", run)
n_counts = Counter(n for _, _, n in obs)
rep = {v: c for v, c in n_counts.items() if c >= 2}
print("repeated n (exact, full set):", dict(sorted(rep.items())))

# ---- (1) build matched Farey null pools, one per bit-length --------------
random.seed(SEED)
bitlens = sorted({N for _, N, _ in obs})
pools = {}
for N in bitlens:
    lo, hi = 1 << (N - 1), 1 << N
    if hi - lo <= POOL:            # tiny range: enumerate exactly
        ds = range(lo, hi)
    else:
        ds = (random.randrange(lo, hi) for _ in range(POOL))
    pools[N] = [best_nk(d, N)[0] for d in ds]

# ---- statistics ----------------------------------------------------------
def consec_collisions(seq):        # seq = list of (puzzle, n)
    return sum(1 for i in range(len(seq) - 1)
               if seq[i + 1][0] == seq[i][0] + 1 and seq[i + 1][1] == seq[i][1])

def total_pairs(ns):
    return sum(m * (m - 1) // 2 for m in Counter(ns).values())

def max_mult(ns):
    return max(Counter(ns).values())

def run_battery(subset):
    ns  = [n for (_, _, n) in subset]
    seq = [(p, n) for (p, _, n) in subset]
    obs_stat = dict(consec=consec_collisions(seq),
                    pairs=total_pairs(ns),
                    maxmult=max_mult(ns))
    ge = dict(consec=0, pairs=0, maxmult=0)
    for _ in range(R):
        sim = [random.choice(pools[N]) for (_, N, _) in subset]
        simseq = [(subset[i][0], sim[i]) for i in range(len(subset))]
        if consec_collisions(simseq) >= obs_stat["consec"]:  ge["consec"]  += 1
        if total_pairs(sim)          >= obs_stat["pairs"]:   ge["pairs"]   += 1
        if max_mult(sim)             >= obs_stat["maxmult"]: ge["maxmult"] += 1
    return obs_stat, ge          # ge = integer counts of (null >= observed) out of R

for label, subset in (("FULL", obs),
                      ("N>=20", [t for t in obs if t[1] >= 20])):
    stat, ge = run_battery(subset)
    print(f"\n--- {label} (n={len(subset)}) ---")
    for k in ("consec", "pairs", "maxmult"):
        permille = (1000 * ge[k]) // R          # integer p-value in per-mille
        star = "  <-- signal (p<0.05)" if 20 * ge[k] < R else ""
        print(f"  {k:8s}: observed={stat[k]:4d}   "
              f"p(null>=obs)={ge[k]}/{R} (~{permille}e-3){star}")
