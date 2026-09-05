#!/usr/bin/env python3
"""
kfold_gate_demo_Azero_v1.py — the REAL v35 'A==0' candidate, run through kfold_gate.

masked_structure_findings_v35: "A == 0 on the curve" looked enriched in-sample
(8/27, matched-null p=0.002) and died out-of-sample (1 vs 1.07, p=0.66). The
manual guard split by a RANGE boundary. This re-runs the SAME frozen hypothesis
using the real orbit E-values, but partitions the selected primes by SHA-256
(magnitude-blind) and applies the both-folds emission rule automatically.

Frozen hypothesis H_A (unchanged, read from _A_zero_matched_null_v1.py):
   at p != 3 mod 8 with NE even, P(A == 0) EXCEEDS the matched-null rate.
Population = usable primes in [LO,HI) meeting that selection. The gate splits THAT
population by hash into discovery/validation and emits only if BOTH clear alpha.

Signal path integer-only: the matched null resamples fair +-1 sign assignments on
each prime's E-orbit multiset (exactly _A_zero_matched_null_v1.matched_null's
model); float appears only in the printed p-value. Usage:
   python kfold_gate_demo_Azero_v1.py [LO HI B ALPHA SEED]
"""
import random
import sys

from sympy import isprime

from _A_zero_matched_null_v1 import orbit_data
from kfold_gate_v1 import KFoldGate, fold_of


def scan(lo, hi):
    """Selected population: (p, E-orbit +-1 values) for p!=3 mod 8 with NE even."""
    sel = []
    for p in range(lo, hi):
        if p % 6 != 1 or not isprime(p) or p == 7:
            continue
        r = orbit_data(p)
        if r is None:
            continue
        if r["pmod8"] != 3 and len(r["E"]) % 2 == 0:
            sel.append((p, tuple(r["E"])))
    return sel


def zero_count_pvalue(primes, emap, B, seed):
    """Integer matched-null p-value for 'A==0 enriched' over `primes`.
    observed = #{primes with sum(E)==0}; hits = #null draws with >= observed zeros,
    each draw reassigning fair +-1 signs to every prime's E-orbit."""
    observed = sum(1 for p in primes if sum(emap[p]) == 0)
    per = [len(emap[p]) for p in primes]
    rng = random.Random(seed)
    hits = 0
    for _ in range(B):
        z = 0
        for k in per:
            if sum(1 if rng.getrandbits(1) else -1 for _ in range(k)) == 0:
                z += 1
        if z >= observed:
            hits += 1
    return observed, hits, B


def main():
    lo = int(sys.argv[1]) if len(sys.argv) > 1 else 100
    hi = int(sys.argv[2]) if len(sys.argv) > 2 else 9000
    B = int(sys.argv[3]) if len(sys.argv) > 3 else 4000
    alpha = sys.argv[4] if len(sys.argv) > 4 else "0.01"
    seed = int(sys.argv[5]) if len(sys.argv) > 5 else 7

    print("=" * 78)
    print(f"REAL 'A==0' candidate through kfold_gate  —  window [{lo},{hi})  B={B}")
    print("=" * 78)
    print("scanning primes (p=1 mod 6, p!=3 mod 8, NE even) ...")
    sel = scan(lo, hi)
    emap = dict(sel)
    primes = [p for p, _ in sel]
    print(f"  selected population: {len(primes)} primes")

    # (1) POOLED — no split. This is the number the range-era test reported.
    obs, hits, trials = zero_count_pvalue(primes, emap, B, seed=1000)
    print("\n[pooled, no split]")
    print(f"  A==0 observed = {obs}/{len(primes)}   matched-null p = {hits/trials:.4g}"  # noqa: float
          f"  ({hits}/{trials})")

    # (2) GATE — deterministic hash split, both folds must clear alpha.
    gate = KFoldGate(alpha=alpha, K=2, seed=seed)
    res = gate.run(primes,
                   lambda f, sub: zero_count_pvalue(sub, emap, B, seed=2000 + f)[1:])
    print("\n[kfold_gate, SHA-256 2-fold, magnitude-blind]")
    # annotate observed per fold for transparency
    for fo in res.folds:
        sub = [p for p in primes if fold_of(p, seed, 2) == fo.fold]
        o = sum(1 for p in sub if sum(emap[p]) == 0)
        print(f"    fold {fo.fold}: A==0 observed = {o}/{len(sub)}")
    print(res.render())

    print("\n" + "-" * 78)
    if res.emit:
        print("VERDICT: gate EMITS — the A==0 enrichment held in BOTH hash folds.")
    else:
        print("VERDICT: gate SUPPRESSES — enrichment did not replicate across both")
        print("hash folds. A pooled/in-sample p-value alone is not a claim (v35 lesson).")


if __name__ == "__main__":
    main()
