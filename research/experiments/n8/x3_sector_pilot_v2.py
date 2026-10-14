#!/usr/bin/env python3
"""PILOT v2 for the x=3 sector at p=163 -- inverted enumeration with the pair-type structure
used as a BRANCHING/PRUNING rule rather than a post-hoc filter (the move
docs/HANDOVER_2026_09_07b.md sec 6.1 names as untried).

Two additions over v1, both derived from the PROVED cap table (CAP_TABLE_UNIFORM_v1.md):

 [P1] DEFICIENCY PRUNE.  Every non-coarse speed covers AT MOST 2 of the 4 targets of any
      class.  So with (4 - d) speeds left, every class of M must already have at least
      4 - 2(4-d) targets covered.  At d = 3 that is "every class of M has >= 2 covered",
      checked in 11 bitwise ops via
          atleast2 = OR over pairs s<t of (cov[s] & cov[t]);   prune if M & ~atleast2.
      This fires immediately before the widest (fourth) branching level.
 [P2] MRV BRANCHING.  Branch on the uncovered (class, target) with the FEWEST covering
      speeds, not the lowest index.

Completeness: [P1] only removes states that provably cannot be completed within the
remaining budget, and [P2] reorders branches without discarding any, so the search still
decides the sector.  Integer/bitmask only; timing in integer nanoseconds.  No float.
Usage: x3_sector_pilot_v2.py <n_triples> <seed>
"""
import sys, random
from time import perf_counter_ns
from itertools import combinations
sys.path.insert(0, "experiments/n8")
from x3_sector_pilot_v1 import B, CM, who, noncoarse, coarse_w, FULLC, p

NCOV = [[len(who[t][i]) for i in range(p)] for t in range(4)]
nodes = 0

def search(M, cov, depth, used):
    global nodes
    nodes += 1
    # [P1] deficiency prune
    if depth == 3:
        c0, c1, c2, c3 = cov
        at2 = (c0&c1)|(c0&c2)|(c0&c3)|(c1&c2)|(c1&c3)|(c2&c3)
        if M & ~at2: return None
    # [P2] MRV: pick the uncovered (class,target) with fewest candidate speeds
    best = None; bestn = 1 << 30
    for t in range(4):
        rem = M & ~cov[t]
        while rem:
            b = rem & -rem; i = b.bit_length() - 1; rem ^= b
            n = NCOV[t][i]
            if n < bestn: bestn = n; best = (t, i)
            if n <= 1: break
        if bestn <= 1: break
    if best is None: return list(used)
    if depth == 4: return None
    t, i = best
    for v in who[t][i]:
        if v in used: continue
        nc = [cov[k] | B[v][k] for k in range(4)]
        got = search(M, nc, depth + 1, used + [v])
        if got: return got
    return None

if __name__ == "__main__":
    ntri, seed = int(sys.argv[1]), int(sys.argv[2])
    rng = random.Random(seed)
    trips = [tuple(sorted(rng.sample(coarse_w, 3))) for _ in range(ntri)]
    tn = 0; tns = 0; found = 0; ms = []
    for w1, w2, w3 in trips:
        M = FULLC & ~(CM[w1] | CM[w2] | CM[w3])
        ms.append(bin(M).count("1"))
        nodes = 0
        t0 = perf_counter_ns()
        got = search(M, [0,0,0,0], 0, [])
        tns += perf_counter_ns() - t0
        tn += nodes
        if got: found += 1
    ms.sort()
    print(f"PILOT v2 x=3 at p=163, inverted + pair-type pruning. {ntri} triples, seed {seed}.")
    print(f"  |M| missed by the coarse triple: min {ms[0]} median {ms[len(ms)//2]} max {ms[-1]}"
          f"   (U_min(3) = 58)")
    print(f"  nodes total {tn}  per triple {tn//ntri}")
    print(f"  time {tns//10**6} ms  per triple {tns//ntri//1000} us")
    print(f"  triples with a 4-speed non-coarse completion FOUND: {found}/{ntri}")
    proj = (tns // ntri) * 85320
    print(f"  PROJECTED full C(81,3)=85320 run: {proj//10**9} s = {proj//(10**9*60)} min"
          f" = {proj//(10**9*3600)} h")
