#!/usr/bin/env python3
"""PILOT for the x=3 sector at p=163 -- the INVERTED enumeration.

x = #{v in T : 8 | v}.  x=3 leaves FOUR non-coarse speeds.  Forward enumeration is
C(567,4) ~ 4.2e9 and infeasible, so invert: enumerate the COARSE side, C(81,3) = 85320.

KEY SIMPLIFICATION (from the proved cap table, CAP_TABLE_UNIFORM_v1.md): a coarse speed
covers a class ALL-OR-NOTHING.  So a coarse triple partitions the 163 classes into covered
and MISSED -- there are no partially covered classes -- and every one of the 4 targets of
every missed class must come from the four non-coarse speeds.

This PILOT measures cost only; it decides nothing.  Integer/bitmask arithmetic throughout;
timing uses perf_counter_ns (integer nanoseconds).  No float anywhere.
Usage: x3_sector_pilot_v1.py <n_triples> <seed>
"""
import sys, random
from time import perf_counter_ns
from itertools import combinations

N, H, p = 1304, 652, 163
FULLC = (1 << p) - 1

def covers(j, v): 
    r = (j * v) % N
    return r < p or r > N - p
def v2(v):
    e = 0
    while v % 2 == 0: v //= 2; e += 1
    return e

speeds    = [v for v in range(1, H + 1) if v % p != 0]
noncoarse = [v for v in speeds if v2(v) < 3]
coarse_w  = list(range(1, H // 8 + 1))

# B[v][t] = bitmask over classes r=1..163 where speed v covers target r + 163 t
B = {}
for v in noncoarse:
    bs = [0, 0, 0, 0]
    for i, r in enumerate(range(1, p + 1)):
        for t in range(4):
            if covers(r + p * t, v): bs[t] |= 1 << i
    B[v] = bs
CM = {}
for w in coarse_w:
    m = 0
    for i, r in enumerate(range(1, p + 1)):
        if covers(r, 8 * w): m |= 1 << i
    CM[w] = m

# who[t][i] = list of non-coarse speeds covering target t of class index i
who = [[[] for _ in range(p)] for _ in range(4)]
for v in noncoarse:
    for t in range(4):
        m = B[v][t]
        while m:
            b = m & -m; i = b.bit_length() - 1
            who[t][i].append(v); m ^= b

nodes = 0
def search(M, cov, depth, used):
    """cov = [4 masks] of covered (class,t).  Need cov[t] ⊇ M for all t, using <= 4 speeds."""
    global nodes
    nodes += 1
    rem_t = -1; rem_i = -1
    for t in range(4):
        r = M & ~cov[t]
        if r: rem_t = t; rem_i = (r & -r).bit_length() - 1; break
    if rem_t < 0: return list(used)
    if depth == 4: return None
    for v in who[rem_t][rem_i]:
        if v in used: continue
        nc = [cov[t] | B[v][t] for t in range(4)]
        got = search(M, nc, depth + 1, used + [v])
        if got: return got
    return None

if __name__ == "__main__":
    ntri = int(sys.argv[1]); seed = int(sys.argv[2])
    rng = random.Random(seed)
    trips = [tuple(sorted(rng.sample(coarse_w, 3))) for _ in range(ntri)]
    tot_nodes = 0; tot_ns = 0; found = 0; msizes = []
    for w1, w2, w3 in trips:
        M = FULLC & ~(CM[w1] | CM[w2] | CM[w3])
        msizes.append(bin(M).count("1"))
        nodes = 0
        t0 = perf_counter_ns()
        got = search(M, [0, 0, 0, 0], 0, [])
        tot_ns += perf_counter_ns() - t0
        tot_nodes += nodes
        if got: found += 1
    msizes.sort()
    print(f"PILOT x=3 at p=163, inverted.  {ntri} random coarse triples, seed {seed}.")
    print(f"  |M| (classes missed by the coarse triple): min {msizes[0]} "
          f"median {msizes[len(msizes)//2]} max {msizes[-1]}   (U_min(3) = 58)")
    print(f"  total search nodes {tot_nodes}   per triple {tot_nodes//ntri}")
    print(f"  total time {tot_ns//10**6} ms   per triple {tot_ns//ntri//1000} us")
    print(f"  coarse triples with a 4-speed non-coarse completion FOUND: {found}/{ntri}")
    proj_ns = (tot_ns // ntri) * 85320
    print(f"  PROJECTED full run over C(81,3) = 85320 triples: "
          f"{proj_ns//10**9} s = {proj_ns//(10**9 * 60)} min")
