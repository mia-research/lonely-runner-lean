#!/usr/bin/env python3
"""
Collision-graph + k-structure analysis  (follow-up to the p=0.0015 consecutive-n
signal, 2026-07-11).  Build (i): map ALL shared-n structure among solved keys and
ask whether shared-n keys also share/relate k -- which would pin the CELL (n,k),
not just the denominator, i.e. supply the §C ~14 bits.

Exact throughout (best_nk pure int).  Descriptive dump first; formal null in v2
once the pattern is seen.
"""
import csv
from collections import defaultdict
from math import gcd
from knd_common import best_nk

MASTER = "btc_puzzle_master_exact.csv"

solved = []
with open(MASTER) as fh:
    for r in csv.DictReader(fh):
        if r["status"] != "SOLVED":
            continue
        solved.append((int(r["puzzle"]), int(r["bits"]), int(r["priv_dec"])))
solved.sort()

nk = {}      # puzzle -> (n, k)
for p, N, d in solved:
    nk[p] = best_nk(d, N)

# ---- full collision graph: group puzzles by shared denominator n ----------
groups = defaultdict(list)
for p, N, d in solved:
    n, k = nk[p]
    groups[n].append((p, k, N))

print("=== shared-n groups (denominator appears >=2x) ===")
for n in sorted(groups):
    g = groups[n]
    if len(g) < 2:
        continue
    idxs = [p for p, _, _ in g]
    ks   = [k for _, k, _ in g]
    print(f"n={n:4d}  x{len(g)}  puzzles={idxs}")
    print(f"          k       ={ks}")
    print(f"          k mod n dist to 0/n edges, k/n as pos:")
    for p, k, N in g:
        print(f"            #{p:3d} (bits {N:3d}): k={k:4d}  k/n≈{k}/{n}  gcd(k,n)={gcd(k,n)}")

# ---- consecutive-puzzle-index collisions (the p=0.0015 signal) ------------
print("\n=== consecutive-index n-collisions (adjacent puzzle numbers, same n) ===")
ps = sorted(nk)
for i in range(len(ps) - 1):
    a, b = ps[i], ps[i + 1]
    if b == a + 1 and nk[a][0] == nk[b][0]:
        (na, ka), (nb, kb) = nk[a], nk[b]
        print(f"  #{a}->#{b}: n={na}  k: {ka} -> {kb}  "
              f"Δk={kb-ka}  gcd(ka,kb)={gcd(ka,kb) if ka and kb else 0}")

# ---- runs: maximal blocks of consecutive puzzle indices sharing n ---------
print("\n=== maximal consecutive-index runs with constant n ===")
run = [ps[0]]
def flush(run):
    if len(run) >= 2 and all(nk[p][0] == nk[run[0]][0] for p in run):
        n = nk[run[0]][0]
        ks = [nk[p][1] for p in run]
        print(f"  puzzles {run}: n={n}  k={ks}  Δk={[ks[j+1]-ks[j] for j in range(len(ks)-1)]}")
for i in range(1, len(ps)):
    if ps[i] == run[-1] + 1 and nk[ps[i]][0] == nk[run[0]][0]:
        run.append(ps[i])
    else:
        flush(run); run = [ps[i]]
flush(run)

# ---- is n a simple function of puzzle index / bits? -----------------------
print("\n=== n vs puzzle index (looking for index-coupling / a formula) ===")
for p, N, d in solved:
    n, k = nk[p]
    print(f"  #{p:3d} bits={N:3d}  n={n:4d}  k={k:4d}", end="")
    print(f"   n|?  index%n={p % n if n else 0}  bits%n={N % n if n else 0}")
