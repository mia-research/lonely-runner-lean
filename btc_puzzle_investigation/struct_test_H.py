#!/usr/bin/env python3
"""
struct_test_H.py  —  Plan v5 Test H: is the jump-map graph glued-tree-like?

Quantum walks beat classical hitting times only on specially-structured graphs
(e.g. glued trees). The classical question, answerable without any quantum
hardware: does the kangaroo jump map form such a structured graph, or a generic
random-function graph (no exploitable structure, no quantum leverage)?

Build the functional graph on M scalar nodes:  f(x) = (x + jump(xG)) mod M, where
jump(xG) = jumps[(xG).X % K].  Compute f for all nodes by INCREMENTAL point
addition (M adds, not M mults). Then compare its rho/component statistics to a
true random function on M nodes (Flajolet-Odlyzko: rho ~ sqrt(pi*M/8), cyclic
nodes ~ sqrt(pi*M/2), components ~ 0.5*ln M). A glued-tree graph would look
NOTHING like this (balanced bipartite trees, a bottleneck, hitting time not
~sqrt(M)). Match to random-function => unstructured => no quantum-walk leverage.

Usage: python3 struct_test_H.py
"""
import secrets, math, random
from puzzle_kangaroo import add, G

def build_pointX(M):
    """pointX[x] = X-coord of (x+1)*G for x in 0..M-1, via incremental addition."""
    xs = [0] * M; Pt = None
    for x in range(M):
        Pt = add(Pt, G); xs[x] = Pt[0]
    return xs

def jump_map(M, K, jumps, pointX):
    return [(x + jumps[pointX[x] % K]) % M for x in range(M)]

def graph_stats(f, M, samples=4000):
    """Sample rho = tail+cycle length from random starts; count cyclic nodes & components exactly."""
    # rho sampling
    rhos = []
    for _ in range(samples):
        seen = {}; x = secrets.randbelow(M); t = 0
        while x not in seen:
            seen[x] = t; x = f[x]; t += 1
        rhos.append(t)                                   # tail+cycle length to first repeat
    # exact: cyclic nodes and components via iterative coloring
    color = [0] * M          # 0=unseen,1=in progress,2=done
    cyclic = 0; comps = 0
    on_cycle = [False] * M
    for s in range(M):
        if color[s]:
            continue
        path = []; x = s
        while color[x] == 0:
            color[x] = 1; path.append(x); x = f[x]
        if color[x] == 1:                                # found a new cycle
            comps += 1
            # mark cycle nodes: from x around until back to x
            c = x
            while not on_cycle[c]:
                on_cycle[c] = True; cyclic += 1; c = f[c]
        for n in path:
            color[n] = 2
    mean_rho = sum(rhos) / len(rhos)                     # noqa: float (reported diagnostic)
    return mean_rho, cyclic, comps

def mean_sd(v):
    m = sum(v) / len(v)                                          # noqa: float (diagnostic)
    s = (sum((x - m) ** 2 for x in v) / len(v)) ** 0.5           # noqa: float
    return m, s

def ensemble(M, K, ENS):
    """ENS jump-map draws (varying jump constants) and ENS random-function controls.
    pointX (the curve part) is built ONCE; only the K jump constants vary per draw."""
    pointX = build_pointX(M)
    jm_cyc = []; jm_cmp = []; rf_cyc = []; rf_cmp = []
    for s in range(ENS):
        random.seed(1000 + s)
        jumps = [1 + random.randrange(M - 1) for _ in range(K)]
        fj = jump_map(M, K, jumps, pointX)
        _, cy, cp = graph_stats(fj, M, samples=1500)
        jm_cyc.append(cy); jm_cmp.append(cp)
        random.seed(50000 + s)
        fr = [random.randrange(M) for _ in range(M)]
        _, cy2, cp2 = graph_stats(fr, M, samples=1500)
        rf_cyc.append(cy2); rf_cmp.append(cp2)
    return jm_cyc, jm_cmp, rf_cyc, rf_cmp

def main():
    K = 16; ENS = 10
    print(f"# TEST H  jump-map functional graph vs random function   ENSEMBLE ({ENS} draws each)")
    print("# Flajolet-Odlyzko random-function: cyclic~sqrt(pi*M/2), comps~0.5*lnM")
    print("# glued-tree would be ~1 component + huge rho + bottleneck (nothing like F-O).\n")
    for M in (65521, 131063):                                   # two primes: scale check
        exp_cyc = math.sqrt(math.pi * M / 2); exp_comp = 0.5 * math.log(M)
        jc, jp, rc, rp = ensemble(M, K, ENS)
        jcm, jcs = mean_sd(jc); jpm, jps = mean_sd(jp)
        rcm, rcs = mean_sd(rc); rpm, rps = mean_sd(rp)
        print(f"  M={M} (prime):  F-O expects cyclic~{exp_cyc:.0f}, comps~{exp_comp:.1f}")
        print(f"    JUMP-MAP :  cyclic {jcm:6.1f} +/- {jcs:4.1f}   comps {jpm:5.2f} +/- {jps:4.2f}")
        print(f"    RANDOM-FN:  cyclic {rcm:6.1f} +/- {rcs:4.1f}   comps {rpm:5.2f} +/- {rps:4.2f}")
        # overlap check on cyclic count
        sep = abs(jcm - rcm) / ((jcs**2 + rcs**2) ** 0.5 + 1e-9)  # noqa: float (diagnostic)
        print(f"    cyclic separation: {sep:.2f} sigma  (<2 => same distribution)\n")
    print("  read: jump-map cyclic/comps overlapping the random-function ensemble (within ~2 sigma)")
    print("        and both near F-O => generic random-function graph, NOT glued-tree. Same at both M")
    print("        => scale-invariant. A persistent >2-sigma gap growing with M would be real structure.")

if __name__ == "__main__":
    main()
