#!/usr/bin/env python3
"""
struct_test_D.py  —  Plan v5 Test D: near/multi-collision information in kangaroo.

Standard kangaroo: only an EXACT tame/wild collision gives d (d = m0 + t_acc - w_acc
at the meet). Question: does a NEAR-collision -- a tame point and a wild point whose
X-coordinates agree in the top b bits but are not equal -- carry partial information
about d? If X-proximity implied scalar-proximity there'd be a ladder/collision
shortcut. Test A said no; this checks it at the collision-detection level.

Setup (solvable width W): tame herd from known m0, wild herd from Q=d*G, shared jump
map P->P+jumpG[X%K], accumulating scalars. For every near-collision, form the
candidate c = m0 + t_acc - w_acc (the value that WOULD be d if it were exact) and
measure the signed distance (c - d) mod W. If near-collisions leak, (c-d) concentrates
near 0; if the metric is destroyed, (c-d) is uniform on (-W/2, W/2].

Statistic: fraction of candidates within +/-W/R of the true d, vs the uniform
baseline 2/R, ranked against a permutation null that shuffles which instance's d each
candidate is scored against. Exact integer offsets; the rank decides, not a float.

Usage: python3 struct_test_D.py
"""
import secrets
from puzzle_kangaroo import add, G, N_ORD

def mul(k, Pt):
    R = None; A = Pt; k %= N_ORD
    while k:
        if k & 1: R = add(R, A)
        A = add(A, A); k >>= 1
    return R

WBITS = 28
W = 1 << WBITS
K = 16
STEP = 1 << (WBITS // 2 - 3)                      # mean jump ~ sqrt(W)/K scale
JUMPS = [(i + 1) * STEP for i in range(K)]
JUMPG = [mul(s, G) for s in JUMPS]
TOPB = 16                                         # near-collision: top-16 X bits agree
SHIFT = 256 - TOPB
L = 2500                                          # walk length per herd
INSTANCES = 40
R = 100                                           # "near d" window = W/R

def walk(startP, startscalar, L):
    """Return list of (top_bucket, fullX, acc_scalar) along an L-step walk."""
    out = []; Pt = startP; acc = startscalar
    for _ in range(L):
        x = Pt[0]
        out.append((x >> SHIFT, x, acc))
        j = x % K
        Pt = add(Pt, JUMPG[j]); acc += JUMPS[j]
    return out

def collect_candidates():
    """Run INSTANCES solvable kangaroos; return per-candidate (inst_id, signed c-mod-W)."""
    m0 = W // 2
    tameP = mul(m0, G)
    tame = walk(tameP, m0, L)                     # tame herd is the same each instance
    tbucket = {}
    for b, x, acc in tame:
        tbucket.setdefault(b, []).append((x, acc))
    cands = []; truths = []
    for inst in range(INSTANCES):
        d = secrets.randbelow(W)
        Q = mul(d, G)
        wild = walk(Q, d, L)
        truths.append(d)
        for b, wx, wacc in wild:
            for tx, tacc in tbucket.get(b, ()):
                if tx == wx:
                    continue                      # exact collision (gives d trivially); skip
                c = (m0 + tacc - wacc) % N_ORD
                cmod = c % W                       # candidate reduced into the interval
                cands.append((inst, cmod))
    return cands, truths

def signed_dist(a, b, W):
    d = (a - b) % W
    return d - W if d > W // 2 else d

def main():
    print("# TEST D  near-collision information (top-16-bit X agreement)")
    print(f"# W=2^{WBITS}, {INSTANCES} instances, walk L={L}, near-window +/-W/{R} (baseline {2/R:.3f})\n")
    cands, truths = collect_candidates()
    n = len(cands)
    hits = sum(1 for inst, cmod in cands if abs(signed_dist(cmod, truths[inst], W)) <= W // R)
    frac = hits / n if n else 0.0
    # permutation null: score each candidate against a RANDOM instance's d
    B = 500; ge = 0
    import random as _r
    for _ in range(B):
        h = 0
        for inst, cmod in cands:
            dd = truths[_r.randrange(INSTANCES)]
            if abs(signed_dist(cmod, dd, W)) <= W // R:
                h += 1
        if h >= hits:
            ge += 1
    print(f"  near-collisions found: {n}")
    print(f"  candidates within +/-W/{R} of TRUE d: {hits}/{n} = {frac:.4f}  (uniform baseline {2/R:.3f})")
    print(f"  permutation rank (null score vs true): {ge}/{B}")
    print()
    if ge > B * 0.05:
        print("  => rank mid/high: near-collision candidates are NO closer to d than to a")
        print("     random instance's d. Near-collisions carry no partial info (metric destroyed).")
    else:
        print("  => rank near 0: candidates concentrate near the TRUE d -> partial info. ESCALATE.")

if __name__ == "__main__":
    main()
