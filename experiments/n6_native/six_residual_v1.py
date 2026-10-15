#!/usr/bin/env python3
"""SixResidual, implemented field by field from LonelyRunner/LRC/Spec/OrderSixN.lean (structure
SixResidual, def FreeFlank), plus an exact lonely check by the bounded residue search
(Flanks.lonely_iff_emod_search). Integers only.

Usage: six_residual_v1.py HI [--primitive] [--list N]
Counts 5-subsets of [1, HI] (not all divisible by 6, the hypothesis of lonely_six_or_residual)
that satisfy SixResidual; with --primitive, only gcd = 1.
"""
import sys, math
from itertools import combinations

N = 6

def free_flank(S, e):
    # (∀ d ∈ S, d ≠ e → 6 ∣ d → e ≤ d % (6e) ≤ 5e) ∧ ∃ k < 6, ∀ d ∈ S, ¬6∣d → (d*k + d//e) % 6 ∉ {0,5}
    if not all(e <= d % (6 * e) <= 5 * e for d in S if d != e and d % 6 == 0):
        return False
    return any(all((d * k + d // e) % 6 not in (0, 5) for d in S if d % 6) for k in range(6))

def six_residual(S):
    if len(S) != 5: return False
    if not any(d % 4 == 0 for d in S): return False
    if not any(d % 5 == 0 for d in S): return False
    if not any(5 * a < b for a in S for b in S): return False
    M = sum(1 for d in S if d % 6 == 0); E = 5 - M
    shape = (M == 1 and E == 4) or (M == 2 and E == 3) or (M == 3 and all(d % 3 == 0 for d in S))
    if not shape: return False
    if any(free_flank(S, e) for e in S if e % 6 == 0): return False
    if not all(any(s != V and V <= 5 * s for s in S) for V in S): return False
    return True

def certificates(S, n=N):
    out = []
    for b in S:
        for k in range(b):
            if all(b <= (a * (n * k + 1)) % (n * b) <= (n - 1) * b for a in S):
                out.append((b, k))
    return out

if __name__ == "__main__":
    HI = int(sys.argv[1]); prim = "--primitive" in sys.argv
    lst = int(sys.argv[sys.argv.index("--list") + 1]) if "--list" in sys.argv else 0
    tot = res = 0; shown = 0
    for S in combinations(range(1, HI + 1), 5):
        if all(d % 6 == 0 for d in S): continue
        if prim and math.gcd(*S) != 1: continue
        tot += 1
        if six_residual(S):
            res += 1
            assert certificates(S), S   # every set is lonely (order six holds); sanity
            if shown < lst:
                print("  ", S, "certs:", certificates(S)[:3]); shown += 1
    print(f"HI={HI} primitive={prim}: sets={tot} residual={res}")
