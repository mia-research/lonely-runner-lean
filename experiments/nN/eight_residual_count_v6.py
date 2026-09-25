"""EightResidual with the section 2g field no_small_resolution (D <= resolutionCap8 = 64).

On the 7-subsets of [1,40]: the v5 residual (7 sets, eight_residual_count_v5.out) all clear at
D <= 5 (ladder_vs_fields_v1.out), so v6 is empty there.  Here: the field ALONE against the
session-start residual v1 (the rules before the rational-opening fields), to see what it does
without the flank fields; and the least clearing D over v1.
"""
import itertools, time
from collections import Counter
_rs = __file__.replace('eight_residual_count_v6.py', 'rung_selection_v1.py')
_s = open(_rs).read(); __file__ = _rs; exec(_s[:_s.index("for top in (30, 40):")])
def clears(S, D, a): return all(D <= d * a % (8 * D) <= 7 * D for d in S)
def least_D(S, cap=64):
    for D in range(1, cap + 1):
        if any(clears(S, D, 8 * j + 1) for j in range(D)): return D
    return None
t0 = time.time()
for top in (30, 40):
    R1 = [S for S in itertools.combinations(range(1, top + 1), 7) if eight_residual(S)]
    ds = Counter(least_D(S) for S in R1)
    left = ds.get(None, 0)
    print(f"[1,{top}]: v1 residual {len(R1)};  not cleared by any D <= 64: {left};  least clearing D: {sorted((k, v) for k, v in ds.items() if k)}")
print(f"({time.time() - t0:.0f}s)")
