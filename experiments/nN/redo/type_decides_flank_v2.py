"""The 12 types of type_decides_flank_v1 (range [1,18]) with no common flank: what they share.
For each failing type: the slot residues, which runners share the subject's slot (residue 0) or sit just under it
(residue 7), and for each member those runners' whole slots (laps) at d_min.  Exact."""
import itertools
from math import gcd
from functools import reduce
from type_decides_flank_v1 import run, type_of
import io, contextlib
arrs = [(1,) + c for c in itertools.combinations(range(2, 19), 7) if reduce(gcd, [x - 1 for x in c]) == 1]
with contextlib.redirect_stdout(io.StringIO()): members = run(arrs, '')
bad = [(T, M) for T, M in members.items() if len(M) >= 2 and not set.intersection(*[m[2] for m in M])]
print(f"{len(bad)} types with no common flank")
for T, M in bad:
    k, res = T
    sharers = [j for j in range(8) if j != k and res[j] in (0, 7)]
    print(f"\n type rank {k}, residues {res}; runners in or just under the subject's slot: ranks {sharers}")
    for V, kk, w, c in M:
        m = min(abs(v - V[kk]) for j, v in enumerate(V) if j != kk)
        laps = {j: (V[j] - V[kk]) // m for j in sharers}
        print(f"    {V}: sharer slots {laps}, working flank ranks {sorted(w)}")
