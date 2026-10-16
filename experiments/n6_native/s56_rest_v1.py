#!/usr/bin/env python3
"""Observation: the §5/§6 sets closed by neither family, fold nor cluster box (s56_families_v1): all with entries
<= 26; and for their patterns (1,3,4,5,X), (1,4,5,6,X) etc., which X in 6..300 stay unclosed."""
import math
from itertools import combinations
exec(open("s56_families_v1.py").read().split("def run(")[0])
small = [S for S in combinations(range(1, 27), 5) if math.gcd(*S) == 1 and case(S)]
rest = [S for S in small if not (fam(S) or fold(S) or cluster(S))]
print(len(rest), rest)
pats = sorted(set(S[:4] for S in rest))
for p in pats:
    xs = [X for X in range(p[3] + 1, 301) if case(p + (X,)) and math.gcd(*(p + (X,))) == 1 and not (fam(p + (X,)) or fold(p + (X,)) or cluster(p + (X,)))]
    print("pattern", p, "unclosed X in [.., 300]:", xs)
