#!/usr/bin/env python3
"""Observation only. For each primitive SixResidual set S = (v1<...<v5), run the cascade
(MomentIterationN.move at n = 6) from 1/(6 v1) with exact Fractions. Each move goes to the latest next
opening among the elements in the way; its SETTER is that element. Records:
  - number of moves; setter sequence as size ranks (1 = smallest .. 5 = largest) with laps;
  - the final instant T and the flank it is an opening of (the last setter; v1 if no move);
  - BHK's case as dispatched by LRC.OrderSixN.lonely6_of_lt (D = v3 - v2):
      S8: v3 <= 3 v1;  S5: D | v1;  S6: D | v3 (D does not divide v1);  S7: otherwise.
Writes one line per set to six_cascade_observe_v1.tsv and prints summary tables."""
import sys, math, importlib.util
from itertools import combinations
from fractions import Fraction as F
from collections import Counter, defaultdict
spec = importlib.util.spec_from_file_location("r", "six_residual_v1.py")
r = importlib.util.module_from_spec(spec); spec.loader.exec_module(r)
HI = int(sys.argv[1])
def cd(x):
    f = x - (x.numerator // x.denominator); return min(f, 1 - f)
def cascade(S, n=6, cap=1000):
    t = F(1, n * S[0]); moves = []
    for _ in range(cap):
        blk = [d for d in S if cd(d * t) < F(1, n)]
        if not blk: return t, moves
        best = None
        for d in blk:
            x = d * t - F(1, n); c = -((-x.numerator) // x.denominator)
            o = (c + F(1, n)) / d
            if best is None or o > best[0]: best = (o, d, c)
        moves.append((S.index(best[1]) + 1, best[2]))
        t = best[0]
    raise RuntimeError(S)
def bhk_case(S):
    v1, v2, v3 = S[0], S[1], S[2]; D = v3 - v2
    if v3 <= 3 * v1: return "S8"
    if v1 % D == 0: return "S5"
    if v3 % D == 0: return "S6"
    return "S7"
nm = Counter(); final_rank = Counter(); seq = Counter(); by_case = defaultdict(Counter); case_n = Counter()
first_setter = Counter()
with open("six_cascade_observe_v1.tsv", "w") as out:
    out.write("set\tbhk_case\tmoves\tsetter_ranks\tlaps\tT\tfinal_flank_rank\n")
    for S in combinations(range(1, HI + 1), 5):
        if math.gcd(*S) != 1 or not r.six_residual(S): continue
        T, mv = cascade(S)
        ranks = tuple(m[0] for m in mv); laps = tuple(m[1] for m in mv)
        fr = ranks[-1] if ranks else 1
        c = bhk_case(S)
        nm[len(mv)] += 1; final_rank[fr] += 1; seq[ranks] += 1; case_n[c] += 1
        by_case[c][(len(mv), fr)] += 1
        if ranks: first_setter[ranks[0]] += 1
        out.write(f"{S}\t{c}\t{len(mv)}\t{ranks}\t{laps}\t{T}\t{fr}\n")
N = sum(nm.values())
print(f"HI={HI}: residual sets={N}")
print("  moves:", dict(sorted(nm.items())))
print("  final flank (size rank of the element whose opening T is):", dict(sorted(final_rank.items())))
print("  first setter rank:", dict(sorted(first_setter.items())))
print("  most common setter-rank sequences:", seq.most_common(12))
print("  BHK case counts:", dict(case_n))
for c in sorted(by_case):
    tot = case_n[c]
    fr = Counter(); mvs = Counter()
    for (m, f), k in by_case[c].items(): fr[f] += k; mvs[m] += k
    print(f"  {c}: final flank rank {dict(sorted(fr.items()))}; moves {dict(sorted(mvs.items()))}")
