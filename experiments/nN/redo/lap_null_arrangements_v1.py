"""REDO of lap_null_v1/v2 (which used difference sets): the extra-lap family against a same-size null,
on RULE-MISS RUNNERS of arrangements -- runners of arrangements of 8 distinct speeds in [1,24] (gcd 1,
every runner) whose readings lie in the session-start residual and fail the q <= 8 first-opening rule.
Family and null as lap_null_v1 (openings i*(e/q) + r of multiples e of q <= 8, r <= R; null: the same
number of random openings of the same flanks), 20 seeds."""
import random, statistics as st
from itertools import combinations
from math import gcd
from functools import reduce
from collections import Counter
from residual_arrangements_v1 import v1_residual
_rs = '../rung_selection_v1.py'; _s = open(_rs).read(); __file__ = _rs
exec(_s[:_s.index("for top in (30, 40):")])
from arrangement_lib import readings
def lonely_open(S, e, j):
    a = 8 * j + 1; return all(e <= d * a % (8 * e) <= 7 * e for d in S)
def family(S, R):
    out = set()
    for q in range(2, 9):
        for e in S:
            if e % q: continue
            for i in range(q):
                if gcd(i, q) != 1: continue
                for r in range(R + 1): out.add((e, (i * (e // q) + r) % e))
    return sorted(out)
if __name__ == "__main__":
    miss = []
    for V in combinations(range(1, 25), 8):
        if reduce(gcd, [v - V[0] for v in V[1:]]) != 1: continue
        for k in range(8):
            S = tuple(sorted({abs(v - V[k]) for v in V if v != V[k]}))
            if len(S) == 7 and v1_residual(S) and not any(rule(S, q, free_exact) for q in range(2, 9)): miss.append((V, k, S))
    sets = [S for _, _, S in miss]
    print(f"rule-miss runners in arrangements of [1,24]: {len(miss)} runners, {len(set(sets))} distinct reading sets")
    for R in (0, 1, 2):
        fams = [family(S, R) for S in sets]
        hit = sum(any(lonely_open(S, e, j) for e, j in F_) for S, F_ in zip(sets, fams))
        nulls = []
        for seed in range(20):
            rnd = random.Random(seed); c = 0
            for S, F_ in zip(sets, fams):
                fl = [e for e, _ in F_]
                c += any(lonely_open(S, e, rnd.randrange(e)) for e in (rnd.choice(fl) for _ in F_))
            nulls.append(c)
        print(f"   laps r <= {R}: family {hit}/{len(sets)};  null mean {st.mean(nulls):.1f} sd {st.pstdev(nulls):.1f} range {min(nulls)}-{max(nulls)}")
