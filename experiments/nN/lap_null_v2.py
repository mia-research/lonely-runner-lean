"""Settles the extra-lap question between the two 2026-09-25 sessions, on ONE object with ONE null.

any_lap_v1 (session 2) tested EVERY opening j < e of the rule's flank (Theorem 10 at that flank);
lap_null_v1 (session 1) tested laps r <= 2 on the 28 sets of [1,40] with one null seed.  Here:
lap_null_v1's family and null, verbatim, on session 2's 1,436 rule-miss sets (hard_sets_41_60.json),
20 null seeds per lap bound and 500 at r <= 2; and the any-lap family at the rule's least-multiple
flanks against the same number of random flanks of S.
Pre-set criterion: laps carry structure only if the family beats the null beyond the seed spread.
"""
import json, random, statistics as st
from math import gcd
H = [tuple(S) for S in json.load(open('hard_sets_41_60.json'))]
def lonely_open(S, e, j):
    a = 8 * j + 1; m = 8 * e
    return all(e <= d * a % m <= 7 * e for d in S)
def family(S, R):
    out = set()
    for q in range(2, 9):
        for e in S:
            if e % q: continue
            M = e // q
            for i in range(q):
                if gcd(i, q) != 1: continue
                for r in range(R + 1): out.add((e, (i * M + r) % e))
    return sorted(out)
L = {S: {e: {j for j in range(e) if lonely_open(S, e, j)} for e in S} for S in H}
print(f"{len(H)} rule-miss sets, largest 41..60")
for R, seeds, base in ((0, 20, 0), (1, 20, 0), (2, 20, 0), (2, 500, 1000)):
    fams = [family(S, R) for S in H]
    hit = sum(any(j in L[S][e] for e, j in F) for S, F in zip(H, fams))
    nulls = []
    for seed in range(seeds):
        rnd = random.Random(base + seed); c = 0
        for S, F in zip(H, fams):
            fl = [e for e, _ in F]
            c += any(rnd.randrange(e) in L[S][e] for e in (rnd.choice(fl) for _ in F))
        nulls.append(c)
    ge = sum(n >= hit for n in nulls)
    print(f"laps r <= {R}: family size {st.mean(len(F) for F in fams):.1f}; family {hit}; null ({seeds} seeds) "
          f"mean {st.mean(nulls):.2f} sd {st.pstdev(nulls):.2f} range {min(nulls)}-{max(nulls)}; seeds >= family {ge}/{seeds}")
rule = sum(any(L[S][min(d for d in S if d % q == 0)] for q in range(2, 9) if any(d % q == 0 for d in S)) for S in H)
nulls = []
for seed in range(20):
    rnd = random.Random(100 + seed); c = 0
    for S in H:
        k = len({min(d for d in S if d % q == 0) for q in range(2, 9) if any(d % q == 0 for d in S)})
        c += any(L[S][e] for e in rnd.sample(S, k))
    nulls.append(c)
print(f"any lap: the rule's least-multiple flanks {rule}; same number of random flanks of S (20 seeds): "
      f"mean {st.mean(nulls):.1f} sd {st.pstdev(nulls):.1f} range {min(nulls)}-{max(nulls)}")
