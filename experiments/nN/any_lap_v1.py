"""Is the obstruction the first lap?

The rung-selection rule at q (rung_selection_v1) takes e = the least multiple of q and the instants
i/q + 1/(8e): the FIRST opening of e pushed round the q-gon.  The certificate (Theorem 10) allows
any opening (j + 1/8)/e.  Here, on the hard sets (no q <= 8 certifies by the rule):
  any lap:  for some q <= 8, the least multiple e of q has a lonely opening at ANY j
            (Theorem 10: d*(8j+1) mod 8e in [e, 7e] for every d);
  which j:  for the lonely openings found, the lap index j relative to the rule's family
            (j = i*(e/q) for a unit i is the rule's own; others are later/other laps);
  any flank: some flank of the set has a lonely opening (always true -- Theorem 9 -- recorded for
            the flank ranks used).
"""
import json, os
from math import gcd
from collections import Counter
HERE = os.path.dirname(os.path.abspath(__file__))
H = [tuple(S) for S in json.load(open(os.path.join(HERE, 'hard_sets_41_60.json')))]

def lonely_js(S, e): return [j for j in range(e) if all(e <= d * (8 * j + 1) % (8 * e) <= 7 * e for d in S)]

anylap = Counter(); kinds = Counter(); ranks = Counter(); which_q = Counter(); ex = []
for S in H:
    ok = False; qs = []
    for q in range(2, 9):
        mult = [d for d in S if d % q == 0]
        if not mult: continue
        e = min(mult); js = lonely_js(S, e)
        if js:
            ok = True; qs.append(q)
            M = e // q
            for j in js:
                kinds['on the rule lattice (j = i*e/q)' if j % M == 0 else 'other lap of e'] += 1
    anylap[ok] += 1
    if ok: which_q[min(qs)] += 1
    elif len(ex) < 6: ex.append(S)
    srt = sorted(S, reverse=True)
    r = next(i for i, e in enumerate(srt) if lonely_js(S, e))
    ranks[r] += 1
print(f"hard sets {len(H)}: some q <= 8 with its least multiple e having a lonely opening at ANY lap: {anylap[True]}; not: {anylap[False]} {ex}")
print(f"   least such q: {sorted(which_q.items())}")
print(f"   the lonely openings found, by lap: {dict(kinds)}")
print(f"   rank of the largest flank with a lonely opening (0 = largest): {sorted(ranks.items())}")

# Relax the second "first": any multiple of q (not only the least) as the flank, any lap.
rest = [S for S in H if not any(lonely_js(S, min(d for d in S if d % q == 0)) for q in range(2, 9) if any(d % q == 0 for d in S))]
c = Counter(); detail = []
for S in rest:
    hits = [(q, e) for q in range(2, 9) for e in S if e % q == 0 and lonely_js(S, e)]
    c[bool(hits)] += 1
    detail.append((S, sorted({e for _, e in hits}), sorted({q for q, _ in hits})))
print(f"the {len(rest)} left: some multiple of some q <= 8, any lap, has a lonely opening: {c[True]}; not: {c[False]}")
for S, es, qs in detail: print(f"   {S}: lonely flanks that are multiples of a q <= 8: {es} (q in {qs})")
