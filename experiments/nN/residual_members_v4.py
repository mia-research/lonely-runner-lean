"""Targeted search for residual members with NO separation of scale (max/min < 9).

residual_members_v3: 0 of 4,000 random constructions (one runner d1 = 8*lcm(1..64)*u, mixed residues);
the free flank and the cost field remove them.  Here: hill-climbing on the other six runners (kept in
(d1/8.9, d1]), objective = how far down the residual's field list the set gets; moves re-draw one
runner with a random residue mod 8 or mod 24.  Exact integer arithmetic; fixed seed; 150 restarts.
"""
exec(open('residual_members_v1.py').read().split("L = 8 * lcm")[0])
from math import lcm
import time
L = 8 * lcm(*range(1, 65)); rnd = random.Random(34)
FIELDS = [("odd", lambda S: any(d % 2 for d in S)),
          ("5,6,7,8", lambda S: all(any(d % q == 0 for d in S) for q in (5, 6, 7, 8))),
          ("spread", lambda S: max(S) > 7 * min(S)),
          ("cost", lambda S: sum(4 if d % 8 == 4 else 2 for d in S if d % 8) >= 8),
          ("free flank", lambda S: not any(free_flank8(S, e) for e in S if e % 8 == 0)),
          ("shifted", lambda S: not shifted(S)), ("fast", lambda S: sorted(S)[-1] <= 7 * sorted(S)[-2]),
          ("first lap/-7", lambda S: not (first_lap(S) or minus_seven(S))),
          ("rational N|8", lambda S: not has_rational_opening(S)),
          ("thirds/fifths", lambda S: not (has_thirds(S) or has_fifths(S))),
          ("6,7,9", lambda S: not (has_N(S, 6) or has_N(S, 7) or has_N(S, 9))),
          ("small resolution", lambda S: not small_resolution(S)),
          ("no common factor", lambda S: reduce(gcd, S) == 1)]
def score(S):
    if len(set(S)) < 7 or max(S) >= 9 * min(S): return -1
    for i, (_, f) in enumerate(FIELDS):
        if not f(S): return i
    return len(FIELDS)
t0 = time.time(); best = (-1, None); found = []
for r in range(150):
    d1 = L * rnd.randrange(1, 20); lo = int(d1 / 8.9) + 1
    others = [rnd.randrange(lo, d1) for _ in range(6)]
    S = tuple(sorted([d1] + others)); sc = score(S)
    for step in range(300):
        o = list(others); i = rnd.randrange(6)
        base = rnd.randrange(lo, d1); mod = rnd.choice((8, 24, 40))
        o[i] = base - base % mod + rnd.randrange(mod)
        if not (lo <= o[i] <= d1): continue
        T = tuple(sorted([d1] + o)); s2 = score(T)
        if s2 >= sc: others, S, sc = o, T, s2
        if sc == len(FIELDS): break
    if sc > best[0]: best = (sc, S)
    if sc == len(FIELDS): found.append(S)
print(f"{time.time() - t0:.0f}s; residual members found: {len(found)}")
print(f"furthest: passes {best[0]} of {len(FIELDS)} fields (next field: {FIELDS[best[0]][0] if best[0] < len(FIELDS) else '-'}); residues mod 8 {[d % 8 for d in best[1]]}")

# where do the scale-free members clear?  the ladder past 64, exact
from collections import Counter
def dead(S, D): return any(d % (8 * D) == 0 for d in S)
res = []
for S in found:
    D = 65; L0 = None; live = 0
    while D <= 5000:
        if not dead(S, D):
            if L0 is None: L0 = D
            j = next((j for j in range(D) if clears(S, D, 8 * j + 1)), None)
            if j is not None: break
            live += 1
        D += 1
    res.append((D, L0, live, S))
print("members (D* = least clearing resolution > 64, L_0 = first live lattice > 64, live lattices blocked before D*):")
for D, L0, live, S in res[:22]:
    print(f"  D*={D}, L_0={L0}, blocked live lattices={live}, residues mod 8={[d % 8 for d in S]}, max/min={max(S)/min(S):.2f}")
