"""Null test for the lap-extended rule (other session, claude/n8-pair-moduli-tests, e29c6e4).

The extended instants i/q + (r + 1/8)/e, q <= 8, e a multiple of q in S, i a unit mod q, are the
openings of flank e with index j = i*(e/q) + r.  Null: the same number of random openings of the
same flanks.  Reports, for the 28 sets no first-lap rule with q <= 8 certifies and for the 1,586
failing q = 2..5 (v1 residual of [1,40]): family against null, laps r <= 0, 1, 2.
"""
import itertools, random, time
from math import gcd
from collections import Counter
_rs = __file__.replace('lap_null_v1.py', 'rung_selection_v1.py')
_s = open(_rs).read(); __file__ = _rs; exec(_s[:_s.index("for top in (30, 40):")])
def lonely_open(S, e, j):                 # the opening (8j+1)/(8e), exact band test
    a = 8 * j + 1; m = 8 * e
    return all(e <= d * a % m <= 7 * e for d in S)
def family(S, R):
    """openings j = i*(e/q) + r of flanks e (multiples in S of some q <= 8), i a unit mod q, r <= R"""
    out = set()
    for q in range(2, 9):
        for e in S:
            if e % q: continue
            M = e // q
            for i in range(q):
                if gcd(i, q) != 1: continue
                for r in range(R + 1): out.add((e, (i * M + r) % e))
    return sorted(out)
random.seed(11)
R40 = [S for S in itertools.combinations(range(1, 41), 7) if eight_residual(S)]
f25 = [S for S in R40 if not any(rule(S, q, free_exact) for q in range(2, 6))]
hard = [S for S in f25 if not any(rule(S, q, free_exact) for q in (6, 7, 8))]
t0 = time.time()
for label, sets in (("28 hard sets", hard), ("1,586 failing q = 2..5", f25)):
    for Rl in (0, 1, 2):
        hit = nul = 0; size = 0
        for S in sets:
            F = family(S, Rl); size += len(F)
            hit += any(lonely_open(S, e, j) for e, j in F)
            flanks = [e for e, _ in F]
            nul += any(lonely_open(S, e, random.randrange(e)) for e in (random.choice(flanks) for _ in F))
        print(f"{label}, laps r <= {Rl}: family size {size/len(sets):.1f};  family {hit}/{len(sets)};  same number of random openings of the same flanks {nul}/{len(sets)}")
print(f"({time.time()-t0:.0f}s)")
