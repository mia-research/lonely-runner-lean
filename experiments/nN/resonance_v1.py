"""Who blocks the rung-selection rule, and the modulus resonant with the largest disparity.

The rule (rung_selection_v1): for q, e the least multiple of q in S, the instants i/q + 1/(8e);
multiples of q need e's band, the non-multiples a common clear unit i.  At t = i/q + eps a
disparity d = s + q*m reads s*i/q + d*eps: residues on the vertices of the regular q-gon (Theorem 4's
global instants at modulus q), sizes as displacements (Theorem 5).  eps = 1/(8e) is the least
displacement that moves the least multiple of q off the subject; large non-multiples then wrap.

Reports, on the v1 residual of [1,40]: for the sets failing q = 2..7 and a sample of those failing
q = 2..5, how many q a single disparity blocks and how large the busiest blocker is; then how many
sets the rule certifies with q <= 8, with q a proper divisor of the largest disparity, and what
is left.
"""
import itertools, random, time
from collections import Counter
_rs = __file__.replace('resonance_v1.py', 'rung_selection_v1.py')
_s = open(_rs).read(); __file__ = _rs; exec(_s[:_s.index("for top in (30, 40):")])

def witnesses(S, q):
    mult = [d for d in S if d % q == 0]; e = min(mult)
    out = {d for d in mult if not (e <= d % (8 * e) <= 7 * e)}
    out |= {d for d in S if d % q and any(blocked(X(d, e, q, i), e) for i in rung_units(e, q))}
    return out

def isprime(n): return n > 1 and all(n % k for k in range(2, int(n ** .5) + 1))

t0 = time.time(); R = [S for S in itertools.combinations(range(1, 41), 7) if eight_residual(S)]
f25 = [S for S in R if not any(rule(S, q, free_exact) for q in range(2, 6))]
f27 = [S for S in f25 if not any(rule(S, q, free_exact) for q in (6, 7))]
random.seed(4)
for label, sets, Q in (("fail q = 2..7", f27, range(2, 8)), ("fail q = 2..5 (sample 400)", random.sample(f25, 400), range(2, 6))):
    duty = Counter(); size = Counter()
    for S in sets:
        W = {q: witnesses(S, q) for q in Q if any(d % q == 0 for d in S)}
        cnt = Counter(d for w in W.values() for d in w)
        duty[max(cnt.values())] += 1; size[round(max(cnt, key=cnt.get) / max(S), 1)] += 1
    print(f"{label}: {len(sets)} sets; most q blocked by one disparity {sorted(duty.items())}; busiest blocker / largest {sorted(size.items())}")
c = Counter(); rest = Counter()
for S in R:
    D = max(S)
    small = any(rule(S, q, free_exact) for q in range(2, 9))
    prop = any(D % q == 0 and rule(S, q, free_exact) for q in range(2, D))
    c['q <= 8'] += small; c['q | largest, q < largest'] += prop; c['either'] += small or prop
    if not (small or prop): rest[('largest prime' if isprime(D) else 'largest composite', rule(S, D, free_exact))] += 1
print(f"[1,40] residual v1 {len(R)}: {dict(c)}; the rest (kind of largest, largest flank's own ladder): {dict(rest)}  ({time.time() - t0:.0f}s)")
