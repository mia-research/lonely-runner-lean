"""E407 (2026-10-06), descent_mod_q_reach_v1: the descent by a modulus q at threshold 1/8, read on the stored
residual members and on the divisible members of divisible_members_v2.json.  Exact (integers and Fractions).
Rule (derived by hand; Lean target DescentModQN.lean): if at most six readings are divisible by q and the
others' budget sum_{q not | e} g*ceil(q/(4g)) (g = gcd(e, q)) is below q, then at sigma = rho/q, where rho is a
lonely instant of the quotients d/q at 1/8, some shift k in [0, q) leaves sigma + k/q lonely
[PROVISIONAL: counting tool; supports: the free shift].  The quotient set's instant here is its cascade landing
(exact); the instant sigma + k/q is then checked for every reading.  q runs over [3, 199], q != 8.
Recorded: per source, members by (status under lean_case_reach_v3, rule applies or not), the least q, and the
number of constructed instants that fail the exact check.
"""
import sys, json, collections
from math import gcd
from fractions import Fraction as F
sys.path.insert(0, '.')
from members_reach_check_v1 import load, full_residual, cascade, lonely
from lean_case_reach_v2 import settled
from lean_case_reach_v3 import grid
def b(e, q):
    g = gcd(e, q); return g * ((q + 4 * g - 1) // (4 * g))
def rule_q(S, Q=200):
    for q in range(3, Q):
        if q == 8: continue
        still = [d for d in S if d % q == 0]; non = [d for d in S if d % q]
        if len(still) <= 6 and sum(b(e, q) for e in non) < q: return q
    return None
def instant(S, q):
    quot = sorted({d // q for d in S if d % q == 0})
    rho = cascade(quot) if quot else F(1, 2)
    sigma = rho / q
    for k in range(q):
        t = sigma + F(k, q)
        if lonely(S, t): return t
    return None
if __name__ == '__main__':
    out = open('descent_mod_q_reach_v1.out', 'w'); out.write(__doc__ + "\n")
    srcs = [(fn, [S for S in dict.fromkeys(load(fn)) if full_residual(S)]) for fn in
            ['../residual_members_C_list_v1.json', 'both_shadowed_members_v1.json']]
    store = json.load(open('divisible_members_v2.json'))
    srcs += [('divisible_members_v2.json:' + k, [tuple(S) for S in store[k]]) for k in ('A', 'B')]
    for fn, sets in srcs:
        c = collections.Counter(); qs = collections.Counter(); fails = []
        for S in sets:
            mult = [d for d in S if d % 8 == 0]; rs = tuple(sorted(d % 8 for d in S if d % 8))
            st = 'Lean (v3)' if (settled(len(mult), rs, '22') or grid(S)) else 'open (v3)'
            q = rule_q(S)
            c[(st, 'rule applies' if q else 'rule does not apply')] += 1
            if q:
                qs[q] += 1
                if instant(S, q) is None: fails.append((S, q))
        out.write("\n%s: %d members: %s\n" % (fn, len(sets), dict(sorted(c.items()))))
        out.write("  least q: %s\n  constructed instants failing the exact check: %d %s\n" % (dict(sorted(qs.items())), len(fails), fails[:3]))
    out.close(); print(open('descent_mod_q_reach_v1.out').read()[len(__doc__):])
