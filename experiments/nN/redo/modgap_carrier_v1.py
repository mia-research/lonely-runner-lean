"""modgap_carrier_v1 (2026-10-06): the descent modulus q as the interaction between the readings' residues mod q (which
readings are 0 mod q) and the landing.  Exact (integers, Fractions).
Objects.  S the readings, t* = cascade(S), openers e (e t* = J + 1/8).  For q, M_q = {d in S : q | d}, rho_q =
cascade({d/q : d in M_q}).  q is a CARRIER of S when t* = rho_q / q (the multiples of q alone fix the landing).
[P] t* >= rho_q/q always (modgap_map_v1 P7: a lonely instant of S is lonely for the subset M_q, and the subset M_q at an
    instant t is the quotients at q t).  Equality iff S is lonely at rho_q/q.
Statements tested (every set of every population, q in [2, 64]):
  CQ1  q is a carrier  =>  q divides every opener of S at t*.
  CQ2  no carrier q in [2, 64]: minimal subset T of S with cascade(T) = t* (the witness is T's own landing: t*(S) >= t*(T)
       by the subset argument, equality means T's landing is lonely for all S).  Recorded per set: |T|, whether T lies in
       some M_q (T is then a carrier subset in the descent's sense, with q > 64 or q | gcd(T) not a modulus of S), the
       opener classes mod 8, the readings in T.
Exceptions (sets with no carrier q <= 64) are listed individually after the counts: readings, t*, openers, minimal T.
"""
import sys, json, itertools, collections
sys.path.insert(0, '.')
from fractions import Fraction as F
from math import gcd
from functools import reduce
from modgap_lib_v1 import load, full_residual, cascade, openers, typ8

C = [S for S in dict.fromkeys(load('../residual_members_C_list_v1.json')) if full_residual(S)]
BS = [S for S in dict.fromkeys(load('both_shadowed_members_v1.json')) if full_residual(S)]
st = json.load(open('divisible_members_v2.json'))
DA = list(dict.fromkeys(tuple(sorted(S)) for S in st['A'])); DB = list(dict.fromkeys(tuple(sorted(S)) for S in st['B']))
known = set(C) | set(BS) | set(DA) | set(DB)
raw = json.load(open('members_5978_v1.json'))
T1 = [S for S in dict.fromkeys(tuple(sorted(x[2])) for x in raw) if S not in known]
import random
def smalls(n):
    rnd = random.Random(20261006); out = []
    seen = set()
    while len(out) < n:
        S = tuple(sorted(rnd.sample(range(1, 61), 7)))
        if reduce(gcd, S) == 1 and S not in seen and full_residual(S):
            seen.add(S); out.append(S)
    return out
out = open('modgap_carrier_v1.out', 'w'); out.write(__doc__ + "\n")
def w(s): out.write(s + "\n"); print(s)
for name, sets in (('C', C), ('BS', BS), ('DA', DA), ('DB', DB), ('T1 (new)', T1)):
    c = collections.Counter(); exc = []; carq = collections.Counter(); sz = collections.Counter()
    for S in sets:
        t = cascade(S); op = openers(S, t)
        cars = []
        for q in range(2, 65):
            M = [d // q for d in S if d % q == 0]
            if not M: continue
            if cascade(M) / q == t:
                cars.append(q); c[('CQ1', all(o % q == 0 for o in op))] += 1
        c['has carrier' if cars else 'no carrier'] += 1
        if cars: carq[cars[0]] += 1
        else:
            T = next(T for k in range(1, 8) for T in itertools.combinations(S, k) if cascade(list(T)) == t)
            inM = [q for q in range(2, 200) if all(d % q == 0 for d in T)]
            sz[(len(T), bool(inM))] += 1
            exc.append((S, t, op, T, inM))
    w("\n==== %s: %d sets" % (name, len(sets)))
    w("  CQ1 carrier => q | every opener: [T %d/%d]" % (c[('CQ1', True)], c[('CQ1', True)] + c[('CQ1', False)]))
    w("  sets with a carrier q in [2, 64]: %d; without: %d" % (c['has carrier'], c['no carrier']))
    w("  least carrier q (count): %s" % dict(sorted(carq.items())))
    w("  no carrier: (|minimal T|, T inside some M_q for q < 200): %s" % dict(sorted(sz.items())))
    for S, t, op, T, inM in exc[:40]:
        w("    EXC S=%s t*=%s openers=%s (%s) minimal T=%s T in M_q for q=%s" % (S, t, op, ''.join(typ8(o) for o in op), T, inM))
    if len(exc) > 40: w("    ... %d more exceptions not printed (counts above are over all)" % (len(exc) - 40))
out.close()
