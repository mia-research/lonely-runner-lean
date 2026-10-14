"""modgap_family_v2 (2026-10-06): a freshly built (3, oooo) divisible family with SHAPE as the parameter.  Seeded (20261006), exact (integers, Fractions).
SCALE IS NOT A PARAMETER: kS lonely at s iff S lonely at k s, so t*(kS) = t*(S)/k and the setter sequence is unchanged; checked below as a control on 300 members (multiplication by 10^7 + 3).
Shape (v2, after reading the residual predicate: no resolution at any D <= 64 forces a universal multiple 8 lcm(1..64) u; no fast pair forces three comparable big multiples): multiples 8 lcm(1..64) u, 8 lcm(1..64) u2 (u < u2 <= 7u), 8 c3 (c3 in [lcm u/7, 7 lcm u]); the four odd readings are random odd divisors of lcm(1..64) of 0 to K digits, so every odd w divides the cofactor lcm(1..64) u of the universal multiple
(the divisible family of E405).  Variants (assignment of the w_i to the cofactors): V1 all four divide c_1 (c_1 = lcm * u); V2 w_1, w_2 | c_1 and w_3, w_4 | c_2; V3 w_i | c_{1 + i mod 3};
the unconstrained cofactors are lcm-multiples times a free multiplier up to 10^K.  Only members in EightResidual (full_residual, all 22 fields) with gcd 1 and exactly 3 multiples of 8
and 4 odd readings are kept.  For K in {2, 4, 8, 12}.
Measures per member: setter roles along the cascade path (M multiple of 8, O odd), the alternation count (number of M<->O switches in the setter sequence), moves, laps traversed per jump
(max), re-block events, ratio d_max/d_min (digits).  Baseline: the same measures on the stored DA and DB members.
[PROVISIONAL: counting tool; supports: the distributions]"""
import sys, json, math, random, collections
sys.path.insert(0, '.')
from fractions import Fraction as F
from math import gcd
from functools import reduce
from members_reach_check_v1 import full_residual, cascade as casc, cd
from modgap_lib_v1 import cascade_path, E8
def lcm(a, b): return a * b // gcd(a, b)
def logodd(rnd, K):
    e = rnd.uniform(0, K); v = int(10 ** e) | 1
    return v
from math import lcm
L8 = 8 * lcm(*range(1, 65)); LC = L8 // 8
PRIMES = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61]
PP = []
for p in PRIMES:
    q = p
    while q * p <= 64 and False: q *= p
    pw = [p]; x = p
    while x * p <= 64: x *= p; pw.append(x)
    PP.append(pw)
def odd_divisor(rnd, target_digits):
    """A random odd divisor of lcm(1..64) of about the given number of digits (greedy random product of its prime powers)."""
    order = list(range(len(PRIMES))); rnd.shuffle(order); v = 1
    for k in order:
        if len(str(v)) >= target_digits: break
        v *= rnd.choice(PP[k]) if rnd.random() < 0.5 else PRIMES[k]
    return v
def build(rnd, K, variant):
    u = rnd.randrange(1, 50); u2 = rnd.randrange(u + 1, 7 * u + 1)
    U1 = L8 * u; U2 = L8 * u2; c3 = rnd.randrange(max(1, LC * u // 7), 7 * LC * u); U3 = 8 * c3
    w = set()
    while len(w) < 4:
        w.add(odd_divisor(rnd, rnd.randrange(1, K + 1)) | 1 if False else odd_divisor(rnd, rnd.randrange(0, K + 1)))
    S = sorted({U1, U2, U3} | set(w))
    if len(S) != 7: return None
    g = reduce(gcd, S); S = tuple(x // g for x in S)
    M = [d for d in S if d % 8 == 0]; W = [d for d in S if d % 8]
    if len(M) != 3 or len(W) != 4 or any(x % 2 == 0 for x in W): return None
    if not all(any((m // 8) % x == 0 for m in M) for x in W): return None
    return S
def measures(S):
    path = cascade_path(S); ts = [p for p, _ in path]
    roles = ''.join('M' if d % 8 == 0 else 'O' for _, d in path[1:])
    sw = sum(1 for a, b in zip(roles, roles[1:]) if a != b)
    laps = max([math.floor(d * (ts[i + 1] - ts[i])) for i in range(len(ts) - 1) for d in S] or [0])
    last = {}; reb = 0
    for i, ti in enumerate(ts):
        for d in S:
            if cd(d * ti) < E8:
                if d in last and last[d] != i: reb += 1
                last[d] = i
    return roles, sw, len(ts) - 1, laps, reb, ts[-1]
out = open('modgap_family_v2.out', 'w'); out.write(__doc__ + "\n")
def summarise(name, sets):
    R = [measures(S) for S in sets]
    if not R: out.write("\n%s: 0 members\n" % name); return
    out.write("\n%s: %d members\n" % (name, len(R)))
    for lab, idx in (('alternation count (M<->O switches)', 1), ('moves', 2), ('re-block events', 4)):
        out.write("  %-34s %s\n" % (lab, dict(sorted(collections.Counter(r[idx] for r in R).items()))))
    out.write("  max laps in one jump: %d;  ratio d_max/d_min digits: %s\n" % (max(r[3] for r in R), dict(sorted(collections.Counter(len(str(S[-1] // S[0])) for S in sets).items()))))
    top = sorted(zip(R, sets), key=lambda x: -x[0][1])[:5]
    out.write("  five with the most switches (role string, switches, moves):\n")
    for r, S in top: out.write("    %s  %d  %d   (%d-digit readings, ratio %d digits)\n" % (r[0], r[1], r[2], len(str(S[-1])), len(str(S[-1] // S[0]))))
st = json.load(open('divisible_members_v2.json'))
for nm in ('A', 'B'):
    summarise('baseline stored %s (DA/DB)' % nm, [tuple(sorted(S)) for S in st[nm]])
for K in (2, 6, 12, 18, 24):
    rnd = random.Random(20261006 + K); mem = []; tried = 0
    while tried < 60000 and len(mem) < 1500:
        tried += 1
        S = build(rnd, K, 1)
        if S is not None and full_residual(S): mem.append(S)
    mem = list(dict.fromkeys(mem))
    out.write("\nK = %d: %d draws, %d members in EightResidual\n" % (K, tried, len(mem)))
    summarise('K = %d, all variants' % K, mem)
    for v in (1, 2, 3):
        pass
    if K == 12:
        ctl = mem[:300]; ok = 0
        for S in ctl:
            kk = 10 ** 7 + 3; S2 = tuple(kk * x for x in S)
            r1 = measures(S); r2 = measures(S2)
            ok += (r1[0] == r2[0] and r2[5] * kk == r1[5])
        out.write("  scale control (multiply by 10^7 + 3): setter roles identical and t*(kS) = t*(S)/k in %d of %d\n" % (ok, len(ctl)))
out.close(); print(open('modgap_family_v2.out').read()[len(__doc__):][:9000])
