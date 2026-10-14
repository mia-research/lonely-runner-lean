"""E405 (2026-10-06), divisible_members_v1: residual members (all 22 fields, the Python mirror full_residual of
members_reach_check_v1) of shape (3,4), type (o,o,o,o), in the DIVISIBLE family: every odd non-multiple divides the
cofactor of some multiple of 8 (so E403's grid argument does not apply).  Two constructions, seeded and
deterministic (random.Random(seed); the cascade is deterministic, the construction is a search):
 A (separated by design): c1 = L*a (L = lcm(1..64)), the four odd readings odd divisors of c1 of size Lodd/q,
   c2, c3 drawn in [c1/6, 6 c1].
 B (not separated by design): c_big = L*r kills every resolution D <= 64; c1 odd with several small odd
   factors, rescaled by an odd factor to the size of c_big; the odd readings are c1/q for small odd q;
   c3 drawn in [c1/7, 7 c1].
Recorded per member, exactly (Fractions): the ratio (4th smallest -> 5th smallest reading) against 9 and 26; the
cascade's first lonely instant t; the readings at exactly 1/8 there (the opener); whether the opener is a
multiple of 8 whose cofactor every odd reading divides; the opener's lap index j (t = (8j+1)/(8e)).
"""
import sys, random, math, time, collections
from math import gcd, lcm
from fractions import Fraction as F
sys.path.insert(0, '.')
from members_reach_check_v1 import full_residual, cascade, E8

L = lcm(*range(1, 65)); Lodd = L
while Lodd % 2 == 0: Lodd //= 2
def build_A(rnd):
    odd_small = [q for q in range(1, 200, 2) if Lodd % q == 0]
    c1 = L * rnd.choice([1, 3, 5, 7])
    qs = rnd.sample(odd_small, 4)
    W = sorted({(c1 // (c1 & -c1)) // q for q in qs})
    if len(W) < 4: return None
    c2 = rnd.randrange(c1 // 6, 6 * c1); c3 = rnd.randrange(c1 // 6, 6 * c1)
    return tuple(sorted({8 * c1, 8 * c2, 8 * c3} | set(W)))
def build_B(rnd):
    smallodd = [3, 5, 7, 9, 11, 13, 15, 21, 25, 27, 35, 45]
    base = 1
    for p in rnd.sample([3, 5, 7, 9, 11, 13], 3): base *= p
    c1 = base * rnd.randrange(1, 10**6, 2)
    divs = [c1 // q for q in [1] + smallodd if c1 % q == 0]
    if len(divs) < 4: return None
    W = sorted(rnd.sample(divs, 4))
    cb = L * rnd.randrange(1, 50)
    scale = cb // (c1 * rnd.randrange(1, 7)) or 1
    if scale % 2 == 0: scale += 1
    c1s = c1 * scale; Ws = [w * scale for w in W]
    c3 = rnd.randrange(max(1, c1s // 7), 7 * c1s)
    return tuple(sorted({8 * cb, 8 * c1s, 8 * c3} | set(Ws)))

if __name__ == '__main__':
    secs = float(sys.argv[1]) if len(sys.argv) > 1 else 60
    out = open('divisible_members_v1.out', 'w'); out.write(__doc__ + "\n")
    for name, build, seed in (('A', build_A, 1), ('B', build_B, 2)):
        rnd = random.Random(seed); t0 = time.time(); tried = 0; mem = []
        while time.time() - t0 < secs:
            tried += 1; S = build(rnd)
            if S is None or len(S) != 7: continue
            M = [d for d in S if d % 8 == 0]; W = [d for d in S if d % 8]
            if len(M) != 3 or any(w % 2 == 0 for w in W): continue
            if not all(any((m // 8) % w == 0 for m in M) for w in W): continue
            if full_residual(S): mem.append(S)
        st = collections.Counter(); ex = []
        for S in dict.fromkeys(mem):
            s = sorted(S); r = F(s[4], s[3])
            sep = 'ratio >= 26' if r >= 26 else ('ratio in [9, 26)' if r >= 9 else 'ratio < 9')
            t = cascade(list(S))
            op = [d for d in S if d * t - math.floor(d * t) == E8]
            W = [d for d in S if d % 8]
            divided = [e for e in op if e % 8 == 0 and all((e // 8) % w == 0 for w in W)]
            kind = 'opener a multiple of 8 divisible by every odd reading' if divided else (
                'opener another multiple of 8' if all(e % 8 == 0 for e in op) else 'opener a non-multiple')
            st[(sep, kind)] += 1
            if len(ex) < 6:
                e = op[0]; j = (t * 8 * e - 1) / 8
                ex.append((S, t, op, j))
        out.write("\nconstruction %s: tried %d, members %d (distinct %d)\n" % (name, tried, len(mem), len(set(mem))))
        for k, v in sorted(st.items()): out.write("  %s: %d\n" % (k, v))
        for e in ex: out.write("  example %s landing %s opener %s lap j %s\n" % e)
    out.close(); print(open('divisible_members_v1.out').read()[len(__doc__):])
