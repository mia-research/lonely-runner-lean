"""E163: bridges through the cascade.  For every chain (Case B to readings <= 24; late fine band shapes): each bridge
a -> b (b faster on a later lap, or slower on an earlier lap) with a's exit lap k.  (1) Does the same ordered pair bridge
more than once in one chain, and at what lap gaps?  (2) For whole-number readings with b/a = p/r in lowest terms, the
bridge condition ||(8k+1) b/(8a)|| < 1/8 depends only on k mod r: check that every recurrence gap is a multiple of r is
NOT required (the condition can hold for several residues of k mod r); record gaps against r.  (3) What ends each
chain: the last move's type.  Exact."""
import itertools, random, sys
from fractions import Fraction as F
from math import floor, gcd
from collections import Counter, defaultdict
sys.path.insert(0, '../band_cert_v1'); from core import clear_set
E8 = F(1, 8)
def nd(x):
    x = x % 1
    return min(x, 1 - x)
def chain(T):
    t = F(1, 8 * T[0]); mv = []
    while True:
        W = [d for d in T if nd(d * t) < E8]
        if not W: return mv
        ex = {d: (F(floor(d * t - E8) + 1) + E8) / d for d in W}
        t2 = max(ex.values()); a = max(W, key=lambda d: ex[d]); mv.append((a, floor(a * t2))); t = t2
def study(sets, whole):
    rec = Counter(); last = Counter(); gaps = Counter()
    for T in sets:
        mv = chain(T)
        if not mv: last['lands at the bound'] += 1; continue
        seen = defaultdict(list)
        types = []
        for (a, ka), (b, kb) in zip(mv, mv[1:]):
            typ = 'sweep' if (b < a and kb == ka) else 'bridge'
            types.append(typ)
            if typ == 'bridge': seen[(a, b)].append(ka)
        last['last handover: %s' % (types[-1] if types else 'none (one move)')] += 1
        for (a, b), ks in seen.items():
            if len(ks) > 1:
                rec['bridge pair recurs in the chain'] += 1
                if whole:
                    r = b // gcd(a, b) if False else a // gcd(a, b)
                    for x, y in zip(ks, ks[1:]): gaps['gap %d, ratio denominator r = %d, gap multiple of r: %s' % (y - x, r, (y - x) % r == 0)] += 1
            else: rec['bridge pair once'] += 1
    return rec, last, gaps
caseB = [T for T in itertools.combinations(range(1, 25), 7) if 7 * T[0] < T[-1] <= 24 * T[0]]
r1 = study(caseB, True)
print("== Case B to 24"); [print("  %7d  %s" % (v, k)) for C in r1 for k, v in sorted(C.items(), key=lambda kv: -kv[1])[:10]]
D1 = 27720; rng = random.Random(41); late = set()
for sd in [(1, 2.3509, 3.2412, 4.1886, 5.2223, 5.7871, 7.4378), (1, 2.5302, 3.2218, 4.1563, 4.531, 5.6544, 7.0302)]:
    T = [int(round(x * D1)) for x in sd]
    for step in range(3000):
        U = list(T); i = rng.randrange(1, 7); U[i] += rng.randrange(-500, 501); U = sorted(set(U))
        if len(U) < 7 or U[0] != D1 or not (7 * D1 < U[-1] < 9 * D1): continue
        if clear_set([F(d, D1) for d in U], F(1), F(7)): continue
        T = U; late.add(tuple(U))
r2 = study(sorted(late), False)
print("== late fine band shapes"); [print("  %7d  %s" % (v, k)) for C in r2[:2] for k, v in sorted(C.items(), key=lambda kv: -kv[1])[:10]]
