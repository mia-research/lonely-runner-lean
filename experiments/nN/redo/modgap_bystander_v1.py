"""modgap_bystander_v1 (2026-10-06): the strict bystander test.  Fix the necessary readings T (a minimal subset with cascade(T) = t*), vary one added
reading d over every integer 1..DMAX not in T, run the exact cascade on T + {d}.  t* = u/w in lowest terms (8 | w).
 B1 [P] cascade(T+{d}) = t* iff d u mod w lies in [w/8, 7w/8]  (T+{d} lonely at t*; Theorem 12: no lonely instant precedes the cascade's).  checked for every d.
 B2 [P] the allowed classes mod w are u^-1 times the arc: {d mod w : w <= 8 (d u mod w) <= 7 w} = u^-1 [w/8, 7w/8]; their number is #{r in Z/w : w <= 8r <= 7w},
        independent of u and of T.  checked: the number of allowed residues mod w, and that d and d + w are in the same class.
 B3 for a blocked d (not allowed): the new landing t' = cascade(T + {d}).  Categories: (i) d takes over: t' = (8 round(d t*) + 1)/(8d) (d's own edge from t*) and d is the
    opener of t'; (ii) t' is d's edge but another reading is the opener (cannot occur if t' lonely at its edge? recorded); (iii) t' later than d's edge: the chain continues
    (number of further moves).  Also the displacement (t' - t*) times d_max(T + {d}), reported as an exact fraction for the first examples.
 B4 the sizes: for blocked d, is d larger than max(T) (a faster reading)?  counts by category and by d <= max(T) / d > max(T).
Populations: the first 4,000 non-unit-fraction sets of S1 (T computed per set), the first 4,000 of T2 (as modgap_ancestor_v1); DMAX = 3 * 24 and 3 * 28.  Exact.
[PROVISIONAL: counting tool; supports: the category counts in B3/B4]"""
import itertools, math, collections, sys
sys.path.insert(0, '.')
from fractions import Fraction as F
from math import gcd
from functools import reduce
from modgap_lib_v1 import cascade, openers, component, simplest, cd, E8
def s1():
    for r in itertools.combinations(range(2, 25), 6): yield (1,) + r
def t2():
    for r in itertools.combinations(range(2, 29), 6):
        if r[-1] >= 25: yield (1,) + r
out = open('modgap_bystander_v1.out', 'w'); out.write(__doc__ + "\n")
for name, gen, DMAX in (('S1', s1(), 72), ('T2', t2(), 84)):
    c = collections.Counter(); ex = []; nset = 0; cnt_allowed = collections.Counter()
    for S in gen:
        if nset >= 4000: break
        t = cascade(S); tR, cl = component(S, t)
        if t < 1 and F(1, math.ceil(1 / tR)) >= t: continue
        nset += 1
        T = next(T for k in range(1, 8) for T in itertools.combinations(S, k) if cascade(list(T)) == t)
        u, w = t.numerator, t.denominator
        arc = sum(1 for r in range(w) if w <= 8 * r <= 7 * w)
        allowed = [d for d in range(1, w + 1) if w <= 8 * (d * u % w) <= 7 * w]
        c[('B2 #allowed residues mod w = #arc', len(allowed) == arc)] += 1
        uinv = pow(u, -1, w)
        c[('B2 allowed = u^-1 * arc (as classes)', set(a % w for a in allowed) == {uinv * r % w for r in range(w) if w <= 8 * r <= 7 * w})] += 1
        for d in range(1, DMAX + 1):
            if d in T: continue
            tp = cascade(list(T) + [d])
            ok = w <= 8 * (d * u % w) <= 7 * w
            c[('B1 stays at t* iff residue allowed', (tp == t) == ok)] += 1
            if ok: c['allowed'] += 1; continue
            c['blocked'] += 1
            edge = F(8 * round(d * t) + 1, 8 * d)
            op = [x for x in list(T) + [d] if (x * tp - E8).denominator == 1]
            big = d > max(T)
            if tp == edge and d in op: cat = 'i: d takes over (t\' = d\'s edge, d the opener)'
            elif tp == edge: cat = 'ii: t\' = d\'s edge, another reading is the opener'
            else: cat = 'iii: t\' later than d\'s edge (chain continues)'
            c[(cat, 'd > max T' if big else 'd <= max T')] += 1
            if tp != edge and len(ex) < 6: ex.append((T, str(t), d, str(edge), str(tp), op))
    out.write("\n==== %s: %d sets\n" % (name, nset))
    for k, v in sorted(c.items(), key=str): out.write("  %s: %d\n" % (k, v))
    out.write("  examples of (iii): (T, t*, d, d's edge, t', openers of t')\n")
    for e in ex: out.write("    %s\n" % (e,))
out.close(); print(open('modgap_bystander_v1.out').read()[len(__doc__):])
