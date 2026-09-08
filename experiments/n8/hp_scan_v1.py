r"""
hp_scan_v1 -- exact scan of the unit-4-tuple invariants (o, u, component counts,
the W_K refinements) over unit tuples, split by gcd of the 4 unit speeds.

Purpose: locate the extremes of  o,  u,  u+o,  u+2o  among PRIMITIVE unit tuples,
and record which tuples attain them.  Exact Fractions throughout.

usage:  python3 hp_scan_v1.py QMAX
"""
import itertools, sys
from math import gcd
from fractions import Fraction as F
from nr2_core import MASK, OMASK, EMASK, ALL, ODD, EVEN, components, merge

QMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 5
R4 = (1, 3, 5, 7)
K1 = frozenset({0, 4}); K2 = frozenset({2, 6})
NEED = {K: sum(1 << r for r in (set(range(0, 8, 2)) - set(K))) for K in (K1, K2)}


def pred_O(_R, st):
    c = 0
    for rho, t in zip(R4, st):
        c |= OMASK[(rho, t)]
    return c == ODD


def pred_U(_R, st):
    c = 0
    for rho, t in zip(R4, st):
        c |= MASK[(rho, t)]
    return c == ALL


def make_OW(K):
    need = NEED[K]
    def p(_R, st):
        co = ce = 0
        for rho, t in zip(R4, st):
            co |= OMASK[(rho, t)]; ce |= EMASK[(rho, t)]
        return co == ODD and (ce & need) == need
    return p


PRED_OW = {K: make_OW(K) for K in (K1, K2)}


def invariants(sp4):
    Oc = merge(components(sp4, R4, pred_O)[0])
    Uc = merge(components(sp4, R4, pred_U)[0])
    o = sum(b - a for a, b in Oc)
    u = sum(b - a for a, b in Uc)
    ow = {}
    for K in (K1, K2):
        c = merge(components(sp4, R4, PRED_OW[K])[0])
        ow[K] = (sum(b - a for a, b in c), len(c))
    return o, u, len(Oc), len(Uc), ow


def gcd4(t):
    g = 0
    for e in t:
        g = gcd(g, e)
    return g


best = {}


def note(key, val, sp4, extra=""):
    if key not in best or val > best[key][0]:
        best[key] = (val, sp4, extra)


n_prim = n_all = 0
prim_fail_apriori4 = []
prim_fail_apriori26 = []
for qs in itertools.product(range(QMAX + 1), repeat=4):
    sp4 = tuple(8 * q + r for q, r in zip(qs, R4))
    if len(set(sp4)) != 4:
        continue
    n_all += 1
    g = gcd4(sp4)
    o, u, nO, nU, ow = invariants(sp4)
    if g == 1:
        n_prim += 1
        note("o", o, sp4)
        note("u", u, sp4)
        note("u+o", u + o, sp4)
        note("u+2o", u + 2 * o, sp4)
        note("owsum", ow[K1][0] + ow[K2][0], sp4)
        note("nO", F(nO), sp4)
        note("nU", F(nU), sp4)
        if not (u == 0 or u + 2 * o <= F(1, 2)):
            prim_fail_apriori4.append((sp4, o, u, nO, nU))
        if not (o <= F(1, 4) or ow[K1][0] + ow[K2][0] <= F(1, 4)):
            prim_fail_apriori26.append((sp4, o, u, ow[K1][0] + ow[K2][0]))
    else:
        note("g>1:u+2o", u + 2 * o, sp4, f"g={g}")

print(f"QMAX={QMAX}  unit tuples {n_all}, primitive {n_prim}")
for k in ("o", "u", "u+o", "u+2o", "owsum", "nO", "nU", "g>1:u+2o"):
    if k in best:
        v, sp, ex = best[k]
        print(f"  max {k:10s} = {v}  ({float(v):.6f})   at {sp} {ex}")
print(f"  primitive tuples failing the rho0=4 a-priori test : {len(prim_fail_apriori4)}")
print(f"  primitive tuples failing the rho0 in 2,6 a-priori : {len(prim_fail_apriori26)}")
for t in prim_fail_apriori4[:12]:
    print("     4 :", t)
for t in prim_fail_apriori26[:12]:
    print("    26 :", t)
