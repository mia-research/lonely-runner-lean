r"""
nr2_closures_v2  --  the proved sufficient conditions in their sharpest a-priori form,
plus their coverage.  All measures exact.

Write O, V, U = O n V for the four unit runners (cover all odds / all evens / all of
Z/8), o = |O| = |V|, u = |U|.  For an even 2-element coset K of {0,4} in Z/8 put

    W_K = { x : the four units' EVEN elements cover  evens \ K } ,   so  W_K  contains V.

The two even cosets are K1 = {0,4} and K2 = {2,6}.

PROVED (see the report):

  rho0 = 4       |S^c| = |A n U| + 2|A' n O|,  |A| = 1/2, |A'| = |A''| = 1/4
                 => closes if   u = 0   or   u + 2 o <= 1/2 .

  rho0 in {2,6}  |S^c| = 2( |P_{e,K1} n O n W_K1| + |P_{e,K2} n O n W_K2| ),
                 |P_{e,K}| = 1/4 each
                 => closes if   o <= 1/4   or   |O n W_K1| + |O n W_K2| <= 1/4
                    (in particular if one of the two intersections is empty and the
                     other has measure <= 1/4).

  ALL rho0       L3 discrepancy: closes once e_rho0 exceeds an explicit threshold
                 built from o, u and the component counts of O and U.
"""
import itertools, sys
from math import gcd
from fractions import Fraction as F
from nr2_core import (MASK, OMASK, EMASK, ALL, ODD, EVEN, safe_measure,
                      components, P_sets, inter_measure, merge, O_components)

QMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 5
HALF = F(1, 2)
K1 = frozenset({0, 4})
K2 = frozenset({2, 6})
EVMASK = {K: sum(1 << r for r in (set(range(0, 8, 2)) - set(K))) for K in (K1, K2)}


def unit_pred_O(_R, st):
    c = 0
    for rho, t in zip((1, 3, 5, 7), st):
        c |= OMASK[(rho, t)]
    return c == ODD


def unit_pred_U(_R, st):
    c = 0
    for rho, t in zip((1, 3, 5, 7), st):
        c |= MASK[(rho, t)]
    return c == ALL


def make_pred_OW(K):
    need = EVMASK[K]
    def pred(_R, st):
        co = ce = 0
        for rho, t in zip((1, 3, 5, 7), st):
            co |= OMASK[(rho, t)]
            ce |= EMASK[(rho, t)]
        return co == ODD and (ce & need) == need
    return pred


PRED_OW = {K: make_pred_OW(K) for K in (K1, K2)}

cache = {}
def unitdata(sp4):
    if sp4 not in cache:
        Oc = merge(components(sp4, (1, 3, 5, 7), unit_pred_O)[0])
        Uc = merge(components(sp4, (1, 3, 5, 7), unit_pred_U)[0])
        o = sum(b - a for a, b in Oc)
        u = sum(b - a for a, b in Uc)
        ow = {}
        for K in (K1, K2):
            c = merge(components(sp4, (1, 3, 5, 7), PRED_OW[K])[0])
            ow[K] = (c, sum(b - a for a, b in c))
        cache[sp4] = (Oc, Uc, o, u, len(Oc), len(Uc), ow)
    return cache[sp4]


def A_sets(e4):
    A, Ap, App = [], [], []
    for j in range(e4):
        iv = (F(j, e4), F(j + 1, e4))
        r = j % 8
        (A if r in (1, 2, 5, 6) else Ap if r in (0, 7) else App).append(iv)
    return merge(A), merge(Ap), merge(App)


# ---- verify the rho0 in {2,6} identity |S^c| = 2(sum of the two K-terms)
print("verify: rho0 in {2,6},  |S^c| == 2( |P_{e,K1} n O n W_K1| + |P_{e,K2} n O n W_K2| )")
def PeK(rho0, e0):
    """the two pieces of P_even, indexed by the coset K = bad(rho0,t)"""
    out = {K1: [], K2: []}
    for j in range(e0):
        s = frozenset(r for r in range(8) if (rho0 * r + j) % 8 in (0, 7))
        if s in (K1, K2):
            out[frozenset(s)].append((F(j, e0), F(j + 1, e0)))
    return {K: merge(v) for K, v in out.items()}

bad = 0; n = 0
for rho0 in (2, 6):
    for qs in itertools.product(range(4), repeat=5):
        sp = tuple(8 * q + r for q, r in zip(qs, (1, 3, 5, 7, rho0)))
        if len(set(sp)) != 5:
            continue
        n += 1
        sc = 1 - safe_measure(sp, (1, 3, 5, 7, rho0))
        Oc, Uc, o, u, nO, nU, ow = unitdata(sp[:4])
        pk = PeK(rho0, sp[4])
        tot = sum(inter_measure(pk[K], ow[K][0]) for K in (K1, K2))
        if 2 * tot != sc:
            bad += 1
            if bad <= 3:
                print("   MISMATCH", sp, sc, 2 * tot)
print(f"   {n} tuples (q <= 3): identity fails {bad} times")

# ---- coverage
print(f"\nCOVERAGE over primitive base tuples, q <= {QMAX}")
grand = [0, 0, 0]
for rho0 in (2, 4, 6):
    rhos = (1, 3, 5, 7, rho0)
    n = c2 = c3 = res = 0
    residual = []
    for qs in itertools.product(range(QMAX + 1), repeat=5):
        sp = tuple(8 * q + r for q, r in zip(qs, rhos))
        if len(set(sp)) != 5:
            continue
        g = 0
        for e in sp:
            g = gcd(g, e)
        if g != 1:
            continue
        n += 1
        Oc, Uc, o, u, nO, nU, ow = unitdata(sp[:4])
        e0 = sp[4]
        if rho0 == 4:
            apriori = (u == 0) or (u + 2 * o <= HALF)
            M = F(e0, 4)
            disc = ((o + u) / 2 + F(nU + 3 * nO, 4) / M) < HALF
        else:
            apriori = (o <= F(1, 4)) or (ow[K1][1] + ow[K2][1] <= F(1, 4))
            M = F(e0, 2)
            disc = (o + F(nO) / M) < HALF
        if apriori:
            c2 += 1
        elif disc:
            c3 += 1
        else:
            res += 1
            if len(residual) < 8:
                residual.append(sp)
    grand[0] += n; grand[1] += c2 + c3; grand[2] += res
    print(f"   rho0={rho0}: primitive {n};  a-priori lemma {c2} ({100*c2/n:.2f}%);"
          f"  discrepancy {c3} ({100*c3/n:.2f}%);  RESIDUAL {res} ({100*res/n:.2f}%)")
    if residual:
        print(f"      residual examples: {residual}")
print(f"   TOTAL: {grand[0]} primitive tuples, closed {grand[1]} ({100*grand[1]/grand[0]:.2f}%),"
      f" residual {grand[2]} ({100*grand[2]/grand[0]:.2f}%)")
