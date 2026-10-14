r"""
nr2_unit_fibre  --  decide a WHOLE FIBRE at once.

For a fixed 4-tuple of unit speeds (e_1,e_3,e_5,e_7) the fibre is the infinite family
of base tuples obtained by adjoining e_rho0 = 8 q + rho0, rho0 in {2,4,6}, q >= 0.

The exact criteria (proved; verified in nr2_reflection.py / nr2_closures_v2.py) are

   rho0 = 4      |S^c| = |A n U| + 2 |A' n O|
   rho0 in {2,6} |S^c| = 2 ( |P_{e,K1} n O n W_K1| + |P_{e,K2} n O n W_K2| )

and the DISCREPANCY LEMMA (P periodic on R, period p, density delta; X a union of n
disjoint intervals of [0,1)  =>  | |X n P| - delta|X| | <= n delta(1-delta) p) gives,
with M = e_rho0/2 resp. e_rho0/4,

   rho0 in {2,6}  |S^c| <= o + n_O / M                     <= 1/2  once  M >= n_O/(1/2-o)
   rho0 = 4       |S^c| <= (o+u)/2 + (n_U + 3 n_O)/(4M)    <= 1/2  once
                                              M >= (n_U + 3 n_O)/(2(1-o-u))

So for each unit tuple only finitely many M need checking, and the check below is
exhaustive over that finite range.  A fibre that passes is closed for EVERY e_rho0 and
hence (with the B-lemma) for every m1 != m2.

Usage: python3 nr2_unit_fibre.py QMAX [MCAP]
"""
import itertools, sys
from math import gcd
from fractions import Fraction as F
from nr2_core import (MASK, OMASK, EMASK, ALL, ODD, EVEN, components, merge,
                      inter_measure, safe_measure)

QMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 5
MCAP = int(sys.argv[2]) if len(sys.argv) > 2 else 10 ** 9
HALF = F(1, 2)
K1 = frozenset({0, 4}); K2 = frozenset({2, 6})
NEED = {K: sum(1 << r for r in (set(range(0, 8, 2)) - set(K))) for K in (K1, K2)}


def pred_O(_R, st):
    c = 0
    for rho, t in zip((1, 3, 5, 7), st):
        c |= OMASK[(rho, t)]
    return c == ODD

def pred_U(_R, st):
    c = 0
    for rho, t in zip((1, 3, 5, 7), st):
        c |= MASK[(rho, t)]
    return c == ALL

def make_OW(K):
    need = NEED[K]
    def pred(_R, st):
        co = ce = 0
        for rho, t in zip((1, 3, 5, 7), st):
            co |= OMASK[(rho, t)]; ce |= EMASK[(rho, t)]
        return co == ODD and (ce & need) == need
    return pred
PRED_OW = {K: make_OW(K) for K in (K1, K2)}


def periodic_pieces(e0, resid):
    """merged interval list of { x : floor(e0 x) mod 8 in resid }"""
    out = []
    for j in range(e0):
        if j % 8 in resid:
            out.append((F(j, e0), F(j + 1, e0)))
    return merge(out)


def fibre(sp4, verbose=False):
    """returns (status, detail).  status in {'apriori', 'checked', 'FAIL'}"""
    Oc = merge(components(sp4, (1, 3, 5, 7), pred_O)[0])
    Uc = merge(components(sp4, (1, 3, 5, 7), pred_U)[0])
    OW = {K: merge(components(sp4, (1, 3, 5, 7), PRED_OW[K])[0]) for K in (K1, K2)}
    o = sum(b - a for a, b in Oc); u = sum(b - a for a, b in Uc)
    nO, nU = len(Oc), len(Uc)
    ow = {K: sum(b - a for a, b in OW[K]) for K in (K1, K2)}

    out = {}
    for rho0 in (2, 4, 6):
        if rho0 == 4:
            if u == 0 or u + 2 * o <= HALF:
                out[rho0] = ('apriori', None); continue
            if o + u >= 1:
                out[rho0] = ('FAIL', 'o+u>=1'); continue
            T = F(nU + 3 * nO, 2) / (1 - o - u)          # M >= T closes
        else:
            if o <= F(1, 4) or ow[K1] + ow[K2] <= F(1, 4):
                out[rho0] = ('apriori', None); continue
            if o >= HALF:
                out[rho0] = ('FAIL', 'o>=1/2'); continue
            T = F(nO) / (HALF - o)
        Tint = int(T) + 1
        if Tint > MCAP:
            out[rho0] = ('FAIL', f'threshold M<{Tint} exceeds cap'); continue
        worst = None
        for M in range(1, Tint + 1, 2):                 # M is odd
            e0 = (4 if rho0 == 4 else 2) * M
            if e0 % 8 != rho0:
                continue
            if rho0 == 4:
                A = periodic_pieces(e0, (1, 2, 5, 6))
                Ap = periodic_pieces(e0, (0, 7))
                sc = inter_measure(A, Uc) + 2 * inter_measure(Ap, Oc)
            else:
                pk = {K: [] for K in (K1, K2)}
                for j in range(e0):
                    s = frozenset(r for r in range(8) if (rho0 * r + j) % 8 in (0, 7))
                    if s in (K1, K2):
                        pk[s].append((F(j, e0), F(j + 1, e0)))
                sc = 2 * sum(inter_measure(merge(pk[K]), OW[K]) for K in (K1, K2))
            if worst is None or sc > worst[0]:
                worst = (sc, e0)
            if sc > HALF:
                out[rho0] = ('FAIL', f'|S^c| = {sc} > 1/2 at e_rho0 = {e0}')
                break
        else:
            out[rho0] = ('checked', (Tint, worst))
    return out


print(f"unit tuples q <= {QMAX}; deciding the whole e_rho0 fibre for each")
n = 0
apri = {2: 0, 4: 0, 6: 0}
chk = {2: 0, 4: 0, 6: 0}
fails = []
maxT = 0
for qs in itertools.product(range(QMAX + 1), repeat=4):
    sp4 = tuple(8 * q + r for q, r in zip(qs, (1, 3, 5, 7)))
    if len(set(sp4)) != 4:
        continue
    n += 1
    res = fibre(sp4)
    for rho0, (st, det) in res.items():
        if st == 'apriori':
            apri[rho0] += 1
        elif st == 'checked':
            chk[rho0] += 1
            maxT = max(maxT, det[0])
        else:
            fails.append((sp4, rho0, det))
    if n % 200 == 0:
        print(f"   ... {n} unit tuples done, failures so far {len(fails)}")
        sys.stdout.flush()
print(f"\n   unit tuples: {n}")
for rho0 in (2, 4, 6):
    print(f"   rho0={rho0}: closed a priori {apri[rho0]}, closed by finite check {chk[rho0]},"
          f" total {apri[rho0]+chk[rho0]} of {n}")
print(f"   largest finite-check threshold M < {maxT}")
print(f"   FAILURES: {len(fails)}")
for f in fails[:20]:
    print("      ", f)
