r"""
hp_fibre_v2 -- the fibre criterion CORRECTED for the reduction.

The reduction removes every 5-tuple with gcd(E_non) >= 3.  gcd(E_non) =
gcd(g4, e_rho0) with g4 = gcd of the four unit speeds, and g4 is odd, so the
5-tuple survives iff gcd(g4, e_rho0) = 1.  nr2_unit_fibre.fibre() scans the WHOLE
fibre including the non-primitive members, and that is why the dilation orbit
lam*(1,3,5,7) shows up as a failure: its only failing member is e_rho0 = 4*lam,
which has gcd(E_non) = lam >= 3 and is therefore already removed.

This module restricts the finite check to the primitive members, and additionally
excludes the single representative 5-tuple (1,3,5,7,4) (that one is genuinely
|S| = 5/14 < 1/2 and is closed by Lemma D, not by a measure bound).

usage: python3 hp_fibre_v2.py QMAX [MCAP]
"""
import itertools, sys
from math import gcd
from fractions import Fraction as F
from nr2_core import MASK, OMASK, EMASK, ALL, ODD, EVEN, components, merge, inter_measure
from nr2_unit_fibre import pred_O, pred_U, PRED_OW, periodic_pieces, K1, K2

HALF = F(1, 2)
R4 = (1, 3, 5, 7)
REPRESENTATIVE = ((1, 3, 5, 7), 4, 4)          # (unit tuple, rho0, e_rho0) -- Lemma D


def unit_data(sp4):
    Oc = merge(components(sp4, R4, pred_O)[0])
    Uc = merge(components(sp4, R4, pred_U)[0])
    OW = {K: merge(components(sp4, R4, PRED_OW[K])[0]) for K in (K1, K2)}
    o = sum(b - a for a, b in Oc); u = sum(b - a for a, b in Uc)
    return Oc, Uc, OW, o, u, len(Oc), len(Uc)


def sc_bound(rho0, e0, Oc, Uc, OW):
    """the exact |S^c| expression of the fibre criterion at this e_rho0"""
    if rho0 == 4:
        A = periodic_pieces(e0, (1, 2, 5, 6))
        Ap = periodic_pieces(e0, (0, 7))
        return inter_measure(A, Uc) + 2 * inter_measure(Ap, Oc)
    pk = {K1: [], K2: []}
    for j in range(e0):
        s = frozenset(r for r in range(8) if (rho0 * r + j) % 8 in (0, 7))
        if s in (K1, K2):
            pk[s].append((F(j, e0), F(j + 1, e0)))
    return 2 * sum(inter_measure(merge(pk[K]), OW[K]) for K in (K1, K2))


def fibre2(sp4, mcap=10 ** 9):
    g4 = 0
    for e in sp4:
        g4 = gcd(g4, e)
    Oc, Uc, OW, o, u, nO, nU = unit_data(sp4)
    ow = {K: sum(b - a for a, b in OW[K]) for K in (K1, K2)}
    out = {}
    for rho0 in (2, 4, 6):
        if rho0 == 4:
            if u == 0 or u + 2 * o <= HALF:
                out[rho0] = ('apriori', None); continue
            if o + u >= 1:
                out[rho0] = ('FAIL', f'o+u = {o+u} >= 1  (threshold infinite)'); continue
            T = F(nU + 3 * nO, 2) / (1 - o - u)
        else:
            if o <= F(1, 4) or ow[K1] + ow[K2] <= F(1, 4):
                out[rho0] = ('apriori', None); continue
            if o >= HALF:
                out[rho0] = ('FAIL', f'o = {o} >= 1/2  (threshold infinite)'); continue
            T = F(nO) / (HALF - o)
        Tint = int(T) + 1
        if Tint > mcap:
            out[rho0] = ('FAIL', f'threshold M<{Tint} exceeds cap'); continue
        worst = None; failed = None
        step = 4 if rho0 == 4 else 2
        for M in range(1, Tint + 1, 2):
            e0 = step * M
            if e0 % 8 != rho0:
                continue
            if gcd(g4, e0) != 1:                       # removed by the reduction
                continue
            if (tuple(sp4), rho0, e0) == REPRESENTATIVE:   # Lemma D
                continue
            sc = sc_bound(rho0, e0, Oc, Uc, OW)
            if worst is None or sc > worst[0]:
                worst = (sc, e0)
            if sc > HALF:
                failed = (sc, e0); break
        out[rho0] = ('FAIL', f'|S^c| = {failed[0]} > 1/2 at e_rho0 = {failed[1]}') \
            if failed else ('checked', (Tint, worst))
    return out


if __name__ == "__main__":
    QMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 5
    MCAP = int(sys.argv[2]) if len(sys.argv) > 2 else 10 ** 9
    n = 0; apri = {2: 0, 4: 0, 6: 0}; chk = {2: 0, 4: 0, 6: 0}
    fails = []; maxT = 0; maxTat = None
    for qs in itertools.product(range(QMAX + 1), repeat=4):
        sp4 = tuple(8 * q + r for q, r in zip(qs, R4))
        if len(set(sp4)) != 4:
            continue
        n += 1
        res = fibre2(sp4, MCAP)
        for rho0, (st, det) in res.items():
            if st == 'apriori':
                apri[rho0] += 1
            elif st == 'checked':
                chk[rho0] += 1
                if det[0] > maxT:
                    maxT, maxTat = det[0], (sp4, rho0)
            else:
                fails.append((sp4, rho0, det))
        if n % 500 == 0:
            print(f"   ... {n} tuples, failures {len(fails)}"); sys.stdout.flush()
    print(f"\nQMAX={QMAX}: unit tuples {n} (ALL of them, primitive or not)")
    for rho0 in (2, 4, 6):
        print(f"   rho0={rho0}: a priori {apri[rho0]}, finite check {chk[rho0]},"
              f" total {apri[rho0]+chk[rho0]} of {n}")
    print(f"   largest finite-check threshold M < {maxT}  at {maxTat}")
    print(f"   FAILURES: {len(fails)}")
    for f in fails[:20]:
        print("      ", f)
