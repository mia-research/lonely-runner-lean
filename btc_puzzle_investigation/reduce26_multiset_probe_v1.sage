#!/usr/bin/env sage
"""reduce26_multiset_probe_v1.sage -- the strongest diagnostic for #26's Frobenius-stratum equality.

The pair-space identity (#26) says Sum_conj chi_2(y1 y2) = Sum_rat_distinct chi_2(y1 y2) for every R.
That is an equality of SUMS. The much stronger statement: the MULTISETS {chi_2(y1 y2)} agree on the
two strata (split rational pairs vs inert conjugate pairs). If the multisets agree, there is a
BIJECTION between the strata preserving chi_2(y1 y2) -- which would identify the mechanism (and the
bijection, by the E[2] obstruction, cannot be a simple translation; it would be a richer correspondence).

This script computes, for each R, the sorted multiset of chi_2(y1 y2) values on each stratum, and
checks: (a) do the multisets agree? (b) if not, how do the count-distributions of +1/-1/0 compare?

EXACT F_p / F_{p^2} arithmetic.
"""
from sage.all import GF, EllipticCurve, ZZ
from collections import Counter


def chi2(a, p):
    a = int(a) % p
    if a == 0: return 0
    return 1 if pow(a, (p-1)//2, p) == 1 else -1


def stratum_multisets(p, A, B, e):
    """For R=[e]G: return (rat_multiset, conj_multiset) of chi_2(y1 y2), excluding the diagonal P0
    from the rational stratum (so both strata are 'distinct pairs')."""
    Fp = GF(p); Fp2 = GF(p**2, 'a')
    E = EllipticCurve(Fp, [A, B]); n = E.order()
    G = next(P for P in E if P.order() == n)
    R = e*G
    if R.is_zero(): return None
    E2 = E.change_ring(Fp2); R2 = E2(R[0], R[1])
    seen = set(); rat = []; conj = []
    for x1 in Fp2:
        rhs = x1**3 + A*x1 + B
        if not rhs.is_square(): continue
        y1 = rhs.sqrt()
        for sg in (1,-1):
            P1 = E2(x1, sg*y1); P2 = R2 - P1
            if P1.is_zero() or P2.is_zero(): continue
            inFp = (P1[0] in Fp) and (P1[1] in Fp)
            Pf = E2(P1[0]**p, P1[1]**p)
            is_conj = (Pf == P2) and not inFp
            is_rat = inFp and (P2[0] in Fp)
            if not (is_conj or is_rat): continue
            key = frozenset((tuple(P1), tuple(P2)))
            if key in seen: continue
            seen.add(key)
            py = P1[1]*P2[1]
            if py != py**p: continue
            c = chi2(py, p)
            if is_rat:
                # exclude the diagonal P0 (P1==P2)
                if tuple(P1) == tuple(P2): continue
                rat.append(c)
            else:
                conj.append(c)
    return sorted(rat), sorted(conj), R


if __name__ == "__main__":
    print("#26 multiset probe: do split/inert strata have the SAME chi_2(y1 y2) multiset per R?\n")
    for (p,A,B,lab) in [(43,0,7,"j=0"),(79,1,4,"generic"),(73,1,3,"eps+1"),(127,0,3,"j=0 larger")]:
        print("="*64); print("p=%d E:y^2=x^3+%dx+%d (%s)"%(p,A,B,lab))
        all_match = True; details = []
        for e in range(1, 12):
            res = stratum_multisets(p,A,B,e)
            if res is None: continue
            rat, conj, R = res
            match = (rat == conj)
            if not match: all_match = False
            rc = Counter(rat); cc = Counter(conj)
            details.append((e, len(rat), len(conj), dict(rc), dict(cc), match,
                            sum(rat), sum(conj)))
        # print compact: for each e, the +/- counts on each stratum
        for (e, nr, nc, rc, cc, m, sr, sc) in details:
            mark = "MULTISET MATCH" if m else "sums-eq-multisets-differ"
            print("  R=[%2d]G: rat(%2d:%s) sum=%3d | conj(%2d:%s) sum=%3d | %s"
                  % (e, nr, "+%d/-0"%rc.get(1,0) if rc.get(-1,0)==0 else "+%d/-%d"%(rc.get(1,0),rc.get(-1,0)),
                     sr, nc, "+%d/-%d"%(cc.get(1,0),cc.get(-1,0)), sc, mark))
        print("  -> ALL R multiset-match:" , all_match)
