"""Exact checker for the band covering conditions (agent_caseB_A).

Conditions checked
  G1(i)        the two-block gap condition (L2), stated as a gap condition:
               g_i = s_i/s_{i-1} >= 9/7 and s_6 <= (5/3) s_i, i = 1..6;  R = 9/s_i.
  T[e,K,lam]   cluster-type conditions (derivation.md Sec. 2), read from TYPES_FILE:
               for each maximal run a..b of equal lap k in lam:
                   (8k+1) s_e <= (8K+1) s_a   and   (8K+1) s_b <= (8k+7) s_e ;
               R = (8K+1)/s_e.
Negative controls (must be CAUGHT by the soundness check)
  BAD_G1       G1 with the gap threshold lowered to 8/7.
  BAD_T        the most-used type with every upper window end widened by 1/2 lap unit
               ((8k+7) -> (8k+15/2)).

(a) SOUNDNESS: on every set where a condition fires (decided by the condition's own
    inequalities, integer arithmetic), the named R is checked independently with
    Fractions: R in [1,7] u [9,15] and every reading clear at R.
(b) COVERAGE on: all integer band sets with readings <= 24; <= 32; the fine shapes in
    fine_shapes.txt (denominator 2520, incl. late walks).
(c) prints the first 50 uncovered sets of each dataset and the count.
Positive controls: (i) the landing oracle (core.landing) finds a lonely R for every set;
(ii) on the fine shapes and on ints<=24, every type is evaluated by brute force and the
     result compared with the lap-indexed evaluation used for speed on ints<=32.
No floating point in any decision.
"""
import sys, json, time
from fractions import Fraction as F
from core import integer_band_sets, lonely_at, in_range, landing, candidates

TYPES_FILE = sys.argv[1] if len(sys.argv) > 1 else 'types_final.json'
DATASETS = sys.argv[2].split(',') if len(sys.argv) > 2 else ['int24', 'int32', 'fine']


# ------------------------------------------------------------------ conditions

def G1(ns, i, num=9, den=7):
    """gap condition L2 at position i; returns R or None."""
    if den * ns[i] >= num * ns[i - 1] and 3 * ns[6] <= 5 * ns[i]:
        return F(9 * ns[0], ns[i])
    return None


def type_cons(e, K, lam, widen=False):
    m = 8 * K + 1
    cons = []  # (a, b, qnum, qden): n_a * qden <= qnum * n_b
    d = 0
    while d < 7:
        k = lam[d]; lo = d
        while d + 1 < 7 and lam[d + 1] == k:
            d += 1
        hi = d
        if lo != e:
            cons.append((e, lo, m, 8 * k + 1))              # s_e <= m/(8k+1) s_lo
        if hi != e:
            if widen:
                cons.append((hi, e, 16 * k + 15, 2 * m))    # s_hi <= (8k+15/2)/m s_e
            else:
                cons.append((hi, e, 8 * k + 7, m))          # s_hi <= (8k+7)/m s_e
        d += 1
    return cons


def T_fires(ns, cons):
    for a, b, qn, qd in cons:
        if ns[a] * qd > qn * ns[b]:
            return False
    return True


def T_R(ns, e, K):
    return F((8 * K + 1) * ns[0], ns[e])


def laps_at(ns, e, K):
    m = 8 * K + 1
    return tuple((m * nd) // (8 * ns[e]) for nd in ns)


# ------------------------------------------------------------------ datasets

def load(name):
    if name == 'int24':
        return list(integer_band_sets(24))
    if name == 'int32':
        return list(integer_band_sets(32))
    if name == 'fine':
        out = []
        for l in open('fine_shapes.txt'):
            r = l.split(); out.append(tuple(map(int, r[:7])))
        return out
    raise ValueError(name)


def main():
    types = [(t[0][0], t[0][1], tuple(t[1])) for t in json.load(open(TYPES_FILE))['types']]
    typeset = set(types)
    by_eK = {}
    for e, K, lam in types:
        by_eK.setdefault((e, K), set()).add(lam)
    tcons = {t: type_cons(*t) for t in types}
    print(f"types loaded: {len(types)} from {TYPES_FILE}")
    bad_t = types[0]
    bad_cons = type_cons(*bad_t, widen=True)

    grand_unsound = 0
    for name in DATASETS:
        t0 = time.time()
        sets = load(name)
        brute = name in ('fine', 'int24')
        fired = {'G1': 0, 'T': 0, 'BAD_G1': 0, 'BAD_T': 0}
        unsound = {'G1': [], 'T': [], 'BAD_G1': [], 'BAD_T': []}
        cov_G1 = 0; cov_T = 0; cov_any = 0
        uncovered = []; no_landing = []; brute_mismatch = 0
        for ns in sets:
            # positive control: target holds at this set (independent oracle)
            if landing(ns) is None:
                no_landing.append(ns)
            covered = False; g1 = False
            for i in range(1, 7):
                R = G1(ns, i)
                if R is not None:
                    fired['G1'] += 1; g1 = True
                    if not (in_range(R) and lonely_at(ns, R)):
                        unsound['G1'].append((ns, i, R))
                R = G1(ns, i, 8, 7)
                if R is not None:
                    fired['BAD_G1'] += 1
                    if not (in_range(R) and lonely_at(ns, R)):
                        unsound['BAD_G1'].append((ns, i, R))
            if T_fires(ns, bad_cons):
                fired['BAD_T'] += 1
                R = T_R(ns, bad_t[0], bad_t[1])
                if not (in_range(R) and lonely_at(ns, R)):
                    unsound['BAD_T'].append((ns, bad_t, R))
            # type conditions: a type (e,K,lam) can fire only if lam = laps_at(ns,e,K)
            # (its inequalities place every reading in lap lam_d); evaluate those.
            firing = set()
            for (e, K), lams in by_eK.items():
                lam = laps_at(ns, e, K)
                if lam in lams and T_fires(ns, tcons[(e, K, lam)]):
                    firing.add((e, K, lam))
            if brute:
                full = set(t for t in types if T_fires(ns, tcons[t]))
                if full != firing:
                    brute_mismatch += 1
            for t in firing:
                fired['T'] += 1
                R = T_R(ns, t[0], t[1])
                if not (in_range(R) and lonely_at(ns, R)):
                    unsound['T'].append((ns, t, R))
            if g1: cov_G1 += 1
            if firing: cov_T += 1
            if g1 or firing: cov_any += 1
            else: uncovered.append(ns)
        n = len(sets)
        print(f"\n=== dataset {name}: {n} band sets  ({time.time()-t0:.0f}s)")
        print(f"  positive control, landing oracle finds lonely R: {n-len(no_landing)}/{n}")
        if brute:
            print(f"  brute-force vs lap-indexed type evaluation mismatches: {brute_mismatch}")
        for c in ('G1', 'T', 'BAD_G1', 'BAD_T'):
            print(f"  {c:7s} fired {fired[c]:8d}   unsound {len(unsound[c])}"
                  + ("   <- negative control" if c.startswith('BAD') else ""))
            for u in unsound[c][:3]:
                print("        e.g.", u)
        grand_unsound += len(unsound['G1']) + len(unsound['T'])
        print(f"  coverage: G1 alone {cov_G1}/{n}; types alone {cov_T}/{n}; union {cov_any}/{n}")
        print(f"  uncovered: {len(uncovered)}")
        for u in uncovered[:50]:
            print("     ", u, [str(F(x, u[0])) for x in u])
        neg_ok = len(unsound['BAD_G1']) > 0 or fired['BAD_G1'] == 0
        print(f"  negative control BAD_G1 caught: {len(unsound['BAD_G1']) > 0}; "
              f"BAD_T caught: {len(unsound['BAD_T']) > 0} (fired {fired['BAD_T']})")
    print(f"\nTOTAL unsound firings of real conditions: {grand_unsound}")


if __name__ == '__main__':
    main()
