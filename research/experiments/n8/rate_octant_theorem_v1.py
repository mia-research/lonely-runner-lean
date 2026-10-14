"""
rate_octant_theorem_v1.py

Main theorem for the n=8 unit-complete five-runner fibre step, plus an
INDEPENDENT verification path that never uses the a_rho reparametrisation.

THEOREM (octant fibres).  Let 8 | L, let e_1,e_3,e_5,e_7,e_{rho0} be positive
integers with e_rho = rho (mod 8), rho0 in {2,4,6}.  Then there is
c in {1,...,7} such that b = c*L/8 lies in B_div and T(b) is not in BAD(rho0).

Proof engine: T(c*L/8)_rho = (c*a_rho + floor(c*rho/8)) mod 8 with
a_rho = (e_rho - rho)/8, so the state at the seven octant fibres is a function
of A = (a_rho mod 8) in (Z/8)^5 alone -- 32768 cases, checked exhaustively.

Verification path 2 builds actual (L, e_rho) tuples and evaluates
floor(e_rho * b / L) directly with Python integers.

Exact integer arithmetic only.
"""

import random
from itertools import product, combinations

from rate_bad_states_v1 import build_bad, RHOS_UNIT

CS = tuple(range(1, 8))


def good_cs(A, rho0, bad):
    """Which c in 1..7 give a SAFE octant fibre, from A = (a_rho mod 8)."""
    rhos = RHOS_UNIT + (rho0,)
    out = []
    for c in CS:
        T = tuple((c * A[i] + (c * rhos[i]) // 8) % 8 for i in range(5))
        if T not in bad:
            out.append(c)
    return tuple(out)


# ---------------------------------------------------------------- path 1
def exhaustive(rho0, bad):
    """Full sweep of (Z/8)^5.  Returns (min #good c, histogram, worst A list,
    all distinct good-c sets encountered)."""
    hist = {}
    worst = []
    best = 8
    sets_seen = set()
    for A in product(range(8), repeat=5):
        g = good_cs(A, rho0, bad)
        sets_seen.add(g)
        hist[len(g)] = hist.get(len(g), 0) + 1
        if len(g) < best:
            best, worst = len(g), [A]
        elif len(g) == best:
            worst.append(A)
    return best, hist, worst, sets_seen


def minimal_c_subsets(sets_seen):
    """Smallest S subset of {1..7} meeting every good-c set (i.e. S alone proves it)."""
    for k in range(1, 8):
        hits = [S for S in combinations(CS, k)
                if all(set(S) & set(g) for g in sets_seen)]
        if hits:
            return k, hits
    return None, []


# ---------------------------------------------------------------- path 2
def direct_state(L, es, rho0):
    """T(b) at b = c*L/8 computed straight from floor(e*b/L); no reparametrisation."""
    assert L % 8 == 0
    out = {}
    for c in CS:
        b = c * (L // 8)
        assert L // 8 <= b <= 7 * L // 8
        out[c] = tuple((e * b) // L % 8 for e in es)
    return out


def sample_instances(rho0, bad, trials=200000, seed=20260907):
    """Random admissible-shaped instances, checked with the direct evaluator.
    Also cross-checks path 1 against path 2 state by state."""
    rnd = random.Random(seed)
    rhos = RHOS_UNIT + (rho0,)
    fails = []
    mismatch = []
    for _ in range(trials):
        es = []
        for r in rhos:
            k = rnd.randrange(0, 60)
            es.append(8 * k + r)
        # L must be a multiple of 8 and of every e (each e divides L in the
        # real setting).  Use L = 8 * lcm(es) -- the strongest such shape.
        from math import lcm
        L = 8 * lcm(*es)
        st = direct_state(L, es, rho0)
        A = tuple(((e - r) // 8) % 8 for e, r in zip(es, rhos))
        for c in CS:
            pred = tuple((c * A[i] + (c * rhos[i]) // 8) % 8 for i in range(5))
            if pred != st[c]:
                mismatch.append((es, L, c, pred, st[c]))
        if all(st[c] in bad for c in CS):
            fails.append((es, L))
    return fails, mismatch


# ---------------------------------------------------------------- degenerate
def degenerate_cases(rho0, bad):
    """Small speeds, repeated jump structure, e_rho = 1, e_5|e_7 etc.
    Every such family is just a particular A, so it is already covered; this
    enumerates named ones and confirms."""
    rhos = RHOS_UNIT + (rho0,)
    fams = []
    # (a) all speeds minimal (e_rho = rho): the most degenerate possible
    fams.append(("all minimal e_rho = rho", list(rhos)))
    # (b) e_1 = 1 -> m_1 = L, coordinate 1 FROZEN across all of B_div
    fams.append(("e_1=1 frozen", [1, 3, 5, 7, rho0]))
    # (c) nested jump structure: e_5 = 5 | e_7 = 15  (15 = 7 mod 8), m_5 = 3*m_7
    #     NB the prompt's suggested e_7 = 35 is NOT admissible: 35 = 3 (mod 8).
    fams.append(("e_5=5 | e_7=15 nested", [1, 3, 5, 15, rho0]))
    # (d) e_3 = 3 | e_5 = 21  (21 = 5 mod 8)
    fams.append(("e_3=3 | e_5=21 nested", [1, 3, 21, 7, rho0]))
    # (e) chain 1 | 3 | 21 | ... plus a large non-unit
    fams.append(("large non-unit", [1, 3, 5, 7, rho0 + 8 * 97]))
    # (f) every speed large and coprime-ish
    fams.append(("all large", [8*11+1, 8*13+3, 8*17+5, 8*19+7, 8*23+rho0]))
    # (g) all a_rho = 0 mod 8 (the c=1 state is A=0, deep inside BAD for rho0=4)
    fams.append(("a_rho = 0 mod 8", [8*8+1, 8*8+3, 8*8+5, 8*8+7, 8*8+rho0]))
    res = []
    from math import lcm
    for name, es in fams:
        assert all(e % 8 == r % 8 for e, r in zip(es, rhos)), (name, es)
        L = 8 * lcm(*es)
        st = direct_state(L, es, rho0)
        g = [c for c in CS if st[c] not in bad]
        res.append((name, es, L, g))
    return res


def main():
    bads = {r: build_bad(r) for r in (2, 4, 6)}
    all_sets = set()
    print("=== PATH 1: exhaustive over A in (Z/8)^5 ===")
    for rho0 in (2, 4, 6):
        best, hist, worst, sets_seen = exhaustive(rho0, bads[rho0])
        all_sets |= sets_seen
        print(f"rho0={rho0}: min number of SAFE octant fibres over all 32768 A = {best}")
        print(f"          histogram (#safe c -> #A): "
              f"{ {k: hist[k] for k in sorted(hist)} }")
        print(f"          #A attaining the minimum = {len(worst)}; e.g. {worst[:4]}")
        if best == 0:
            print("          *** FAILURE: some A has no safe octant fibre ***")
    print()

    k, hits = minimal_c_subsets(all_sets)
    print(f"minimal subset of c in 1..7 that already suffices for ALL rho0 and ALL A: "
          f"size {k}")
    print(f"  number of such subsets = {len(hits)}; all of them: {hits}")
    print()

    print("=== PATH 2: independent direct evaluation, no reparametrisation ===")
    for rho0 in (2, 4, 6):
        fails, mism = sample_instances(rho0, bads[rho0], trials=40000)
        print(f"rho0={rho0}: random instances 40000  |  "
              f"reparametrisation mismatches = {len(mism)}  |  "
              f"instances with NO safe octant fibre = {len(fails)}")
        if mism:
            print("   *** ", mism[:3])
    print()

    print("=== degenerate / coincident-jump families (direct evaluation) ===")
    for rho0 in (2, 4, 6):
        for name, es, L, g in degenerate_cases(rho0, bads[rho0]):
            print(f"rho0={rho0}  {name:26s} e={es}  L={L}  safe c = {g}")


if __name__ == "__main__":
    main()
