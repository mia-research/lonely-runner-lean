"""
bridge_safe_fibre_to_k_v1.py  --  n = 8 audit of the load-bearing bridge

    "there exists a safe fibre b in B_div"  ==>  "x_0(E) >= 1"

of lrc_proof_v10_21.md (sections 2.4, 5.1, 5.3, 9.6, 11.2).

Definitions used (all exactly as in the manuscript, section 5.1 / 1.2):

    n     = 8
    E     = (e_1,...,e_7) distinct positive integers, gcd(E) = 1
    L     = lcm(E),  N = n*L
    x_0(E)= #{ k in {1,...,N-1} : (e_i k mod N) in [L,(n-1)L] for all i }
    E_div = { e in E : n | e },   E_non = E \ E_div      (Case 2: E_div nonempty)
    B_div = { b in Z : L/n <= b <= (n-1)L/n }
    t_e(b)= floor(e b / L)
    Sol(e,j,n)  = { r in Z/nZ : e r = j mod n }
    bad(e,t,n)  = Sol(e,-t,n) u Sol(e,-(t+1),n)

Two readings of "safe", because the manuscript uses both:
    SAFE_non(b) : union over e in E_non   of bad(e,t_e(b),n) != Z/nZ   (sections 2, 2.4)
    SAFE_all(b) : union over e in E (all) of bad(e,t_e(b),n) != Z/nZ   (section 5.1 literal,
                                                                       section 11.3a' practice)

Candidate map, the only one consistent with the manuscript's own coordinates
(k in {1,..,N-1}, b in [0,L), r in Z/nZ):

    k(b,r) := b + r*L .

The manuscript never writes this map down; it is reconstructed here (see report).
Everything below is exact integer arithmetic; no floating point in any decision.
"""

import sys, random
from math import gcd, lcm
from itertools import combinations
import numpy as np

N_RUNNERS = 8              # n
NUM_SPEEDS = N_RUNNERS - 1 # 7 distinct speeds


# ---------------------------------------------------------------- primitives

def bad_set(e, t, n):
    """bad(e,t,n) = Sol(e,-t,n) u Sol(e,-(t+1),n) as a frozenset of residues."""
    out = set()
    for j in (-t, -(t + 1)):
        jj = j % n
        for r in range(n):
            if (e * r) % n == jj:
                out.add(r)
    return out


def floors(E, L):
    """t_e(b) is computed per b; this returns a helper closure."""
    return lambda e, b: (e * b) // L


def true_x0(E, n):
    """x_0(E) by direct enumeration over k in {1,...,N-1}. Exact integer numpy."""
    L = lcm(*E)
    N = n * L
    k = np.arange(1, N, dtype=np.int64)
    ok = np.ones(N - 1, dtype=bool)
    for e in E:
        pos = (np.int64(e) * k) % N
        ok &= (pos >= L) & (pos <= (n - 1) * L)
        if not ok.any():
            return 0, L, N, np.zeros(0, dtype=np.int64)
    return int(ok.sum()), L, N, k[ok]


def is_safe_k(E, k, L, n):
    """Membership test for a single k, exact."""
    N = n * L
    return all(L <= (e * k) % N <= (n - 1) * L for e in E)


def analyse(E, n=N_RUNNERS, collect_k=True):
    """Full per-tuple analysis. Returns a dict of findings."""
    L = lcm(*E)
    N = n * L
    Ediv = [e for e in E if e % n == 0]
    Enon = [e for e in E if e % n != 0]
    assert Ediv, "Case 2 requires E_div nonempty"

    x0, L2, N2, safe_ks = true_x0(E, n)
    assert L2 == L and N2 == N

    blo, bhi = -(-L // n), (n - 1) * L // n   # ceil(L/n) .. floor((n-1)L/n); n | L so exact
    full = set(range(n))

    safe_non_fibres = []   # (b, uncovered residues under E_non-only)
    safe_all_fibres = []   # (b, uncovered residues under all of E)
    for b in range(blo, bhi + 1):
        un_non = set()
        for e in Enon:
            un_non |= bad_set(e, (e * b) // L, n)
        un_all = set(un_non)
        for e in Ediv:
            un_all |= bad_set(e, (e * b) // L, n)
        if un_non != full:
            safe_non_fibres.append((b, sorted(full - un_non)))
        if un_all != full:
            safe_all_fibres.append((b, sorted(full - un_all)))

    # --- test the map k(b,r) = b + r*L on every (safe fibre, uncovered residue) pair
    fail_non = []   # (b, r, k) where E_non-safe fibre produced a NON-safe k
    ok_non = 0
    for b, rs in safe_non_fibres:
        for r in rs:
            k = b + r * L
            if not (1 <= k <= N - 1):
                fail_non.append((b, r, k, "k out of range"))
            elif not is_safe_k(E, k, L, n):
                fail_non.append((b, r, k, "k not a safe point"))
            else:
                ok_non += 1

    fail_all = []
    ok_all = 0
    for b, rs in safe_all_fibres:
        for r in rs:
            k = b + r * L
            if not (1 <= k <= N - 1):
                fail_all.append((b, r, k, "k out of range"))
            elif not is_safe_k(E, k, L, n):
                fail_all.append((b, r, k, "k not a safe point"))
            else:
                ok_all += 1

    # --- reverse: does every true safe point k come from a fibre b in B_div?
    k_outside_Bdiv = 0
    if collect_k:
        for k in safe_ks.tolist():
            b = k % L
            if not (blo <= b <= bhi):
                k_outside_Bdiv += 1

    return dict(
        E=tuple(E), L=L, N=N, Ediv=tuple(Ediv), x0=x0,
        n_safe_non=len(safe_non_fibres), n_safe_all=len(safe_all_fibres),
        pairs_non_ok=ok_non, pairs_non_fail=len(fail_non), fail_non=fail_non[:5],
        pairs_all_ok=ok_all, pairs_all_fail=len(fail_all), fail_all=fail_all[:5],
        n_true_safe_k=int(x0), k_outside_Bdiv=k_outside_Bdiv,
    )


# ---------------------------------------------------------------- generation

def divisor_family(Lmax, per_L, rng, require_no_plain_n=False):
    """Tuples of 7 distinct divisors of L with lcm exactly L, gcd 1, some multiple of 8."""
    out = []
    for L in range(N_RUNNERS, Lmax + 1, N_RUNNERS):
        divs = [d for d in range(1, L + 1) if L % d == 0]
        if len(divs) < NUM_SPEEDS:
            continue
        combos = list(combinations(divs, NUM_SPEEDS))
        rng.shuffle(combos)
        picked = 0
        for c in combos:
            if picked >= per_L:
                break
            if not any(x % N_RUNNERS == 0 for x in c):
                continue
            if require_no_plain_n and N_RUNNERS in c:
                continue
            g = 0
            for x in c:
                g = gcd(g, x)
            if g != 1:
                continue
            l = 1
            for x in c:
                l = lcm(l, x)
            if l != L:
                continue
            out.append(tuple(sorted(c)))
            picked += 1
    return out


def random_family(count, Lmax, rng, smax=90, require_no_plain_n=False):
    """Random 7-subsets of [1,smax] with gcd 1, some multiple of 8, lcm <= Lmax."""
    out, tries = [], 0
    pool = list(range(1, smax + 1))
    while len(out) < count and tries < count * 4000:
        tries += 1
        c = tuple(sorted(rng.sample(pool, NUM_SPEEDS)))
        if not any(x % N_RUNNERS == 0 for x in c):
            continue
        if require_no_plain_n and N_RUNNERS in c:
            continue
        g = 0
        for x in c:
            g = gcd(g, x)
        if g != 1:
            continue
        l = 1
        for x in c:
            l = lcm(l, x)
        if l > Lmax:
            continue
        out.append(c)
    return sorted(set(out))


# ---------------------------------------------------------------- main

def main():
    rng = random.Random(20260907)
    Lmax = int(sys.argv[1]) if len(sys.argv) > 1 else 2000

    fams = {
        "divisor-family (any E_div)": divisor_family(Lmax, 6, rng),
        "divisor-family (8 NOT in E)": divisor_family(Lmax, 6, rng, require_no_plain_n=True),
        "random small speeds (any E_div)": random_family(400, Lmax, rng),
        "random small speeds (8 NOT in E)": random_family(400, Lmax, rng, require_no_plain_n=True),
    }

    grand = []
    for name, tuples in fams.items():
        tuples = sorted(set(tuples))
        print(f"\n=== {name}: {len(tuples)} tuples, L <= {Lmax} ===")
        rows = [analyse(E) for E in tuples]
        grand.extend(rows)

        n_x0_zero = sum(1 for r in rows if r["x0"] == 0)
        n_no_safe_non = sum(1 for r in rows if r["n_safe_non"] == 0)
        n_no_safe_all = sum(1 for r in rows if r["n_safe_all"] == 0)
        n_map_fail_non = sum(1 for r in rows if r["pairs_non_fail"] > 0)
        n_map_fail_all = sum(1 for r in rows if r["pairs_all_fail"] > 0)
        tot_pairs_non = sum(r["pairs_non_ok"] + r["pairs_non_fail"] for r in rows)
        tot_fail_non = sum(r["pairs_non_fail"] for r in rows)
        tot_pairs_all = sum(r["pairs_all_ok"] + r["pairs_all_fail"] for r in rows)
        tot_fail_all = sum(r["pairs_all_fail"] for r in rows)
        # tuples where EVERY E_non-safe fibre yields a bad k (bridge gives nothing)
        n_total_fail = sum(1 for r in rows
                           if r["n_safe_non"] > 0 and r["pairs_non_ok"] == 0)
        n_k_outside = sum(1 for r in rows if r["k_outside_Bdiv"] > 0)

        print(f"  x_0 = 0 tuples                              : {n_x0_zero}")
        print(f"  tuples with NO E_non-safe fibre             : {n_no_safe_non}")
        print(f"  tuples with NO all-E-safe fibre             : {n_no_safe_all}")
        print(f"  (b,r) pairs from E_non-safe fibres          : {tot_pairs_non}"
              f"   FAILING map: {tot_fail_non}")
        print(f"  (b,r) pairs from all-E-safe fibres          : {tot_pairs_all}"
              f"   FAILING map: {tot_fail_all}")
        print(f"  tuples with >=1 failing (b,r) [E_non defn]  : {n_map_fail_non}")
        print(f"  tuples with >=1 failing (b,r) [all-E defn]  : {n_map_fail_all}")
        print(f"  tuples where EVERY E_non-safe fibre fails   : {n_total_fail}")
        print(f"  tuples with true safe k whose b NOT in B_div: {n_k_outside}")

        worst = [r for r in rows if r["pairs_non_fail"] > 0]
        worst.sort(key=lambda r: -r["pairs_non_fail"])
        for r in worst[:3]:
            print(f"    example E={r['E']} L={r['L']} x0={r['x0']} "
                  f"E_div={r['Ediv']} failing pairs={r['pairs_non_fail']} "
                  f"of {r['pairs_non_fail']+r['pairs_non_ok']}; "
                  f"first={r['fail_non'][0]}")

    print("\n=== GRAND TOTALS over all families ===")
    print(f"  tuples analysed                             : {len(grand)}")
    print(f"  x_0 = 0                                     : {sum(1 for r in grand if r['x0']==0)}")
    print(f"  E_non-safe fibre exists but x_0 = 0         : "
          f"{sum(1 for r in grand if r['n_safe_non']>0 and r['x0']==0)}")
    print(f"  x_0 >= 1 but NO E_non-safe fibre            : "
          f"{sum(1 for r in grand if r['n_safe_non']==0 and r['x0']>=1)}")
    print(f"  x_0 >= 1 but NO all-E-safe fibre            : "
          f"{sum(1 for r in grand if r['n_safe_all']==0 and r['x0']>=1)}")
    tn = sum(r['pairs_non_ok']+r['pairs_non_fail'] for r in grand)
    fn = sum(r['pairs_non_fail'] for r in grand)
    ta = sum(r['pairs_all_ok']+r['pairs_all_fail'] for r in grand)
    fa = sum(r['pairs_all_fail'] for r in grand)
    print(f"  map k=b+rL on E_non-safe pairs              : {tn-fn}/{tn} valid, {fn} FAIL")
    print(f"  map k=b+rL on all-E-safe pairs              : {ta-fa}/{ta} valid, {fa} FAIL")
    print(f"  tuples where EVERY E_non-safe fibre fails   : "
          f"{sum(1 for r in grand if r['n_safe_non']>0 and r['pairs_non_ok']==0)}")
    tk = sum(r['n_true_safe_k'] for r in grand)
    ok_ = sum(r['k_outside_Bdiv'] for r in grand)
    print(f"  true safe points k, total                   : {tk}")
    print(f"  ... whose fibre b = k mod L is NOT in B_div : {ok_}"
          f"  ({100.0*ok_/max(tk,1):.1f}%  -- B_div restriction is lossy)")


if __name__ == "__main__":
    main()
