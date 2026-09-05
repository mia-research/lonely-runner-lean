#!/usr/bin/env python3
"""Independent reproduction of the Barajas-Serra 2008 section 7 computer search
(the |A| = 5, m = 1 case), both stages.

BS section 7 asserts, without publishing the search:
  stage 1 (N = 49):  at most (1/21)*C(21,5) = 969 non-equivalent 5-sets; all but
                     three admit a multiplier placing every element in [7,42];
                     the exceptions are {1,4,11,39,43}, {1,4,18,22,29},
                     {1,4,18,44,46}.
  stage 2 (N' = 98): each exception, combined with d6 = 7k, admits a multiplier
                     except for three sets, all of which have gcd >= 2 and so
                     cannot arise under the LRC normalization gcd(D) = 1.

Run:  python3 verify_section7_m1.py
Both stages reproduce exactly.  Two conventions matter and are easy to get wrong;
both are recorded here because getting either wrong changes the answer:

  * The stage-1 universe is NOT all 42 units mod 49.  It is the 21 residues whose
    class mod 7 lies in {1,2,4} -- the `hres` hypothesis of the Lean statement.
    That is where BS's "21" comes from.  Over all 42 units the count is 20254
    orbits with 48 exceptions, which does not match BS.
  * In stage 2 the multiplier must range over ALL of 1..97, not just the units
    mod 98.  Restricting to units produces a spurious fourth exception,
    (4,44,46,50,67) with d6 = 21, which has gcd 1 and so would not be disposed of
    by BS's gcd argument.  It is not a counterexample: the multipliers 7, 21, 77,
    91 all work for it, and as a real instance those speeds reach min distance
    0.283 >> 1/7.
"""
from itertools import combinations, product
from functools import reduce
from math import gcd

def stage1():
    N = 49
    S21 = [x for x in range(1, N) if x % 7 in (1, 2, 4)]
    LAM = [u for u in range(1, N) if u % 7 in (1, 2, 4)]
    assert len(S21) == 21 and len(LAM) == 21
    good = lambda T: any(all(7 <= (l * t) % N <= 42 for t in T) for l in LAM)
    seen, bad = set(), []
    for T in combinations(S21, 5):
        key = min(tuple(sorted((l * t) % N for t in T)) for l in LAM)
        if key in seen:
            continue
        seen.add(key)
        if not good(T):
            bad.append(key)
    return len(seen), sorted(bad)

def stage2(exceptions):
    N = 98
    ALL = list(range(1, N))
    d6vals = [7 * k for k in range(1, 14) if (7 * k) % 49 != 0 and 7 * k < N]
    good = lambda D: any(all(14 <= (l * x) % N <= 84 for x in D) for l in ALL)
    fails = {}
    for E in exceptions:
        for lifts in product(*[(x, x + 49) for x in E]):
            L = tuple(sorted(l % N for l in lifts))
            for d6 in d6vals:
                if not good(L + (d6,)):
                    fails.setdefault(L, []).append(d6)
    return fails

if __name__ == "__main__":
    n_orbits, bad = stage1()
    print(f"stage 1 (N=49): {n_orbits} orbits, {len(bad)} exceptions")
    for b in bad:
        print("   ", b)
    assert n_orbits == 969, n_orbits
    assert bad == [(1, 4, 11, 39, 43), (1, 4, 18, 22, 29), (1, 4, 18, 44, 46)], bad
    print("   matches BS section 7 exactly")

    fails = stage2(bad)
    print(f"\nstage 2 (N'=98): {len(fails)} failing 5-set lifts")
    for L, ds in sorted(fails.items()):
        print(f"    {L}  d6 in {ds}  gcd(6-set) = {reduce(gcd, L + tuple(ds))}")
    assert len(fails) == 3, len(fails)
    assert all(reduce(gcd, L + tuple(ds)) >= 2 for L, ds in fails.items())
    print("   every failing configuration has gcd >= 2; gcd(D) = 1 disposes of all")
    print("\nBOTH STAGES REPRODUCE. BS section 7 verified.")
