#!/usr/bin/env python3
"""The m = 1 exceptions resolve at N = 7^3 = 343, inside the 7-adic framework.

Barajas-Serra section 7 resolves the three exceptional 5-sets by passing to
N' = 2*49 = 98 and appealing to gcd(D) >= 2. That route is unusable for this
formalization for three independent reasons (docs/n7_bs/SECTION7_M1_ANALYSIS_v1.md
section 2): 98 is not a power of 7 so it is outside the qz/nu apparatus; 20 of the
1134 gcd = 1 configurations there admit ONLY multipliers divisible by 7, so no
statement of the form "exists lam, not 7 | lam and ..." is true for them; and d6
cannot help at N = 49 at all.

This script checks a different route that avoids all three problems: stay with
powers of 7 and go one level UP, to N = 343.

For every lift mod 343 of every exceptional 5-set, combined with every valid
d6 (7 | d6, 49 does not divide d6), there is a multiplier COPRIME TO 7 placing
all six elements in the central band. 2,117,682 configurations, zero failures,
under both the strict `qz 2 not in {0,6}` band [49,293] and the circDist >= 1/7
band [49,294].

The lifts matter and are the whole point: a genuine D is pinned only mod 49, so
checking the three published representatives is not enough. Each of the five
elements has 7 lifts mod 343, giving 3 * 7^5 * 42 configurations.

Run: python3 verify_m1_at_343.py     (~1 min with numpy)
"""
import itertools
import numpy as np

N = 343
EXC = [(1, 4, 11, 39, 43), (1, 4, 18, 22, 29), (1, 4, 18, 44, 46)]
LAMS = np.array([l for l in range(1, N) if l % 7 != 0], dtype=np.int64)
D6S = [7 * k for k in range(1, 49) if k % 7 != 0]


def sweep(lo, hi):
    total = fails = 0
    examples = []
    for E in EXC:
        for lift in itertools.product(range(7), repeat=5):
            D5 = np.array([E[i] + 49 * lift[i] for i in range(5)], dtype=np.int64)
            P5 = (LAMS[:, None] * D5[None, :]) % N
            ok5 = ((P5 >= lo) & (P5 <= hi)).all(axis=1)
            if not ok5.any():
                fails += len(D6S)
                total += len(D6S)
                examples.append((tuple(int(x) for x in D5), "no lam for the 5-set"))
                continue
            cand = LAMS[ok5]
            for d6 in D6S:
                v = (cand * d6) % N
                if not ((v >= lo) & (v <= hi)).any():
                    fails += 1
                    examples.append((tuple(int(x) for x in D5), d6))
                total += 1
    return total, fails, examples


if __name__ == "__main__":
    for lo, hi, label in [(49, 293, "strict  qz 2 not in {0,6}  [49,293]"),
                          (49, 294, "band    circDist >= 1/7    [49,294]")]:
        total, fails, ex = sweep(lo, hi)
        print(f"{label}:  checked={total}  failures={fails}")
        for e in ex[:5]:
            print("     ", e)
        assert fails == 0, ex[:5]
    print("\nAll m=1 exceptional configurations resolve at N = 343 with a")
    print("multiplier coprime to 7. No need for N' = 98.")
