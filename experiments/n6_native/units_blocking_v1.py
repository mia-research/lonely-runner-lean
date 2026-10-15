#!/usr/bin/env python3
"""E45: the hunch, checked. At a divisible flank e = nE the coarse shifts are u in Z/n (openings uE, row 0); a slower
runner with residue r = d mod n blocks u iff r u mod n in {0, n-1} (the n-ary form of SixCells.Blocks; phase 0 at
row 0). Claims to check by direct enumeration, n = 3..8:
 (1) a unit r blocks exactly {0, -r^{-1}}; a non-unit r (g = gcd(r,n) > 1) blocks exactly the multiples of n/g;
 (2) so the unit (event) shifts are blocked only by unit runners, one each, and non-unit shifts only by non-units;
 (3) all n shifts blocked by a residue set R (|R| <= n-2 slower runners) iff R contains every unit and the non-unit
     residues in R cover the non-unit nonzero shifts. Lists the minimal blocking residue sets per order, and
     reproduces SixCells.all_shifts_blocked_iff at n = 6 (1,3,5 in R and (2 or 4) in R).
"""
from math import gcd
from itertools import combinations
for n in range(3, 9):
    units = {r for r in range(1, n) if gcd(r, n) == 1}
    B = {r: frozenset(u for u in range(n) if (r * u) % n in (0, n - 1)) for r in range(1, n)}
    ok1 = all(B[r] == frozenset({0, (-pow(r, -1, n)) % n}) for r in units) and \
          all(B[r] == frozenset(range(0, n, n // gcd(r, n))) for r in range(1, n) if r not in units)
    event_shifts = units; nonunit_shifts = set(range(1, n)) - units
    ok2 = all((B[r] - {0}) <= event_shifts for r in units) and all((B[r] - {0}) <= nonunit_shifts for r in range(1, n) if r not in units)
    blocking = [set(R) for k in range(1, n - 1) for R in combinations(range(1, n), k) if frozenset().union(*[B[r] for r in R]) == frozenset(range(n))]
    rule = lambda R: units <= R and nonunit_shifts <= set().union(*[B[r] for r in R if r not in units], set())
    ok3 = all(rule(R) for R in blocking) and all((frozenset().union(*[B[r] for r in R]) == frozenset(range(n))) for k in range(1, n - 1) for R in map(set, combinations(range(1, n), k)) if rule(R))
    minimal = [R for R in blocking if not any(S < R for S in blocking)]
    need = len(units) + (min((len(R - units) for R in blocking), default=None) if blocking else None) if blocking else None
    print(f"n = {n}: units (events) {sorted(units)}, non-unit shifts {sorted(nonunit_shifts)}; runners slower than the flank: up to {n-2}")
    print(f"   shapes (1) {ok1}; separation (2) {ok2}; blocking rule (3) {ok3}")
    print(f"   blocking residue sets with <= {n-2} runners: {len(blocking)}; minimal: {[sorted(R) for R in minimal]}")
    if n == 6:
        print("   SixCells.all_shifts_blocked_iff (1,3,5 in R and 2 or 4 in R) reproduced:",
              all((({1,3,5} <= R) and (2 in R or 4 in R)) == (frozenset().union(*[B[r] for r in R]) == frozenset(range(6))) for k in range(1, 6) for R in map(set, combinations(range(1, 6), k))))
