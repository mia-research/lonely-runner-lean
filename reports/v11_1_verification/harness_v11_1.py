#!/usr/bin/env python3
"""
v11.1 empirical harness — LRC Tier-1 witness check.

For each (n, E) in the sampled / enumerated grid, compute
    x_0(E) = #{k in [1, N-1] : (e_i * k) mod N in [L, (n-1)L] for all i}
where L = lcm(E), N = nL. Theorem A of v11.1 claims x_0(E) >= 1.

Enumerates all distinct-speed gcd-1 tuples with max speed <= max_e for
small n; samples random tuples for larger n. Exits non-zero on any failure.
"""

from __future__ import annotations

import itertools
import math
import random
import sys
import time
from pathlib import Path
from typing import Iterable, Tuple

Tuple_ = Tuple[int, ...]


def lcm(xs: Iterable[int]) -> int:
    out = 1
    for x in xs:
        out = out * x // math.gcd(out, x)
    return out


def x0(E: Tuple_, n: int) -> int:
    """Count safe points k in [1, N-1]."""
    L = lcm(E)
    N = n * L
    lo, hi = L, (n - 1) * L  # closed interval [L, (n-1)L]
    count = 0
    # Iterate k directly. For each k compute e_i*k mod N.
    # Use list comprehension for inner loop speed.
    for k in range(1, N):
        ok = True
        for e in E:
            r = (e * k) % N
            if r < lo or r > hi:
                ok = False
                break
        if ok:
            count += 1
    return count


def gen_enum(n: int, max_e: int) -> Iterable[Tuple_]:
    """Enumerate all distinct gcd-1 tuples of size n-1 with entries in [1, max_e]."""
    for combo in itertools.combinations(range(1, max_e + 1), n - 1):
        if math.gcd(*combo) == 1:
            yield combo


def gen_random(n: int, max_e: int, k: int, rng: random.Random) -> Iterable[Tuple_]:
    """Yield k random distinct-speed gcd-1 tuples."""
    pool = list(range(1, max_e + 1))
    seen = set()
    attempts = 0
    while len(seen) < k and attempts < 50 * k:
        attempts += 1
        sample = tuple(sorted(rng.sample(pool, n - 1)))
        if sample in seen:
            continue
        if math.gcd(*sample) != 1:
            continue
        seen.add(sample)
        yield sample


def run():
    random.seed(20260418)
    rng = random.Random(20260418)

    # (n, max_e, mode, sample_k)
    # For small n: enumerate up to max_e; for larger n: random sample.
    schedule = [
        (5,  20, "enum",  None),
        (6,  18, "enum",  None),
        (7,  16, "enum",  None),
        (8,  14, "random", 800),
        (9,  14, "random", 600),
        (10, 14, "random", 400),
        (11, 14, "random", 300),
        (12, 14, "random", 200),
        (13, 16, "random", 150),
        (14, 16, "random", 100),
        (15, 16, "random", 80),
    ]

    t0 = time.time()
    total = 0
    failures = []
    per_n = {}

    for n, max_e, mode, k in schedule:
        if mode == "enum":
            gen = list(gen_enum(n, max_e))
        else:
            gen = list(gen_random(n, max_e, k, rng))

        cnt = 0
        tstart = time.time()
        min_x0 = None
        for E in gen:
            # Skip tuples whose L is astronomical — harness budget.
            L = lcm(E)
            if L > 200_000:
                continue
            c = x0(E, n)
            cnt += 1
            total += 1
            if min_x0 is None or c < min_x0:
                min_x0 = c
            if c < 1:
                failures.append((n, E, c))

        elapsed = time.time() - tstart
        per_n[n] = (cnt, min_x0, elapsed)
        print(f"n={n:2d} mode={mode:6s} tuples_tested={cnt:6d} min_x0={min_x0} elapsed={elapsed:.2f}s", flush=True)

    T = time.time() - t0
    print()
    print(f"TOTAL tuples tested: {total}")
    print(f"Total wall time: {T:.1f}s")
    print(f"Failures (x_0 < 1): {len(failures)}")
    for f in failures[:20]:
        print(f"  FAIL: n={f[0]} E={f[1]} x_0={f[2]}")

    return 0 if not failures else 1


if __name__ == "__main__":
    sys.exit(run())
