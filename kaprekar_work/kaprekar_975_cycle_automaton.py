#!/usr/bin/env python3
"""
Exact 975-family cycle automaton in base 10.

The family is parameterized by integers a,b,c >= 1 and m >= 0 via the three
phase count vectors

  X0 = [1, a, c, m, b, b, m, c, a, 1]
  X1 = [1, b, a, m, c, c, m, a, b, 1]
  X2 = [1, c, b, m, a, a, m, b, c, 1]

and satisfies

  K(X0) = X1,   K(X1) = X2,   K(X2) = X0.

When a=b=c, the three phases coincide and the orbit collapses to a fixed point.
Otherwise the orbit has exact period 3.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path


ROOT = Path("/Users/trentpalelei/Desktop/Kaprekar")
TMP_JSON = Path("/tmp/kaprekar_975_cycle_automaton_2026-04-24.json")


def state0(a: int, b: int, c: int, m: int) -> list[int]:
    return [1, a, c, m, b, b, m, c, a, 1]


def state1(a: int, b: int, c: int, m: int) -> list[int]:
    return [1, b, a, m, c, c, m, a, b, 1]


def state2(a: int, b: int, c: int, m: int) -> list[int]:
    return [1, c, b, m, a, a, m, b, c, 1]


def number_from_counts(cnt: list[int]) -> int:
    desc = "".join(str(d) * cnt[d] for d in range(9, -1, -1))
    asc = "".join(str(d) * cnt[d] for d in range(10))
    return int(desc) - int(asc)


def counts_of_number(n: int, d: int) -> list[int]:
    c = Counter(map(int, str(n).zfill(d)))
    return [c[i] for i in range(10)]


def shell_gap_profile(cnt: list[int]) -> list[int]:
    desc: list[int] = []
    for d in range(9, -1, -1):
        desc.extend([d] * cnt[d])
    asc = list(reversed(desc))
    g = [a - b for a, b in zip(desc, asc)]
    return g[: (len(desc) + 1) // 2]


def verify_grid(a_max: int, b_max: int, c_max: int, m_max: int) -> dict[str, object]:
    checked = 0
    failures = 0
    samples: list[dict[str, object]] = []
    fixed_count = 0
    cycle_count = 0

    for a in range(1, a_max + 1):
        for b in range(1, b_max + 1):
            for c in range(1, c_max + 1):
                for m in range(0, m_max + 1):
                    x0 = state0(a, b, c, m)
                    x1 = state1(a, b, c, m)
                    x2 = state2(a, b, c, m)
                    d = sum(x0)
                    n0 = number_from_counts(x0)
                    n1 = number_from_counts(x1)
                    n2 = number_from_counts(x2)
                    ok = (
                        counts_of_number(n0, d) == x1
                        and counts_of_number(n1, d) == x2
                        and counts_of_number(n2, d) == x0
                    )
                    checked += 1
                    if not ok:
                        failures += 1
                    if a == b == c:
                        fixed_count += 1
                    else:
                        cycle_count += 1
                    if len(samples) < 10 and ok:
                        samples.append(
                            {
                                "params": [a, b, c, m],
                                "d": d,
                                "numbers": [n0, n1, n2],
                                "gap_profiles": [
                                    shell_gap_profile(x0),
                                    shell_gap_profile(x1),
                                    shell_gap_profile(x2),
                                ],
                                "period": 1 if a == b == c else 3,
                            }
                        )
    return {
        "checked": checked,
        "failures": failures,
        "fixed_ridge_points": fixed_count,
        "period3_points": cycle_count,
        "samples": samples,
        "known_slices": {
            "d8_fixed": {"params": [1, 1, 1, 0], "numbers": [number_from_counts(state0(1, 1, 1, 0))]},
            "d10_fixed": {"params": [1, 1, 1, 1], "numbers": [number_from_counts(state0(1, 1, 1, 1))]},
            "d12_cycle": {"params": [1, 1, 2, 1], "numbers": [number_from_counts(state0(1, 1, 2, 1)), number_from_counts(state1(1, 1, 2, 1)), number_from_counts(state2(1, 1, 2, 1))]},
            "d16_cycle": {"params": [1, 2, 3, 1], "numbers": [number_from_counts(state0(1, 2, 3, 1)), number_from_counts(state1(1, 2, 3, 1)), number_from_counts(state2(1, 2, 3, 1))]},
            "d22_cycle": {"params": [2, 3, 3, 2], "numbers": [number_from_counts(state0(2, 3, 3, 2)), number_from_counts(state1(2, 3, 3, 2)), number_from_counts(state2(2, 3, 3, 2))]},
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Verify the exact 975-family cycle automaton.")
    parser.add_argument("--a-max", type=int, default=6)
    parser.add_argument("--b-max", type=int, default=6)
    parser.add_argument("--c-max", type=int, default=6)
    parser.add_argument("--m-max", type=int, default=6)
    parser.add_argument("--json-out", type=Path, default=TMP_JSON)
    args = parser.parse_args()

    payload = verify_grid(args.a_max, args.b_max, args.c_max, args.m_max)
    args.json_out.write_text(json.dumps(payload, indent=2))

    print(f"JSON: {args.json_out}")
    print(
        "checked={checked} failures={failures} fixed_ridge_points={fixed_ridge_points} period3_points={period3_points}".format(
            **payload
        )
    )


if __name__ == "__main__":
    main()
