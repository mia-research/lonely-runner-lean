#!/usr/bin/env python3
"""
Exact 863-family period-7 cycle automaton in base 10.

The unique period-7 count-space attractor at d=8 extends by the uniform shell
move +2_36 to all even dimensions d = 8 + 2m.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path


TMP_JSON = Path("/tmp/kaprekar_863_cycle_automaton_2026-04-24.json")


BASE_STATES: list[list[int]] = [
    [1, 0, 1, 1, 1, 1, 1, 0, 2, 0],
    [1, 0, 1, 2, 0, 0, 2, 0, 2, 0],
    [0, 0, 2, 2, 0, 0, 3, 0, 1, 0],
    [0, 0, 1, 1, 2, 1, 3, 0, 0, 0],
    [1, 0, 1, 1, 1, 0, 2, 1, 1, 0],
    [0, 1, 1, 1, 1, 1, 1, 1, 1, 0],
    [1, 0, 0, 2, 1, 1, 1, 1, 1, 0],
]


def state(i: int, m: int) -> list[int]:
    out = BASE_STATES[i].copy()
    out[3] += m
    out[6] += m
    return out


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


def verify_grid(m_max: int) -> dict[str, object]:
    checked = 0
    failures = 0
    samples: list[dict[str, object]] = []

    for m in range(0, m_max + 1):
        states = [state(i, m) for i in range(7)]
        d = sum(states[0])
        ok = True
        for i, s in enumerate(states):
            n = number_from_counts(s)
            nxt = counts_of_number(n, d)
            if nxt != states[(i + 1) % 7]:
                ok = False
                failures += 1
                break
        checked += 1
        if len(samples) < 8 and ok:
            samples.append(
                {
                    "m": m,
                    "d": d,
                    "numbers": [number_from_counts(s) for s in states],
                    "gap_profiles": [shell_gap_profile(s) for s in states],
                }
            )

    return {
        "checked": checked,
        "failures": failures,
        "samples": samples,
        "known_slices": {
            "d8": {"m": 0, "numbers": [number_from_counts(state(i, 0)) for i in range(7)]},
            "d10": {"m": 1, "numbers": [number_from_counts(state(i, 1)) for i in range(7)]},
            "d12": {"m": 2, "numbers": [number_from_counts(state(i, 2)) for i in range(7)]},
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Verify the exact 863-family period-7 automaton.")
    parser.add_argument("--m-max", type=int, default=20)
    parser.add_argument("--json-out", type=Path, default=TMP_JSON)
    args = parser.parse_args()

    payload = verify_grid(args.m_max)
    args.json_out.write_text(json.dumps(payload, indent=2))

    print(f"JSON: {args.json_out}")
    print("checked={checked} failures={failures}".format(**payload))


if __name__ == "__main__":
    main()
