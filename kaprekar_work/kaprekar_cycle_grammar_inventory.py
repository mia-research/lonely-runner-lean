#!/usr/bin/env python3
"""
Inventory of known base-10 cycle families under the shared +2_36 shell axis.

This runner verifies:
  - 863-family period-7 chain
  - odd families A..H
  - unstable T-family reducing to B

The 975 family is handled in its own dedicated theorem note because it also
has transverse rotating shell generators beyond the shared +2_36 axis.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path


TMP_JSON = Path("/tmp/kaprekar_cycle_grammar_inventory_2026-04-24.json")


def number_from_counts(cnt: list[int]) -> int:
    desc = "".join(str(d) * cnt[d] for d in range(9, -1, -1))
    asc = "".join(str(d) * cnt[d] for d in range(10))
    return int(desc) - int(asc)


def counts_of_number(n: int, d: int) -> list[int]:
    c = Counter(map(int, str(n).zfill(d)))
    return [c[i] for i in range(10)]


def Y_states(m: int) -> list[list[int]]:
    return [
        [1, 0, 1, m + 1, 1, 1, m + 1, 0, 2, 0],
        [1, 0, 1, m + 2, 0, 0, m + 2, 0, 2, 0],
        [0, 0, 2, m + 2, 0, 0, m + 3, 0, 1, 0],
        [0, 0, 1, m + 1, 2, 1, m + 3, 0, 0, 0],
        [1, 0, 1, m + 1, 1, 0, m + 2, 1, 1, 0],
        [0, 1, 1, m + 1, 1, 1, m + 1, 1, 1, 0],
        [1, 0, 0, m + 2, 1, 1, m + 1, 1, 1, 0],
    ]


def A_states(m: int) -> list[list[int]]:
    return [
        [0, 2, 0, m + 2, 1, 1, m + 2, 1, 0, 2],
        [0, 2, 1, m + 1, 1, 1, m + 1, 1, 2, 1],
        [0, 1, 2, m + 1, 1, 1, m + 1, 2, 1, 1],
        [0, 1, 1, m + 1, 2, 2, m + 1, 1, 1, 1],
        [1, 0, 2, m + 1, 1, 1, m + 1, 1, 2, 1],
    ]


def B_states(m: int) -> list[list[int]]:
    return [
        [0, 1, 1, m + 2, 2, 2, m + 3, 0, 0, 2],
        [1, 0, 3, m + 2, 0, 0, m + 2, 2, 2, 1],
    ]


def C_states(m: int) -> list[list[int]]:
    return [
        [0, 1, 2, m + 1, 2, 2, m + 1, 2, 1, 1],
        [1, 0, 2, m + 1, 2, 2, m + 1, 1, 2, 1],
        [1, 1, 1, m + 2, 1, 1, m + 2, 1, 1, 2],
        [0, 3, 0, m + 2, 1, 1, m + 2, 1, 1, 2],
        [0, 2, 2, m + 1, 1, 1, m + 1, 2, 2, 1],
    ]


def D_states(m: int) -> list[list[int]]:
    return [
        [0, 2, 1, m + 1, 2, 2, m + 1, 1, 2, 1],
        [1, 0, 3, m + 1, 1, 1, m + 1, 2, 2, 1],
        [0, 2, 0, m + 2, 2, 2, m + 2, 1, 0, 2],
        [1, 1, 2, m + 1, 1, 1, m + 1, 1, 3, 1],
        [0, 2, 1, m + 2, 1, 1, m + 2, 2, 0, 2],
    ]


def E_states(m: int) -> list[list[int]]:
    return [
        [1, 1, 3, m + 1, 1, 1, m + 1, 2, 3, 1],
        [0, 2, 1, m + 2, 2, 2, m + 2, 2, 0, 2],
        [1, 1, 2, m + 1, 2, 2, m + 1, 1, 3, 1],
        [1, 1, 2, m + 2, 1, 1, m + 2, 2, 1, 2],
        [0, 3, 0, m + 2, 2, 2, m + 2, 1, 1, 2],
    ]


def F_states(m: int) -> list[list[int]]:
    return [
        [1, 2, 1, m + 2, 1, 1, m + 2, 1, 2, 2],
        [0, 3, 1, m + 2, 1, 1, m + 2, 2, 1, 2],
        [0, 2, 2, m + 1, 2, 2, m + 1, 2, 2, 1],
        [1, 0, 3, m + 1, 2, 2, m + 1, 2, 2, 1],
        [1, 1, 1, m + 2, 2, 2, m + 2, 1, 1, 2],
    ]


def G_states(m: int) -> list[list[int]]:
    return [
        [1, 2, 2, m + 2, 1, 1, m + 2, 2, 2, 2],
        [0, 3, 1, m + 2, 2, 2, m + 2, 2, 1, 2],
        [1, 1, 3, m + 1, 2, 2, m + 1, 2, 3, 1],
        [1, 1, 2, m + 2, 2, 2, m + 2, 2, 1, 2],
        [1, 2, 1, m + 2, 2, 2, m + 2, 1, 2, 2],
    ]


def H_states(m: int) -> list[list[int]]:
    return [
        [1, 2, 2, m + 1, 3, 3, m + 1, 2, 2, 2],
        [1, 3, 2, m + 1, 2, 2, m + 1, 2, 3, 2],
        [1, 2, 3, m + 1, 2, 2, m + 1, 3, 2, 2],
    ]


BASE_T8: list[list[int]] = [
    [0, 1, 1, 2, 1, 1, 3, 0, 0, 2],
    [0, 1, 2, 2, 0, 0, 2, 2, 1, 1],
    [0, 0, 2, 1, 2, 2, 2, 0, 1, 1],
    [1, 0, 1, 3, 0, 0, 2, 2, 1, 1],
    [0, 1, 1, 1, 2, 2, 2, 0, 0, 2],
    [1, 0, 3, 1, 0, 0, 1, 2, 2, 1],
    [0, 1, 0, 3, 1, 2, 2, 0, 0, 2],
    [1, 0, 1, 3, 0, 0, 3, 0, 2, 1],
]


def T_states(m: int) -> list[list[int]]:
    out = []
    for s in BASE_T8:
        t = s.copy()
        t[3] += m
        t[6] += m
        out.append(t)
    return out


def verify_cycle_family(fn, m_max: int) -> dict[str, object]:
    checked = 0
    failures = 0
    for m in range(0, m_max + 1):
        states = fn(m)
        d = sum(states[0])
        for i, s in enumerate(states):
            n = number_from_counts(s)
            nxt = counts_of_number(n, d)
            if nxt != states[(i + 1) % len(states)]:
                failures += 1
                return {"checked": checked + 1, "failures": failures, "bad_m": m, "bad_phase": i}
        checked += 1
    return {"checked": checked, "failures": failures}


def verify_transient_to_B(m_max: int) -> dict[str, object]:
    checked = 0
    failures = 0
    hit_hist = Counter()
    for m in range(1, m_max + 1):
        targets = {tuple(s) for s in B_states(m - 1)}
        for phase, s0 in enumerate(T_states(m)):
            checked += 1
            cur = s0
            hit = None
            for t in range(1, 16):
                cur = counts_of_number(number_from_counts(cur), sum(cur))
                if tuple(cur) in targets:
                    hit = t
                    break
            if hit is None:
                failures += 1
                return {"checked": checked, "failures": failures, "bad_m": m, "bad_phase": phase}
            hit_hist[hit] += 1
    return {"checked": checked, "failures": failures, "hit_histogram": dict(sorted(hit_hist.items()))}


def main() -> None:
    parser = argparse.ArgumentParser(description="Verify current cycle-grammar inventory under the shared +2_36 axis.")
    parser.add_argument("--m-max", type=int, default=20)
    parser.add_argument("--json-out", type=Path, default=TMP_JSON)
    args = parser.parse_args()

    payload = {
        "Y_period7": verify_cycle_family(Y_states, args.m_max),
        "A_period5": verify_cycle_family(A_states, args.m_max),
        "B_period2": verify_cycle_family(B_states, args.m_max),
        "C_period5": verify_cycle_family(C_states, args.m_max),
        "D_period5": verify_cycle_family(D_states, args.m_max),
        "E_period5": verify_cycle_family(E_states, args.m_max),
        "F_period5": verify_cycle_family(F_states, args.m_max),
        "G_period5": verify_cycle_family(G_states, args.m_max),
        "H_period3": verify_cycle_family(H_states, args.m_max),
        "T_to_B_reduction": verify_transient_to_B(args.m_max),
    }

    args.json_out.write_text(json.dumps(payload, indent=2))
    print(f"JSON: {args.json_out}")
    for key, row in payload.items():
        if key == "T_to_B_reduction":
            print(f"{key}: checked={row['checked']} failures={row['failures']} hit_hist={row['hit_histogram']}")
        else:
            print(f"{key}: checked={row['checked']} failures={row['failures']}")


if __name__ == "__main__":
    main()
