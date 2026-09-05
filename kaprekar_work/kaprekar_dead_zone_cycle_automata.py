#!/usr/bin/env python3
"""
Dead-zone cycle automata for base-10 dimensions d=5 and d=7.

Build the exact parameter-state transition graph from the symmetric-difference
maps already used in the dead-zone proof, then compute:

- attractor cycles
- basin sizes
- transient-depth histograms

This reframes d=5 and d=7 as pure-cycle borrow automata rather than just
"dimensions with no fixed points".
"""

from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict, deque
from pathlib import Path


ROOT = Path("/Users/trentpalelei/Desktop/Kaprekar")
TMP_JSON = Path("/tmp/kaprekar_dead_zone_cycle_automata_2026-04-24.json")


def digits_d5(A: int, B: int) -> list[int]:
    if B == 0:
        return [A - 1, 9, 9, 9, 10 - A]
    return [A, B - 1, 9, 9 - B, 10 - A]


def next_state_d5(state: tuple[int, int]) -> tuple[int, int]:
    A, B = state
    s = sorted(digits_d5(A, B), reverse=True)
    return (s[0] - s[4], s[1] - s[3])


def digits_d7(A: int, B: int, C: int) -> list[int]:
    if C == 0:
        if B == 0:
            return [A - 1, 9, 9, 9, 9, 9, 10 - A]
        return [A, B - 1, 9, 9, 9, 9 - B, 10 - A]
    return [A, B, C - 1, 9, 9 - C, 9 - B, 10 - A]


def next_state_d7(state: tuple[int, int, int]) -> tuple[int, int, int]:
    A, B, C = state
    s = sorted(digits_d7(A, B, C), reverse=True)
    return (s[0] - s[6], s[1] - s[5], s[2] - s[4])


def representative_number_d5(state: tuple[int, int]) -> int:
    return int("".join(str(d) for d in sorted(digits_d5(*state), reverse=True)))


def representative_number_d7(state: tuple[int, int, int]) -> int:
    return int("".join(str(d) for d in sorted(digits_d7(*state), reverse=True)))


def analyze(states: list[tuple[int, ...]], succ_fn, rep_fn) -> list[dict[str, object]]:
    succ = {s: succ_fn(s) for s in states}
    pred: dict[tuple[int, ...], list[tuple[int, ...]]] = defaultdict(list)
    for s, t in succ.items():
        pred[t].append(s)

    seen: set[tuple[int, ...]] = set()
    cycles: list[list[tuple[int, ...]]] = []

    for s in states:
        if s in seen:
            continue
        path: list[tuple[int, ...]] = []
        idx: dict[tuple[int, ...], int] = {}
        cur = s
        while cur not in idx and cur not in seen:
            idx[cur] = len(path)
            path.append(cur)
            cur = succ[cur]
        if cur in idx:
            cycles.append(path[idx[cur] :])
        seen.update(path)

    out: list[dict[str, object]] = []
    for cyc in cycles:
        basin: set[tuple[int, ...]] = set(cyc)
        depth: dict[tuple[int, ...], int] = {x: 0 for x in cyc}
        q: deque[tuple[int, ...]] = deque(cyc)
        while q:
            u = q.popleft()
            for p in pred[u]:
                if p not in basin:
                    basin.add(p)
                    depth[p] = depth[u] + 1
                    q.append(p)
        out.append(
            {
                "cycle_states": [list(x) for x in cyc],
                "cycle_length": len(cyc),
                "cycle_representatives": [rep_fn(x) for x in cyc],
                "basin_size": len(basin),
                "max_transient_depth": max(depth.values()),
                "depth_histogram": {str(k): v for k, v in sorted(Counter(depth.values()).items())},
            }
        )

    out.sort(key=lambda row: (row["cycle_length"], row["basin_size"]))
    return out


def main() -> None:
    parser = argparse.ArgumentParser(description="Analyze d=5 and d=7 dead-zone cycle automata.")
    parser.add_argument("--json-out", type=Path, default=TMP_JSON)
    args = parser.parse_args()

    states5 = [(A, B) for A in range(1, 10) for B in range(0, A + 1)]
    states7 = [(A, B, C) for A in range(1, 10) for B in range(0, A + 1) for C in range(0, B + 1)]

    payload = {
        "d5": {
            "state_count": len(states5),
            "attractors": analyze(states5, next_state_d5, representative_number_d5),
        },
        "d7": {
            "state_count": len(states7),
            "attractors": analyze(states7, next_state_d7, representative_number_d7),
        },
    }

    args.json_out.write_text(json.dumps(payload, indent=2))
    print(f"JSON: {args.json_out}")
    for d in ("d5", "d7"):
        attractors = payload[d]["attractors"]
        lengths = [row["cycle_length"] for row in attractors]
        basins = [row["basin_size"] for row in attractors]
        print(f"{d}: state_count={payload[d]['state_count']} cycle_lengths={lengths} basin_sizes={basins}")


if __name__ == "__main__":
    main()
