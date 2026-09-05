#!/usr/bin/env python3
"""
Study the lone extra odd period-2 attractor at d=25.

Natural symmetric ansatz:
    Q(w,x,y) = [0,2,w,x,y,y,x,w,2,3]

This script verifies:
1. The only nontrivial period-2 solution in that family is Q(3,3,3).
2. The resulting knot is terminal under one-shell lifts: no ordered pair of
   single complementary-shell additions to its two phases yields another
   period-2 cycle at d=27.
"""

from __future__ import annotations

import json
from collections import Counter
from pathlib import Path


ROOT = Path("/Users/trentpalelei/Desktop/Math Ex/kaprekar_work")
OUT_JSON = ROOT / "kaprekar_period2_boundary_knot_2026-05-03.json"


def number_from_counts(cnt: list[int] | tuple[int, ...]) -> int:
    desc = "".join(str(d) * cnt[d] for d in range(9, -1, -1))
    asc = "".join(str(d) * cnt[d] for d in range(10))
    return int(desc) - int(asc)


def counts_of_number(n: int, d: int) -> list[int]:
    c = Counter(map(int, str(n).zfill(d)))
    return [c[i] for i in range(10)]


def step(cnt: list[int] | tuple[int, ...]) -> list[int]:
    return counts_of_number(number_from_counts(cnt), sum(cnt))


def add(u: list[int], v: tuple[int, ...]) -> list[int]:
    return [a + b for a, b in zip(u, v)]


def Q(w: int, x: int, y: int) -> list[int]:
    return [0, 2, w, x, y, y, x, w, 2, 3]


def main() -> None:
    solutions = []
    unique_cycles = set()
    for w in range(0, 10):
        for x in range(0, 10):
            for y in range(0, 10):
                q0 = Q(w, x, y)
                q1 = step(q0)
                if q1 != q0 and step(q1) == q0:
                    solutions.append({"w": w, "x": x, "y": y, "q0": q0, "q1": q1})
                    cyc = tuple(sorted((tuple(q0), tuple(q1))))
                    unique_cycles.add(cyc)

    knot0 = [0, 2, 3, 3, 3, 3, 3, 3, 2, 3]
    knot1 = step(knot0)
    shells = {
        "09": (1, 0, 0, 0, 0, 0, 0, 0, 0, 1),
        "18": (0, 1, 0, 0, 0, 0, 0, 0, 1, 0),
        "27": (0, 0, 1, 0, 0, 0, 0, 1, 0, 0),
        "36": (0, 0, 0, 1, 0, 0, 1, 0, 0, 0),
        "45": (0, 0, 0, 0, 1, 1, 0, 0, 0, 0),
    }
    lift_hits = []
    for s0_name, s0 in shells.items():
        for s1_name, s1 in shells.items():
            x0 = add(knot0, s0)
            x1 = add(knot1, s1)
            if step(x0) == x1 and step(x1) == x0:
                lift_hits.append({"s0": s0_name, "s1": s1_name, "x0": x0, "x1": x1})

    payload = {
        "symmetric_ansatz": "Q(w,x,y)=[0,2,w,x,y,y,x,w,2,3]",
        "period2_parameter_solution_count": len(solutions),
        "period2_unique_cycle_count": len(unique_cycles),
        "solutions": solutions,
        "knot": {"q0": knot0, "q1": knot1},
        "one_shell_lift_period2_hits": lift_hits,
    }
    OUT_JSON.write_text(json.dumps(payload, indent=2))
    print(f"JSON: {OUT_JSON}")
    print(f"period2_parameter_solution_count={len(solutions)}")
    print(f"period2_unique_cycle_count={len(unique_cycles)}")
    print(f"one_shell_lift_period2_hits={len(lift_hits)}")
    if solutions:
        print(solutions[0])


if __name__ == "__main__":
    main()
