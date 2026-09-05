#!/usr/bin/env python3
"""
Verify B as a two-phase boundary repair of the unstable T seed.

For every m >= 0:
  B0(m) = T0(m) + 45
  B1(m) = T5(m) + 36

This gives a compact absorption of the period-2 line B into the same shell
grammar that already contains the unstable T seed.
"""

from __future__ import annotations

import importlib.util
import json
from collections import Counter
from pathlib import Path


ROOT = Path("/Users/trentpalelei/Desktop/Math Ex/kaprekar_work")
INV_PATH = Path("/Users/trentpalelei/Desktop/Kaprekar/scripts/kaprekar_cycle_grammar_inventory.py")
OUT_JSON = ROOT / "kaprekar_b_boundary_repair_2026-05-03.json"


def load_inventory():
    spec = importlib.util.spec_from_file_location("kap_cycle_inventory", INV_PATH)
    mod = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(mod)
    return mod


def number_from_counts(cnt: list[int]) -> int:
    desc = "".join(str(d) * cnt[d] for d in range(9, -1, -1))
    asc = "".join(str(d) * cnt[d] for d in range(10))
    return int(desc) - int(asc)


def counts_of_number(n: int, d: int) -> list[int]:
    c = Counter(map(int, str(n).zfill(d)))
    return [c[i] for i in range(10)]


def step(cnt: list[int]) -> list[int]:
    return counts_of_number(number_from_counts(cnt), sum(cnt))


def add(u: list[int], v: tuple[int, ...]) -> list[int]:
    return [a + b for a, b in zip(u, v)]


def main() -> None:
    mod = load_inventory()
    S36 = (0, 0, 0, 1, 0, 0, 1, 0, 0, 0)
    S45 = (0, 0, 0, 0, 1, 1, 0, 0, 0, 0)

    checked = 0
    failures = 0
    rows = []
    for m in range(0, 21):
        T = mod.T_states(m)
        B = mod.B_states(m)
        cand0 = add(T[0], S45)
        cand1 = add(T[5], S36)
        exact = cand0 == B[0] and cand1 == B[1]
        period2 = step(B[0]) == B[1] and step(B[1]) == B[0]
        if not (exact and period2):
            failures += 1
        checked += 1
        rows.append(
            {
                "m": m,
                "d": 13 + 2 * m,
                "T0_plus_45": cand0,
                "T5_plus_36": cand1,
                "B0": B[0],
                "B1": B[1],
                "exact": exact,
                "period2": period2,
            }
        )

    payload = {
        "shell_36": S36,
        "shell_45": S45,
        "checked": checked,
        "failures": failures,
        "rows": rows,
    }

    OUT_JSON.write_text(json.dumps(payload, indent=2))
    print(f"JSON: {OUT_JSON}")
    print(f"checked={checked} failures={failures}")
    print(f"B0={rows[0]['B0']}")


if __name__ == "__main__":
    main()
