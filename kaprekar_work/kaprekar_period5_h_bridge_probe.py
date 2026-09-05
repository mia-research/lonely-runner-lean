#!/usr/bin/env python3
"""
Count-space staircase automaton and H-ridge bridge for the odd cycle side.

This probe verifies:

1. the canonical count-space staircase recurrence on A,C,F,G,
2. the level-5 ridge collapse to a fixed count state,
3. the representation of H as ridge plus one rotating defect,
4. exact rotation of that defect under K.
"""

from __future__ import annotations

import importlib.util
import json
from collections import Counter
from pathlib import Path


ROOT = Path("/Users/trentpalelei/Desktop/Math Ex/kaprekar_work")
INV_PATH = Path("/Users/trentpalelei/Desktop/Kaprekar/scripts/kaprekar_cycle_grammar_inventory.py")
OUT_JSON = ROOT / "kaprekar_period5_h_bridge_2026-04-26.json"


def load_inventory():
    spec = importlib.util.spec_from_file_location("kap_cycle_inventory", INV_PATH)
    mod = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(mod)
    return mod


def rotate(rows: list[list[int]], k: int) -> list[list[int]]:
    n = len(rows)
    return [rows[(i + k) % n] for i in range(n)]


def add(u: list[int], v: tuple[int, ...]) -> list[int]:
    return [a + b for a, b in zip(u, v)]


def sub(u: list[int], v: list[int]) -> tuple[int, ...]:
    return tuple(a - b for a, b in zip(u, v))


def number_from_counts(cnt: list[int]) -> int:
    desc = "".join(str(d) * cnt[d] for d in range(9, -1, -1))
    asc = "".join(str(d) * cnt[d] for d in range(10))
    return int(desc) - int(asc)


def counts_of_number(n: int, d: int) -> list[int]:
    c = Counter(map(int, str(n).zfill(d)))
    return [c[i] for i in range(10)]


def kstep(cnt: list[int]) -> tuple[list[int], int]:
    n = number_from_counts(cnt)
    return counts_of_number(n, sum(cnt)), n


def main() -> None:
    mod = load_inventory()

    # Canonical staircase gauge in raw count space.
    A = rotate(mod.A_states(0), 0)
    C = rotate(mod.C_states(0), 3)
    F = rotate(mod.F_states(0), 1)
    G = rotate(mod.G_states(0), 1)
    H = rotate(mod.H_states(0), 0)

    levels = {1: A, 2: C, 3: F, 4: G}

    # Count-space layer pieces.
    N = [
        (0, 1, 0, 0, 0, 0, 0, 0, 1, 0),   # +18
        (0, 0, 1, 0, 0, 0, 0, 1, 0, 0),   # +27
        (0, 0, 0, 0, 1, 1, 0, 0, 0, 0),   # +45
        (1, -1, 1, 0, 0, 0, 0, 0, 1, 0),  # +028 -1
        (0, 1, -1, 1, 0, 0, 1, 0, -1, 1), # +1369 -28
    ]

    recurrence_checks = []
    recurrence_failures = 0
    for r in (1, 2, 3):
        src = levels[r]
        dst = levels[r + 1]
        rows = []
        ok = True
        for i in range(5):
            expected = N[(i + r - 1) % 5]
            observed = sub(dst[i], src[i])
            if observed != expected:
                ok = False
                recurrence_failures += 1
            rows.append({"phase": i, "observed": observed, "expected": expected})
        recurrence_checks.append({"from_level": r, "to_level": r + 1, "ok": ok, "phase_rows": rows})

    # Closed form to level 5.
    staircase = {1: A}
    cur = [row[:] for row in A]
    for r in range(1, 5):
        nxt = []
        for i in range(5):
            nxt.append(add(cur[i], N[(i + r - 1) % 5]))
        staircase[r + 1] = nxt
        cur = nxt

    ridge = [1, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    ridge_ok = all(row == ridge for row in staircase[5])
    ridge_step, ridge_number = kstep(ridge)
    ridge_fixed = ridge_step == ridge

    # H as rotating ridge defects.
    defect_45 = (0, 0, 0, -1, 1, 1, -1, 0, 0, 0)
    defect_18 = (0, 1, 0, -1, 0, 0, -1, 0, 1, 0)
    defect_27 = (0, 0, 1, -1, 0, 0, -1, 1, 0, 0)
    defects = [defect_45, defect_18, defect_27]
    H_from_ridge = [[a + b for a, b in zip(ridge, defect)] for defect in defects]
    H_match = H_from_ridge == H

    defect_rotation = []
    defect_failures = 0
    for i in range(3):
        nxt, n = kstep(H[i])
        expected = H[(i + 1) % 3]
        if nxt != expected:
            defect_failures += 1
        defect_rotation.append(
            {
                "phase": i,
                "number": n,
                "observed_next": nxt,
                "expected_next": expected,
                "observed_defect": sub(H[i], ridge),
                "expected_defect_next": sub(expected, ridge),
            }
        )

    payload = {
        "count_layer_pieces": N,
        "recurrence_checks": recurrence_checks,
        "recurrence_failures": recurrence_failures,
        "staircase_levels": {str(k): v for k, v in staircase.items()},
        "ridge": ridge,
        "ridge_number": ridge_number,
        "ridge_fixed": ridge_fixed,
        "ridge_ok": ridge_ok,
        "H_states": H,
        "H_defects": defects,
        "H_from_ridge": H_from_ridge,
        "H_match": H_match,
        "defect_rotation": defect_rotation,
        "defect_failures": defect_failures,
    }

    OUT_JSON.write_text(json.dumps(payload, indent=2))
    print(f"JSON: {OUT_JSON}")
    print(f"recurrence_failures={recurrence_failures}")
    print(f"ridge_ok={ridge_ok} ridge_fixed={ridge_fixed} ridge_number={ridge_number}")
    print(f"H_match={H_match} defect_failures={defect_failures}")


if __name__ == "__main__":
    main()
