#!/usr/bin/env python3
"""
Canonical period-5 staircase template probe for odd primitive Kaprekar kernels.

This probe packages the stable odd period-5 branch into one canonical phase
gauge and one fixed layer operator. It verifies:

1. the canonical gauge for A, C, F, G,
2. the exact recurrence S_{r+1}^{(i)} = S_r^{(i)} + M_{i+r-1 mod 5},
3. the closed-form cumulative formula for S_r,
4. collapse at level r=5 to the all-ones ridge,
5. the D -> E companion link as the same layer multiset with a phase offset.
"""

from __future__ import annotations

import importlib.util
import json
from collections import Counter
from pathlib import Path


ROOT = Path("/Users/trentpalelei/Desktop/Math Ex/kaprekar_work")
INV_PATH = Path("/Users/trentpalelei/Desktop/Kaprekar/scripts/kaprekar_cycle_grammar_inventory.py")
OUT_JSON = ROOT / "kaprekar_period5_staircase_template_2026-04-24.json"


def load_inventory():
    spec = importlib.util.spec_from_file_location("kap_cycle_inventory", INV_PATH)
    mod = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(mod)
    return mod


def gap_count_vector(cnt: list[int]) -> tuple[int, ...]:
    desc: list[int] = []
    for d in range(9, -1, -1):
        desc.extend([d] * cnt[d])
    asc = list(reversed(desc))
    gaps = [a - b for a, b in zip(desc, asc)][: (len(desc) + 1) // 2]
    c = Counter(x for x in gaps if x > 0)
    return tuple(c.get(k, 0) for k in range(1, 10))


def rotate(rows: list[tuple[int, ...]], k: int) -> list[tuple[int, ...]]:
    n = len(rows)
    return [rows[(i + k) % n] for i in range(n)]


def add(u: tuple[int, ...], v: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(a + b for a, b in zip(u, v))


def sub(u: tuple[int, ...], v: tuple[int, ...]) -> tuple[int, ...]:
    return tuple(a - b for a, b in zip(u, v))


def family_gap_rows(mod, name: str, rot: int) -> list[tuple[int, ...]]:
    raw = [gap_count_vector(s) for s in getattr(mod, f"{name}_states")(0)]
    return rotate(raw, rot)


def main() -> None:
    mod = load_inventory()

    # Canonical gauge for the main staircase channel.
    main_gauge = {"A": 0, "C": 3, "F": 1, "G": 1}
    main_rows = {name: family_gap_rows(mod, name, rot) for name, rot in main_gauge.items()}

    # Canonical level labels.
    levels = {1: "A", 2: "C", 3: "F", 4: "G"}

    # Fixed five-piece layer multiset in phase order.
    layer_pieces = [
        (0, 0, 0, 0, 0, 0, 1, 0, 0),   # M0 = L7
        (0, 0, 0, 0, 1, 0, 0, 0, 0),   # M1 = L5
        (1, 0, 0, 0, 0, 0, 0, 0, 0),   # M2 = L1
        (0, 0, 0, 0, 0, 1, 0, -1, 1),  # M3 = L79
        (0, 0, 1, 0, 0, -1, 0, 1, 0),  # M4 = L3
    ]

    recurrence_checks = []
    failures = 0
    for r in (1, 2, 3):
        src = main_rows[levels[r]]
        dst = main_rows[levels[r + 1]]
        phase_rows = []
        ok = True
        for i in range(5):
            expected = layer_pieces[(i + r - 1) % 5]
            observed = sub(dst[i], src[i])
            if observed != expected:
                ok = False
                failures += 1
            phase_rows.append({"phase": i, "observed": observed, "expected": expected})
        recurrence_checks.append({"from_level": r, "to_level": r + 1, "ok": ok, "phase_rows": phase_rows})

    # Closed-form cumulative staircase.
    S1 = main_rows["A"]
    closed_form = {}
    closed_form_failures = 0
    for r in range(1, 6):
        rows = []
        for i in range(5):
            row = S1[i]
            for t in range(max(0, r - 1)):
                row = add(row, layer_pieces[(i + t) % 5])
            rows.append(row)
        observed = main_rows.get(levels.get(r, ""))
        if observed is not None and rows != observed:
            closed_form_failures += 1
        closed_form[r] = rows

    ridge = (1, 1, 1, 1, 1, 1, 1, 1, 1)
    ridge_ok = all(row == ridge for row in closed_form[5])

    # Companion slice D -> E under a phase-offset copy of the same operator.
    companion_D = family_gap_rows(mod, "D", 0)
    companion_E = family_gap_rows(mod, "E", 2)
    companion_shift = 3
    companion_rows = []
    companion_ok = True
    for i in range(5):
        observed = sub(companion_E[i], companion_D[i])
        expected = layer_pieces[(i + companion_shift) % 5]
        if observed != expected:
            companion_ok = False
        companion_rows.append({"phase": i, "observed": observed, "expected": expected})

    payload = {
        "main_gauge": main_gauge,
        "main_levels": {str(k): v for k, v in levels.items()},
        "layer_pieces": layer_pieces,
        "recurrence_checks": recurrence_checks,
        "recurrence_failures": failures,
        "closed_form_levels": {str(k): v for k, v in closed_form.items()},
        "closed_form_failures": closed_form_failures,
        "ridge_level": 5,
        "ridge_vector": ridge,
        "ridge_ok": ridge_ok,
        "companion_slice": {
            "D_rotation": 0,
            "E_rotation": 2,
            "phase_offset": companion_shift,
            "ok": companion_ok,
            "phase_rows": companion_rows,
        },
    }

    OUT_JSON.write_text(json.dumps(payload, indent=2))

    print(f"JSON: {OUT_JSON}")
    print(f"recurrence_failures={failures}")
    print(f"closed_form_failures={closed_form_failures}")
    print(f"ridge_ok={ridge_ok}")
    print(f"companion_ok={companion_ok}")
    print("level5:")
    for row in closed_form[5]:
        print(row)


if __name__ == "__main__":
    main()
