#!/usr/bin/env python3
"""
Classify minimal one-shell transfer defects around the odd staircase ridge.

We treat the ridge
    R = (1,2,2,2,2,2,2,2,2,2)
as the saturated odd staircase endpoint, then enumerate every ordered
complementary-pair shell transfer:

    remove one shell from source pair P_src
    add one shell to destination pair P_dst

and classify the resulting orbit under K.

The goal is to verify that the only primitive period-3 defect rotor directions
are exactly
    36 -> 18, 36 -> 27, 36 -> 45,
which are the three H directions.
"""

from __future__ import annotations

import importlib.util
import json
from collections import Counter
from pathlib import Path


ROOT = Path("/Users/trentpalelei/Desktop/Math Ex/kaprekar_work")
INV_PATH = Path("/Users/trentpalelei/Desktop/Kaprekar/scripts/kaprekar_cycle_grammar_inventory.py")
OUT_JSON = ROOT / "kaprekar_ridge_defect_direction_2026-04-26.json"


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


def kstep(cnt: list[int]) -> tuple[list[int], int]:
    n = number_from_counts(cnt)
    return counts_of_number(n, sum(cnt)), n


def orbit_signature(start: list[int], limit: int = 30) -> dict[str, object]:
    seen: dict[tuple[int, ...], int] = {}
    states: list[list[int]] = []
    cur = start[:]
    numbers: list[int] = []
    for t in range(limit):
        key = tuple(cur)
        if key in seen:
            mu = seen[key]
            lam = t - mu
            cycle = states[mu:t]
            return {
                "mu": mu,
                "period": lam,
                "cycle_states": cycle,
                "cycle0": cycle[0],
                "numbers": numbers,
            }
        seen[key] = t
        states.append(cur[:])
        nxt, n = kstep(cur)
        numbers.append(n)
        cur = nxt
    raise RuntimeError("orbit did not close within limit")


def main() -> None:
    mod = load_inventory()

    ridge = [1, 2, 2, 2, 2, 2, 2, 2, 2, 2]
    H = mod.H_states(0)
    H_set = {tuple(row) for row in H}

    pairs = {
        "09": (0, 9),
        "18": (1, 8),
        "27": (2, 7),
        "36": (3, 6),
        "45": (4, 5),
    }

    rows = []
    primitive_h_directions: list[str] = []
    h_capture_directions: list[str] = []
    for src_name, (a, b) in pairs.items():
        for dst_name, (c, d) in pairs.items():
            if src_name == dst_name:
                continue
            defect = ridge[:]
            defect[a] -= 1
            defect[b] -= 1
            defect[c] += 1
            defect[d] += 1

            sig = orbit_signature(defect)
            cycle_set = {tuple(row) for row in sig["cycle_states"]}  # type: ignore[index]
            is_h_cycle = cycle_set == H_set and sig["period"] == 3
            is_primitive_h = is_h_cycle and sig["mu"] == 0
            is_h_capture = is_h_cycle and sig["mu"] > 0
            if is_primitive_h:
                primitive_h_directions.append(f"{src_name}->{dst_name}")
            if is_h_capture:
                h_capture_directions.append(f"{src_name}->{dst_name}")

            rows.append(
                {
                    "direction": f"{src_name}->{dst_name}",
                    "source_pair": src_name,
                    "dest_pair": dst_name,
                    "start": defect,
                    "mu": sig["mu"],
                    "period": sig["period"],
                    "cycle0": sig["cycle0"],
                    "numbers": sig["numbers"],
                    "is_H_cycle": is_h_cycle,
                    "is_primitive_H_rotor": is_primitive_h,
                    "is_H_capture": is_h_capture,
                }
            )

    payload = {
        "ridge": ridge,
        "ridge_number": number_from_counts(ridge),
        "H_states": H,
        "rows": rows,
        "primitive_H_directions": primitive_h_directions,
        "primitive_H_direction_count": len(primitive_h_directions),
        "H_capture_directions": h_capture_directions,
        "H_capture_direction_count": len(h_capture_directions),
    }

    OUT_JSON.write_text(json.dumps(payload, indent=2))
    print(f"JSON: {OUT_JSON}")
    print(f"primitive_H_directions={primitive_h_directions}")
    print(f"H_capture_directions={h_capture_directions}")


if __name__ == "__main__":
    main()
