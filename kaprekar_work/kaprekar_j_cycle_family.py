#!/usr/bin/env python3
"""
Exact J-family period-3 cycle on the odd rotor side.

The reduced odd-state census shows one residual period-3 family at d=25 after
the four-direction H shell fan is accounted for. This probe verifies that the
residual is itself an exact +2_36 family:

    J_m = H_m + (18 + 27 + 45) uniformly across phases.
"""

from __future__ import annotations

import importlib.util
import json
from collections import Counter
from pathlib import Path


ROOT = Path("/Users/trentpalelei/Desktop/Math Ex/kaprekar_work")
INV_PATH = Path("/Users/trentpalelei/Desktop/Kaprekar/scripts/kaprekar_cycle_grammar_inventory.py")
OUT_JSON = ROOT / "kaprekar_j_cycle_family_2026-05-03.json"


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
    E = (0, 1, 1, 0, 1, 1, 0, 1, 1, 0)  # +18 +27 +45 uniformly

    checked = 0
    failures = 0
    witness = []
    for m in range(0, 21):
        H = mod.H_states(m)
        J = [add(row, E) for row in H]
        ok = True
        for i in range(3):
            if step(J[i]) != J[(i + 1) % 3]:
                ok = False
                failures += 1
                break
        checked += 1
        witness.append({"m": m, "d": 25 + 2 * m, "cycle0": J[0], "ok": ok})

    payload = {
        "uniform_residual_shell": E,
        "checked": checked,
        "failures": failures,
        "witness": witness,
    }

    OUT_JSON.write_text(json.dumps(payload, indent=2))
    print(f"JSON: {OUT_JSON}")
    print(f"checked={checked} failures={failures}")
    print(f"J0={witness[0]['cycle0']}")


if __name__ == "__main__":
    main()
