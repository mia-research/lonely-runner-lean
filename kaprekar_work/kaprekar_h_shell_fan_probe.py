#!/usr/bin/env python3
"""
Probe the transverse shell fan on top of the odd H rotor channel.

This script compares the reduced odd-state census at d=21,23,25 against the
closure generated from H by four shell directions:

  A = uniform +36  (the old axial m-axis)
  B = uniform +09
  C = rotating +45,+18,+27
  D = rotating +27,+45,+18

The question is whether the observed period-3 attractors are explained by the
degree-r closure of these directions, where r = (d-19)/2.
"""

from __future__ import annotations

import importlib.util
import json
from collections import Counter
from itertools import combinations_with_replacement
from pathlib import Path


ROOT = Path("/Users/trentpalelei/Desktop/Math Ex/kaprekar_work")
INV_PATH = Path("/Users/trentpalelei/Desktop/Kaprekar/scripts/kaprekar_cycle_grammar_inventory.py")
OUT_JSON = ROOT / "kaprekar_h_shell_fan_2026-04-26.json"


def load_module(path: Path, name: str):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(mod)
    return mod


def add(u: list[int], v: tuple[int, ...]) -> list[int]:
    return [a + b for a, b in zip(u, v)]


def number_from_counts(cnt: list[int] | tuple[int, ...]) -> int:
    desc = "".join(str(d) * cnt[d] for d in range(9, -1, -1))
    asc = "".join(str(d) * cnt[d] for d in range(10))
    return int(desc) - int(asc)


def counts_of_number(n: int, d: int) -> list[int]:
    c = Counter(map(int, str(n).zfill(d)))
    return [c[i] for i in range(10)]


def step(cnt: list[int] | tuple[int, ...]) -> list[int]:
    return counts_of_number(number_from_counts(cnt), sum(cnt))


def canon(cyc: list[list[int]] | list[tuple[int, ...]]) -> tuple[tuple[int, ...], ...]:
    rows = [tuple(x) for x in cyc]
    rots = [tuple(rows[i:] + rows[:i]) for i in range(len(rows))]
    return min(rots)


def period3_census_attractors(census_mod, d: int, inv_mod) -> set[tuple[tuple[int, ...], ...]]:
    row = census_mod.analyze_dimension(d, inv_mod)
    out = set()
    for att in row["attractors"]:
        if att["period"] == 3:
            cycle0 = att["cycle0"]
            cyc = [cycle0, step(cycle0), step(step(cycle0))]
            out.add(canon(cyc))
    return out


def main() -> None:
    inv = load_module(INV_PATH, "kap_cycle_inventory")
    census = load_module(ROOT / "kaprekar_odd_cycle_census.py", "kap_odd_census")

    H0 = inv.H_states(0)
    S36 = (0, 0, 0, 1, 0, 0, 1, 0, 0, 0)
    S09 = (1, 0, 0, 0, 0, 0, 0, 0, 0, 1)
    S18 = (0, 1, 0, 0, 0, 0, 0, 0, 1, 0)
    S27 = (0, 0, 1, 0, 0, 0, 0, 1, 0, 0)
    S45 = (0, 0, 0, 0, 1, 1, 0, 0, 0, 0)

    directions = {
        "A": [S36, S36, S36],
        "B": [S09, S09, S09],
        "C": [S45, S18, S27],
        "D": [S27, S45, S18],
    }

    rows = []
    for d in (21, 23, 25):
        r = (d - 19) // 2
        census_set = period3_census_attractors(census, d, inv)
        constructed = {}
        cons_set = set()
        for combo in combinations_with_replacement(sorted(directions.keys()), r):
            cyc = []
            for i in range(3):
                row = H0[i][:]
                for name in combo:
                    row = add(row, directions[name][i])
                cyc.append(row)
            ok = all(step(cyc[i]) == cyc[(i + 1) % 3] for i in range(3))
            cc = canon(cyc)
            constructed[combo] = {"ok": ok, "cycle0": cyc[0], "in_census": cc in census_set}
            if ok:
                cons_set.add(cc)

        missing = sorted(census_set - cons_set)
        extra = sorted(cons_set - census_set)
        rows.append(
            {
                "d": d,
                "shell_degree": r,
                "census_period3_count": len(census_set),
                "constructed_period3_count": len(cons_set),
                "missing_count": len(missing),
                "extra_count": len(extra),
                "missing_cycle0": [list(x[0]) for x in missing],
                "extra_cycle0": [list(x[0]) for x in extra],
                "constructed_rows": [
                    {
                        "combo": combo,
                        "ok": row["ok"],
                        "in_census": row["in_census"],
                        "cycle0": row["cycle0"],
                    }
                    for combo, row in sorted(constructed.items())
                ],
            }
        )

    payload = {
        "directions": {
            "A": directions["A"],
            "B": directions["B"],
            "C": directions["C"],
            "D": directions["D"],
        },
        "rows": rows,
    }
    OUT_JSON.write_text(json.dumps(payload, indent=2))
    print(f"JSON: {OUT_JSON}")
    for row in rows:
        print(
            f"d={row['d']} degree={row['shell_degree']} census={row['census_period3_count']} "
            f"constructed={row['constructed_period3_count']} missing={row['missing_count']} extra={row['extra_count']}"
        )


if __name__ == "__main__":
    main()
