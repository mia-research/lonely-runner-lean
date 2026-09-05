#!/usr/bin/env python3
"""
Exact affine rotor law for the odd period-3 sector.

Phase-0 template:
    R0(u,v,w,x,y) = [u, v, w, x, y, y, x, w, v, u+1]

with phase rotations
    R1(u,v,w,x,y) = [u, y, v, x, w, w, x, v, y, u+1]
    R2(u,v,w,x,y) = [u, w, y, x, v, v, x, y, w, u+1]

The weighted H-shell fan becomes the affine cone
    u >= 1, x >= 1, v >= 2, w >= v, y >= v+1

with unique generator decomposition
    b = u-1
    e = v-2
    d = w-v
    a = x-1
    c = y-v-1
relative to the base rotor H = R(1,2,2,1,3).
"""

from __future__ import annotations

import importlib.util
import json
import random
from collections import Counter
from pathlib import Path


ROOT = Path("/Users/trentpalelei/Desktop/Math Ex/kaprekar_work")
INV_PATH = Path("/Users/trentpalelei/Desktop/Kaprekar/scripts/kaprekar_cycle_grammar_inventory.py")
ODD_CENSUS_JSON = ROOT / "kaprekar_odd_cycle_census_2026-04-26.json"
OUT_JSON = ROOT / "kaprekar_odd_period3_affine_rotor_2026-05-03.json"


def number_from_counts(cnt: list[int] | tuple[int, ...]) -> int:
    desc = "".join(str(d) * cnt[d] for d in range(9, -1, -1))
    asc = "".join(str(d) * cnt[d] for d in range(10))
    return int(desc) - int(asc)


def counts_of_number(n: int, d: int) -> tuple[int, ...]:
    c = Counter(map(int, str(n).zfill(d)))
    return tuple(c[i] for i in range(10))


def step(cnt: list[int] | tuple[int, ...]) -> tuple[int, ...]:
    return counts_of_number(number_from_counts(cnt), sum(cnt))


def canon(cycle: list[list[int]] | list[tuple[int, ...]]) -> tuple[tuple[int, ...], ...]:
    rows = [tuple(x) for x in cycle]
    rots = [tuple(rows[i:] + rows[:i]) for i in range(len(rows))]
    return min(rots)


def R0(u: int, v: int, w: int, x: int, y: int) -> list[int]:
    return [u, v, w, x, y, y, x, w, v, u + 1]


def R1(u: int, v: int, w: int, x: int, y: int) -> list[int]:
    return [u, y, v, x, w, w, x, v, y, u + 1]


def R2(u: int, v: int, w: int, x: int, y: int) -> list[int]:
    return [u, w, y, x, v, v, x, y, w, u + 1]


def affine_fit(state: list[int] | tuple[int, ...]) -> dict[str, int] | None:
    c = list(state)
    if not (
        c[9] == c[0] + 1
        and c[1] == c[8]
        and c[2] == c[7]
        and c[3] == c[6]
        and c[4] == c[5]
    ):
        return None
    u, v, w, x, y = c[0], c[1], c[2], c[3], c[4]
    if not (u >= 1 and x >= 1 and v >= 2 and w >= v and y >= v + 1):
        return None
    return {
        "u": u,
        "v": v,
        "w": w,
        "x": x,
        "y": y,
        "A": x - 1,
        "B": u - 1,
        "C": y - v - 1,
        "D": w - v,
        "E": v - 2,
    }


def random_param_checks(n: int, seed: int) -> dict[str, object]:
    random.seed(seed)
    failures = []
    for _ in range(n):
        u = random.randint(1, 8)
        x = random.randint(1, 8)
        v = random.randint(2, 10)
        w = random.randint(v, 12)
        y = random.randint(v + 1, 13)
        r0, r1, r2 = R0(u, v, w, x, y), R1(u, v, w, x, y), R2(u, v, w, x, y)
        if step(r0) != tuple(r1) or step(r1) != tuple(r2) or step(r2) != tuple(r0):
            failures.append({"u": u, "v": v, "w": w, "x": x, "y": y})
            break
    return {"checked": n, "failures": len(failures), "first_failure": failures[:1]}


def exact_census_fit() -> dict[str, object]:
    obj = json.loads(ODD_CENSUS_JSON.read_text())
    bad = []
    rows = []
    for row in obj["rows"]:
        if row["d"] not in (25, 27, 29):
            continue
        p3 = [att["cycle0"] for att in row["attractors"] if att["period"] == 3]
        fits = []
        for cyc0 in p3:
            fit = affine_fit(cyc0)
            if fit is None:
                bad.append({"d": row["d"], "cycle0": cyc0})
            else:
                fits.append({"cycle0": cyc0, "fit": fit})
        rows.append({"d": row["d"], "period3_count": len(p3), "fit_count": len(fits)})
    return {"rows": rows, "bad_count": len(bad), "bad_examples": bad[:10]}


def main() -> None:
    payload = {
        "law": {
            "R0": "[u,v,w,x,y,y,x,w,v,u+1]",
            "R1": "[u,y,v,x,w,w,x,v,y,u+1]",
            "R2": "[u,w,y,x,v,v,x,y,w,u+1]",
            "constraints": "u>=1, x>=1, v>=2, w>=v, y>=v+1",
            "generator_coordinates": {
                "A": "x-1",
                "B": "u-1",
                "C": "y-v-1",
                "D": "w-v",
                "E": "v-2",
            },
        },
        "random_param_checks": random_param_checks(5000, 0),
        "exact_census_fit": exact_census_fit(),
    }
    OUT_JSON.write_text(json.dumps(payload, indent=2))
    print(f"JSON: {OUT_JSON}")
    print(payload["random_param_checks"])
    print(payload["exact_census_fit"])


if __name__ == "__main__":
    main()
