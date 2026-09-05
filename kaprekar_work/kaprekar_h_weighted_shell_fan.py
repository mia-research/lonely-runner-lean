#!/usr/bin/env python3
"""
Weighted shell-fan probe for the odd period-3 rotor side.

Base rotor: H at d=19.

Weight-1 directions:
  A = uniform +36
  B = uniform +09
  C = rotating +45,+18,+27
  D = rotating +27,+45,+18

Weight-3 direction:
  E = uniform +(18+27+45)

The hypothesis is that the odd period-3 sector at d = 19 + 2r is exactly the
weighted closure of H under these directions, where

  wt(A)=wt(B)=wt(C)=wt(D)=1, wt(E)=3.

This script computes the exact weighted closure counts, compares them with the
known exact reduced-state census counts at d=21,23,25, and then stress-tests
the closure against random reduced-state samples at d=27,29,31,33.
"""

from __future__ import annotations

import importlib.util
import json
import random
from collections import Counter
from pathlib import Path
from typing import Iterable


ROOT = Path("/Users/trentpalelei/Desktop/Math Ex/kaprekar_work")
INV_PATH = Path("/Users/trentpalelei/Desktop/Kaprekar/scripts/kaprekar_cycle_grammar_inventory.py")
OUT_JSON = ROOT / "kaprekar_h_weighted_shell_fan_2026-05-03.json"
ODD_CENSUS_JSON = ROOT / "kaprekar_odd_cycle_census_2026-04-26.json"


def load_inventory():
    spec = importlib.util.spec_from_file_location("kap_cycle_inventory", INV_PATH)
    mod = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(mod)
    return mod


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


def add(u: list[int] | tuple[int, ...], v: tuple[int, ...]) -> list[int]:
    return [a + b for a, b in zip(u, v)]


def rand_comp(n: int, k: int) -> list[int]:
    cuts = sorted(random.sample(range(n + k - 1), k - 1))
    arr: list[int] = []
    prev = -1
    for cut in cuts + [n + k - 1]:
        arr.append(cut - prev - 1)
        prev = cut
    return arr


def random_state_odd(d: int) -> tuple[int, ...]:
    l = (d - 1) // 2
    return tuple(rand_comp(l, 5) + rand_comp(l + 1, 5))


def weighted_multisets(weight: int, names: list[str], weights: dict[str, int], i: int = 0, cur: dict[str, int] | None = None) -> Iterable[dict[str, int]]:
    if cur is None:
        cur = {}
    if i == len(names):
        if weight == 0:
            yield cur.copy()
        return
    name = names[i]
    w = weights[name]
    for k in range(weight // w + 1):
        if k:
            cur[name] = k
        else:
            cur.pop(name, None)
        yield from weighted_multisets(weight - k * w, names, weights, i + 1, cur)
    cur.pop(name, None)


def build_weighted_closure(mod, r: int) -> dict[str, object]:
    H0 = mod.H_states(0)
    S36 = (0, 0, 0, 1, 0, 0, 1, 0, 0, 0)
    S09 = (1, 0, 0, 0, 0, 0, 0, 0, 0, 1)
    S18 = (0, 1, 0, 0, 0, 0, 0, 0, 1, 0)
    S27 = (0, 0, 1, 0, 0, 0, 0, 1, 0, 0)
    S45 = (0, 0, 0, 0, 1, 1, 0, 0, 0, 0)

    dirs = {
        "A": ([S36, S36, S36], 1),
        "B": ([S09, S09, S09], 1),
        "C": ([S45, S18, S27], 1),
        "D": ([S27, S45, S18], 1),
        "E": ([tuple(a + b + c for a, b, c in zip(S18, S27, S45))] * 3, 3),
    }
    names = sorted(dirs)
    weights = {k: v[1] for k, v in dirs.items()}

    cycles: dict[tuple[tuple[str, int], ...], tuple[tuple[int, ...], ...]] = {}
    for mults in weighted_multisets(r, names, weights):
        cyc: list[list[int]] = []
        for phase in range(3):
            row = H0[phase][:]
            for name, k in mults.items():
                for _ in range(k):
                    row = add(row, dirs[name][0][phase])
            cyc.append(row)
        if step(cyc[0]) == tuple(cyc[1]) and step(cyc[1]) == tuple(cyc[2]) and step(cyc[2]) == tuple(cyc[0]):
            key = tuple((name, mults[name]) for name in names if mults.get(name, 0))
            cycles[key] = canon(cyc)

    return {
        "weight": r,
        "unique_cycle_count": len(set(cycles.values())),
        "constructed_rows": [
            {"combo": list(key), "cycle0": list(cyc[0]), "d": sum(cyc[0])}
            for key, cyc in sorted(cycles.items())
        ],
    }


def sample_attractors(d: int, n_samples: int, seed: int) -> dict[str, object]:
    random.seed(seed)
    sampled: dict[tuple[tuple[int, ...], ...], int] = {}
    for _ in range(n_samples):
        s = random_state_odd(d)
        path: list[tuple[int, ...]] = []
        idx: dict[tuple[int, ...], int] = {}
        cur = s
        for _t in range(120):
            if cur in idx:
                cyc = path[idx[cur] :]
                if len(cyc) > 1:
                    sampled[canon(cyc)] = len(cyc)
                break
            idx[cur] = len(path)
            path.append(cur)
            cur = step(cur)

    period_hist = Counter(sampled.values())
    return {
        "d": d,
        "n_samples": n_samples,
        "seed": seed,
        "sampled_attractor_count": len(sampled),
        "period_histogram": dict(sorted(period_hist.items())),
        "period2_cycle0": [list(cyc[0]) for cyc, p in sampled.items() if p == 2],
        "period3_cycles": sorted(cyc for cyc, p in sampled.items() if p == 3),
    }


def main() -> None:
    mod = load_inventory()

    exact_rows = []
    expected_exact_counts = {21: 4, 23: 10}
    for d, expected in expected_exact_counts.items():
        r = (d - 19) // 2
        closure = build_weighted_closure(mod, r)
        exact_rows.append(
            {
                "d": d,
                "weight": r,
                "closure_count": closure["unique_cycle_count"],
                "expected_exact_census_count": expected,
                "matches_exact_count": closure["unique_cycle_count"] == expected,
                "period2_cycle0": [],
            }
        )

    if ODD_CENSUS_JSON.exists():
        census = json.loads(ODD_CENSUS_JSON.read_text())
        for row in census["rows"]:
            d = row["d"]
            if d in (25, 27, 29):
                r = (d - 19) // 2
                closure = build_weighted_closure(mod, r)
                period3_exact = sum(1 for att in row["attractors"] if att["period"] == 3)
                period2_exact = [att["cycle0"] for att in row["attractors"] if att["period"] == 2]
                exact_rows.append(
                    {
                        "d": d,
                        "weight": r,
                        "closure_count": closure["unique_cycle_count"],
                        "expected_exact_census_count": period3_exact,
                        "matches_exact_count": closure["unique_cycle_count"] == period3_exact,
                        "period2_cycle0": period2_exact,
                    }
                )

    sample_specs = {
        31: (80000, 2),
        33: (100000, 3),
    }
    sample_rows = []
    for d, (n_samples, seed) in sample_specs.items():
        r = (d - 19) // 2
        closure = build_weighted_closure(mod, r)
        closure_set = {tuple(map(tuple, row["cycle0:dummy"])) for row in []}
        # Rebuild the cycle set directly from constructed rows.
        weighted_set = set()
        for row in closure["constructed_rows"]:
            cycle0 = tuple(row["cycle0"])
            cycle1 = step(cycle0)
            cycle2 = step(cycle1)
            weighted_set.add(canon([cycle0, cycle1, cycle2]))

        sample = sample_attractors(d, n_samples, seed)
        sampled_p3 = sample["period3_cycles"]
        sampled_p3_set = set(sampled_p3)
        p3_misses = sampled_p3_set - weighted_set
        sample_rows.append(
            {
                "d": d,
                "weight": r,
                "closure_count": closure["unique_cycle_count"],
                "sampled_period3_count": len(sampled_p3_set),
                "sampled_period3_miss_count": len(p3_misses),
                "sampled_period2_cycle0": sample["period2_cycle0"],
                "sampled_period_histogram": sample["period_histogram"],
                "sampled_period3_miss_cycle0": [list(cyc[0]) for cyc in sorted(p3_misses)],
                "n_samples": n_samples,
                "seed": seed,
            }
        )

    payload = {
        "weight_1_directions": {
            "A": "uniform +36",
            "B": "uniform +09",
            "C": "rotating +45,+18,+27",
            "D": "rotating +27,+45,+18",
        },
        "weight_3_direction": {
            "E": "uniform +(18+27+45)",
        },
        "exact_rows": exact_rows,
        "sample_rows": sample_rows,
    }

    OUT_JSON.write_text(json.dumps(payload, indent=2))
    print(f"JSON: {OUT_JSON}")
    for row in exact_rows:
        print(
            f"d={row['d']} weight={row['weight']} closure={row['closure_count']} "
            f"expected={row['expected_exact_census_count']} ok={row['matches_exact_count']} "
            f"period2={row['period2_cycle0']}"
        )
    for row in sample_rows:
        print(
            f"d={row['d']} weight={row['weight']} closure={row['closure_count']} "
            f"sampled_p3={row['sampled_period3_count']} misses={row['sampled_period3_miss_count']} "
            f"period2={row['sampled_period2_cycle0']}"
        )


if __name__ == "__main__":
    main()
