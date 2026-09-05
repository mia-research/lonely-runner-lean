#!/usr/bin/env python3
"""
Odd count-state cycle census on the reduced high-minus-low=1 state space.

State space:
  counts c0..c9 with
    sum(c0..c4) = l
    sum(c5..c9) = l+1
  so d = 2l+1 and the total high-side excess is exactly 1.

For a given odd d, this enumerates all such count states, computes their
Kaprekar successors in count space, and classifies the non-fixed attractor
cycles. It then matches attractors against the current known odd cycle-family
inventory A..H (and T for d=11).
"""

from __future__ import annotations

import argparse
import importlib.util
import json
from collections import Counter, defaultdict
from pathlib import Path
from typing import Iterable


ROOT = Path("/Users/trentpalelei/Desktop/Math Ex/kaprekar_work")
INV_PATH = Path("/Users/trentpalelei/Desktop/Kaprekar/scripts/kaprekar_cycle_grammar_inventory.py")
OUT_JSON = ROOT / "kaprekar_odd_cycle_census_2026-04-26.json"


def load_inventory():
    spec = importlib.util.spec_from_file_location("kap_cycle_inventory", INV_PATH)
    mod = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(mod)
    return mod


def compositions(n: int, k: int) -> Iterable[tuple[int, ...]]:
    if k == 1:
        yield (n,)
        return
    for first in range(n + 1):
        for tail in compositions(n - first, k - 1):
            yield (first,) + tail


def number_from_counts(cnt: tuple[int, ...]) -> int:
    desc = "".join(str(d) * cnt[d] for d in range(9, -1, -1))
    asc = "".join(str(d) * cnt[d] for d in range(10))
    return int(desc) - int(asc)


def counts_of_number(n: int, d: int) -> tuple[int, ...]:
    c = Counter(map(int, str(n).zfill(d)))
    return tuple(c[i] for i in range(10))


def succ(cnt: tuple[int, ...]) -> tuple[int, ...]:
    return counts_of_number(number_from_counts(cnt), sum(cnt))


def family_cycles_for_dimension(mod, d: int) -> dict[str, set[tuple[tuple[int, ...], ...]]]:
    out: dict[str, set[tuple[tuple[int, ...], ...]]] = defaultdict(set)

    def canon(states: list[list[int]]) -> tuple[tuple[int, ...], ...]:
        cyc = [tuple(s) for s in states]
        rots = [tuple(cyc[i:] + cyc[:i]) for i in range(len(cyc))]
        return min(rots)

    if d >= 11 and d % 2 == 1:
        candidates = {
            "A": mod.A_states((d - 11) // 2) if d >= 11 else None,
            "B": mod.B_states((d - 13) // 2) if d >= 13 else None,
            "C": mod.C_states((d - 13) // 2) if d >= 13 else None,
            "D": mod.D_states((d - 13) // 2) if d >= 13 else None,
            "E": mod.E_states((d - 15) // 2) if d >= 15 else None,
            "F": mod.F_states((d - 15) // 2) if d >= 15 else None,
            "G": mod.G_states((d - 17) // 2) if d >= 17 else None,
            "H": mod.H_states((d - 19) // 2) if d >= 19 else None,
        }
        for name, states in candidates.items():
            if states is not None and sum(states[0]) == d:
                out[name].add(canon(states))

        if d == 11:
            out["T"].add(canon(mod.T_states(0)))

    return out


def canon_cycle(cycle: list[tuple[int, ...]]) -> tuple[tuple[int, ...], ...]:
    rots = [tuple(cycle[i:] + cycle[:i]) for i in range(len(cycle))]
    return min(rots)


def analyze_dimension(d: int, mod) -> dict[str, object]:
    assert d % 2 == 1
    l = (d - 1) // 2
    known = family_cycles_for_dimension(mod, d)
    known_lookup: dict[tuple[tuple[int, ...], ...], str] = {}
    for fam, cycset in known.items():
        for cyc in cycset:
            known_lookup[cyc] = fam

    memo: dict[tuple[int, ...], tuple[int, tuple[tuple[int, ...], ...]]] = {}
    attractors: dict[tuple[tuple[int, ...], ...], dict[str, object]] = {}
    state_count = 0

    for low in compositions(l, 5):
        for high in compositions(l + 1, 5):
            state = tuple(low + high)
            state_count += 1
            if state in memo:
                continue

            path: list[tuple[int, ...]] = []
            seen: dict[tuple[int, ...], int] = {}
            cur = state

            while cur not in memo and cur not in seen:
                seen[cur] = len(path)
                path.append(cur)
                cur = succ(cur)

            if cur in memo:
                period, cyc = memo[cur]
                start_idx = None
            else:
                start_idx = seen[cur]
                cyc_states = path[start_idx:]
                cyc = canon_cycle(cyc_states)
                period = len(cyc_states)

            for s in path:
                memo[s] = (period, cyc)

            if period > 1 and cyc not in attractors:
                family = known_lookup.get(cyc, "UNKNOWN")
                attractors[cyc] = {
                    "period": period,
                    "family": family,
                    "cycle0": cyc[0],
                }

    period_hist = Counter(row["period"] for row in attractors.values())
    family_hist = Counter(row["family"] for row in attractors.values())

    return {
        "d": d,
        "reduced_state_count": state_count,
        "nonfixed_attractor_count": len(attractors),
        "period_histogram": dict(sorted(period_hist.items())),
        "family_histogram": dict(sorted(family_hist.items())),
        "unknown_count": sum(1 for row in attractors.values() if row["family"] == "UNKNOWN"),
        "attractors": [
            {
                "period": row["period"],
                "family": row["family"],
                "cycle0": list(row["cycle0"]),
            }
            for row in sorted(attractors.values(), key=lambda x: (x["period"], x["family"], x["cycle0"]))
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Reduced odd count-space cycle census.")
    parser.add_argument("--dims", nargs="+", type=int, default=[11, 13, 15, 17, 19, 21])
    parser.add_argument("--json-out", type=Path, default=OUT_JSON)
    args = parser.parse_args()

    mod = load_inventory()
    payload = {
        "dims": args.dims,
        "rows": [analyze_dimension(d, mod) for d in args.dims],
    }

    args.json_out.write_text(json.dumps(payload, indent=2))
    print(f"JSON: {args.json_out}")
    for row in payload["rows"]:
        print(
            "d={d} states={reduced_state_count} attractors={nonfixed_attractor_count} unknown={unknown_count} fams={family_histogram}".format(
                **row
            )
        )


if __name__ == "__main__":
    main()
