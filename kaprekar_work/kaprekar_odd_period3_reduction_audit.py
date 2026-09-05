#!/usr/bin/env python3
"""
Audit the two-invariant reduction for odd period-3 cycles:

1. phase-sum fixedpoint
2. phasewise asymmetry constancy

This does not prove the reduction, but checks it on:
  - exact reduced odd period-3 census
  - boundary-thread tail
  - sampled full odd count-state universe
"""

from __future__ import annotations

import json
import random
from collections import Counter
from pathlib import Path


ROOT = Path("/Users/trentpalelei/Desktop/Math Ex/kaprekar_work")
REDUCED_JSON = ROOT / "kaprekar_odd_cycle_census_2026-04-26.json"
OUT_JSON = ROOT / "kaprekar_odd_period3_reduction_audit_2026-05-20.json"


def number_from_counts(cnt: tuple[int, ...] | list[int]) -> int:
    desc = "".join(str(d) * cnt[d] for d in range(9, -1, -1))
    asc = "".join(str(d) * cnt[d] for d in range(10))
    return int(desc) - int(asc)


def counts_of_number(n: int, d: int) -> tuple[int, ...]:
    c = Counter(map(int, str(n).zfill(d)))
    return tuple(c[i] for i in range(10))


def step(cnt: tuple[int, ...] | list[int]) -> tuple[int, ...]:
    return counts_of_number(number_from_counts(cnt), sum(cnt))


def canon_cycle(cycle: list[tuple[int, ...]]) -> tuple[tuple[int, ...], ...]:
    rots = [tuple(cycle[i:] + cycle[:i]) for i in range(len(cycle))]
    return min(rots)


def asym(cnt: tuple[int, ...] | list[int]) -> tuple[int, int, int, int, int]:
    c = tuple(cnt)
    return (c[9] - c[0], c[8] - c[1], c[7] - c[2], c[6] - c[3], c[5] - c[4])


def phase_sum(cycle: list[tuple[int, ...]]) -> tuple[int, ...]:
    return tuple(sum(state[i] for state in cycle) for i in range(10))


def random_composition(n: int, k: int, rng: random.Random) -> tuple[int, ...]:
    cuts = sorted(rng.sample(range(n + k - 1), k - 1))
    pts = [-1] + cuts + [n + k - 1]
    return tuple(pts[i + 1] - pts[i] - 1 for i in range(k))


def attractor_from_state(state: tuple[int, ...]) -> tuple[int, tuple[tuple[int, ...], ...]]:
    seen: dict[tuple[int, ...], int] = {}
    path: list[tuple[int, ...]] = []
    cur = state
    while cur not in seen:
        seen[cur] = len(path)
        path.append(cur)
        cur = step(cur)
    cyc = path[seen[cur]:]
    return len(cyc), canon_cycle(cyc)


def cycle_checks(cycle: list[tuple[int, ...]]) -> dict[str, object]:
    a = [asym(c) for c in cycle]
    s = phase_sum(cycle)
    return {
        "asymmetry_constant": a[0] == a[1] == a[2],
        "asymmetry_values": [list(x) for x in a],
        "phase_sum_fixed": step(s) == s,
        "phase_sum": list(s),
        "phase_sum_asymmetry": list(asym(s)),
    }


def reduced_exact_check() -> dict[str, object]:
    obj = json.loads(REDUCED_JSON.read_text())
    bad = []
    rows = []
    for row in obj["rows"]:
        if row["d"] not in (23, 25, 27, 29):
            continue
        p3 = [tuple(att["cycle0"]) for att in row["attractors"] if att["period"] == 3]
        ok = 0
        for c0 in p3:
            cyc = [c0, step(c0), step(step(c0))]
            chk = cycle_checks(cyc)
            if chk["asymmetry_constant"] and chk["phase_sum_fixed"]:
                ok += 1
            else:
                bad.append({"d": row["d"], "cycle0": list(c0), "check": chk})
        rows.append({"d": row["d"], "period3_count": len(p3), "ok_count": ok})
    return {"rows": rows, "bad_count": len(bad), "bad_examples": bad[:10]}


def boundary_tail_check(r_min: int, r_max: int) -> dict[str, object]:
    bad = []
    for r in range(r_min, r_max + 1):
        cyc = [
            (1, r, 4, 4, 4, 4, 4, 4, r, 4),
            (1, 4, r, 4, 4, 4, 4, r, 4, 4),
            (1, 4, 4, 4, r, r, 4, 4, 4, 4),
        ]
        chk = cycle_checks(cyc)
        if not (chk["asymmetry_constant"] and chk["phase_sum_fixed"]):
            bad.append({"r": r, "check": chk})
            break
    return {"checked": r_max - r_min + 1, "bad_count": len(bad), "bad_examples": bad[:5]}


def sampled_global_check() -> dict[str, object]:
    dims = [19, 21, 23, 25, 27, 29, 31, 33, 39, 45, 55]
    rows = []
    bad = []
    for i, d in enumerate(dims):
        rng = random.Random(20260520 + i)
        seen_period3: set[tuple[tuple[int, ...], ...]] = set()
        bad_here = 0
        for _ in range(5000):
            s = random_composition(d, 10, rng)
            period, cyc = attractor_from_state(s)
            if period == 3 and cyc not in seen_period3:
                seen_period3.add(cyc)
                chk = cycle_checks(list(cyc))
                if not (chk["asymmetry_constant"] and chk["phase_sum_fixed"]):
                    bad_here += 1
                    if len(bad) < 10:
                        bad.append({"d": d, "cycle0": list(cyc[0]), "check": chk})
        rows.append({"d": d, "distinct_period3_seen": len(seen_period3), "bad_count": bad_here})
    return {"rows": rows, "bad_count": len(bad), "bad_examples": bad}


def main() -> None:
    payload = {
        "reduction_statement": [
            "phase-sum fixedpoint",
            "phasewise asymmetry constancy",
        ],
        "reduced_exact_check": reduced_exact_check(),
        "boundary_tail_check": boundary_tail_check(5, 24),
        "sampled_global_check": sampled_global_check(),
    }
    OUT_JSON.write_text(json.dumps(payload, indent=2))
    print(f"JSON: {OUT_JSON}")
    print(payload["reduced_exact_check"])
    print(payload["boundary_tail_check"])
    print(payload["sampled_global_check"])


if __name__ == "__main__":
    main()
