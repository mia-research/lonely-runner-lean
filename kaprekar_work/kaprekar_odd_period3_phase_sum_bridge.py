#!/usr/bin/env python3
"""
Bridge odd period-3 affine cycles to the fixed-point grammar via phase sums.

Claim on the affine side:
  If C = (R0_delta, R1_delta, R2_delta) is an exact odd affine period-3 cycle,
  then the phase-sum vector
      S = R0_delta + R1_delta + R2_delta
  is itself a fixed point, with exact closed form
      S = [3u, M, M, 3x, M, M, 3x, M, M, 3u+3delta]
  where M = v+w+y.
"""

from __future__ import annotations

import json
import random
from collections import Counter
from pathlib import Path


ROOT = Path("/Users/trentpalelei/Desktop/Math Ex/kaprekar_work")
REDUCED_JSON = ROOT / "kaprekar_odd_cycle_census_2026-04-26.json"
BOUNDARY_JSON = ROOT / "kaprekar_boundary_thread_k_family_2026-05-12.json"
SAMPLE_JSON = ROOT / "kaprekar_global_odd_period3_sample_audit_2026-05-20.json"
OUT_JSON = ROOT / "kaprekar_odd_period3_phase_sum_bridge_2026-05-20.json"


def number_from_counts(cnt: tuple[int, ...] | list[int]) -> int:
    desc = "".join(str(d) * cnt[d] for d in range(9, -1, -1))
    asc = "".join(str(d) * cnt[d] for d in range(10))
    return int(desc) - int(asc)


def counts_of_number(n: int, d: int) -> tuple[int, ...]:
    c = Counter(map(int, str(n).zfill(d)))
    return tuple(c[i] for i in range(10))


def step(cnt: tuple[int, ...] | list[int]) -> tuple[int, ...]:
    return counts_of_number(number_from_counts(cnt), sum(cnt))


def R0(delta: int, u: int, v: int, w: int, x: int, y: int) -> tuple[int, ...]:
    return (u, v, w, x, y, y, x, w, v, u + delta)


def R1(delta: int, u: int, v: int, w: int, x: int, y: int) -> tuple[int, ...]:
    return (u, y, v, x, w, w, x, v, y, u + delta)


def R2(delta: int, u: int, v: int, w: int, x: int, y: int) -> tuple[int, ...]:
    return (u, w, y, x, v, v, x, y, w, u + delta)


def phase_sum(cycle: list[tuple[int, ...]]) -> tuple[int, ...]:
    return tuple(sum(state[i] for state in cycle) for i in range(10))


def affine_delta_fit(state: tuple[int, ...] | list[int]) -> dict[str, int] | None:
    c = tuple(state)
    delta = c[9] - c[0]
    if delta <= 0 or delta % 2 == 0:
        return None
    if not (c[1] == c[8] and c[2] == c[7] and c[3] == c[6] and c[4] == c[5]):
        return None
    return {
        "delta": delta,
        "u": c[0],
        "v": c[1],
        "w": c[2],
        "x": c[3],
        "y": c[4],
    }


def random_affine_checks(n: int, seed: int) -> dict[str, object]:
    rng = random.Random(seed)
    failures = []
    checked = 0
    while checked < n:
        delta = rng.choice([1, 3, 5])
        u = rng.randint(1, 4)
        v = rng.randint(delta + 1, delta + 5)
        w = rng.randint(v, v + 3)
        x = rng.randint(max(1, delta), delta + 4)
        y = rng.randint(max(w, v + 1), w + 3)
        cyc = [R0(delta, u, v, w, x, y), R1(delta, u, v, w, x, y), R2(delta, u, v, w, x, y)]
        if not (step(cyc[0]) == cyc[1] and step(cyc[1]) == cyc[2] and step(cyc[2]) == cyc[0] and len(set(cyc)) == 3):
            continue
        checked += 1
        s = phase_sum(cyc)
        M = v + w + y
        expected = (3 * u, M, M, 3 * x, M, M, 3 * x, M, M, 3 * u + 3 * delta)
        if step(s) != s or s != expected:
            failures.append(
                {
                    "params": {"delta": delta, "u": u, "v": v, "w": w, "x": x, "y": y},
                    "sum": list(s),
                    "expected": list(expected),
                    "step_sum": list(step(s)),
                }
            )
            break
    return {"checked": checked, "failures": len(failures), "bad_examples": failures[:5]}


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
            c1, c2 = step(c0), step(step(c0))
            cyc = [c0, c1, c2]
            s = phase_sum(cyc)
            fit = affine_delta_fit(c0)
            if fit is None:
                bad.append({"d": row["d"], "cycle0": list(c0), "reason": "non_affine_phase0"})
                continue
            M = fit["v"] + fit["w"] + fit["y"]
            expected = (3 * fit["u"], M, M, 3 * fit["x"], M, M, 3 * fit["x"], M, M, 3 * fit["u"] + 3 * fit["delta"])
            if step(s) == s and s == expected:
                ok += 1
            else:
                bad.append({"d": row["d"], "cycle0": list(c0), "sum": list(s), "expected": list(expected), "step_sum": list(step(s))})
        rows.append({"d": row["d"], "period3_count": len(p3), "ok_count": ok})
    return {"rows": rows, "bad_count": len(bad), "bad_examples": bad[:10]}


def boundary_check(r_min: int, r_max: int) -> dict[str, object]:
    bad = []
    for r in range(r_min, r_max + 1):
        cyc = [R0(3, 1, r, 4, 4, 4), R1(3, 1, r, 4, 4, 4), R2(3, 1, r, 4, 4, 4)]
        s = phase_sum(cyc)
        expected = (3, r + 8, r + 8, 12, r + 8, r + 8, 12, r + 8, r + 8, 12)
        if step(s) != s or s != expected:
            bad.append({"r": r, "sum": list(s), "expected": list(expected), "step_sum": list(step(s))})
            break
    return {"checked": r_max - r_min + 1, "bad_count": len(bad), "bad_examples": bad[:5]}


def sampled_global_check() -> dict[str, object]:
    obj = json.loads(SAMPLE_JSON.read_text())
    # This JSON records counts, not explicit cycles, so just summarize support.
    delta_support = {}
    for row in obj["rows"]:
        delta_support[str(row["d"])] = row["delta_histogram"]
    return {"sampled_delta_support": delta_support}


def main() -> None:
    payload = {
        "bridge_formula": {
            "phase_sum": "[3u, M, M, 3x, M, M, 3x, M, M, 3u+3delta]",
            "M": "v+w+y",
            "fixed_point": True,
        },
        "random_affine_checks": random_affine_checks(1000, 20260520),
        "reduced_exact_check": reduced_exact_check(),
        "boundary_check": boundary_check(5, 24),
        "sampled_global_check": sampled_global_check(),
    }
    OUT_JSON.write_text(json.dumps(payload, indent=2))
    print(f"JSON: {OUT_JSON}")
    print(payload["random_affine_checks"])
    print(payload["reduced_exact_check"])
    print(payload["boundary_check"])


if __name__ == "__main__":
    main()
