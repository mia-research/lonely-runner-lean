#!/usr/bin/env python3
"""
Bridge the reduced odd period-3 rotor cone and the K_p boundary-thread tail
into one odd affine-delta normal form.

Odd affine-delta phase states:
    R0_delta(u,v,w,x,y) = [u, v, w, x, y, y, x, w, v, u+delta]
    R1_delta(u,v,w,x,y) = [u, y, v, x, w, w, x, v, y, u+delta]
    R2_delta(u,v,w,x,y) = [u, w, y, x, v, v, x, y, w, u+delta]

This script checks two currently exact sectors:
  1. every exact reduced-sector odd period-3 attractor in the local census
     (d = 23,25,27,29) fits delta = 1
  2. the boundary-thread period-3 tail Z_r fits the same form at delta = 3
"""

from __future__ import annotations

import json
from collections import Counter
from pathlib import Path


ROOT = Path("/Users/trentpalelei/Desktop/Math Ex/kaprekar_work")
ODD_CENSUS_JSON = ROOT / "kaprekar_odd_cycle_census_2026-04-26.json"
BOUNDARY_JSON = ROOT / "kaprekar_boundary_thread_k_family_2026-05-12.json"
OUT_JSON = ROOT / "kaprekar_odd_period3_affine_levels_2026-05-12.json"


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


def phase_sum_template(cycle: list[tuple[int, ...]]) -> dict[str, object]:
    s = tuple(sum(state[i] for state in cycle) for i in range(10))
    ok = (
        s[1] == s[2] == s[4] == s[5] == s[7] == s[8]
        and s[3] == s[6]
        and (s[9] - s[0]) % 3 == 0
    )
    out = {"phase_sum": list(s), "ok": ok}
    if ok:
        out["u_sum"] = s[0]
        out["middle_sum"] = s[1]
        out["x_sum"] = s[3]
        out["delta"] = (s[9] - s[0]) // 3
    return out


def reduced_sector_check() -> dict[str, object]:
    obj = json.loads(ODD_CENSUS_JSON.read_text())
    rows = []
    bad = []
    for row in obj["rows"]:
        d = row["d"]
        if d not in (23, 25, 27, 29):
            continue
        p3 = [tuple(att["cycle0"]) for att in row["attractors"] if att["period"] == 3]
        fit_count = 0
        for cyc0 in p3:
            cyc1 = step(cyc0)
            cyc2 = step(cyc1)
            cycle = [cyc0, cyc1, cyc2]
            fits = [affine_delta_fit(state) for state in cycle]
            sums = phase_sum_template(cycle)
            if all(fit is not None and fit["delta"] == 1 for fit in fits) and sums["ok"]:
                fit_count += 1
            else:
                bad.append(
                    {
                        "d": d,
                        "cycle0": list(cyc0),
                        "fits": fits,
                        "phase_sum": sums,
                    }
                )
        rows.append({"d": d, "period3_count": len(p3), "fit_count": fit_count})
    return {"rows": rows, "bad_count": len(bad), "bad_examples": bad[:10]}


def boundary_tail_check(r_min: int, r_max: int) -> dict[str, object]:
    bad = []
    rows = []
    for r in range(r_min, r_max + 1):
        z0 = R0(3, 1, r, 4, 4, 4)
        z1 = R1(3, 1, r, 4, 4, 4)
        z2 = R2(3, 1, r, 4, 4, 4)
        cycle = [z0, z1, z2]
        fits = [affine_delta_fit(state) for state in cycle]
        sums = phase_sum_template(cycle)
        law_ok = step(z0) == z1 and step(z1) == z2 and step(z2) == z0
        if not (law_ok and all(fit is not None and fit["delta"] == 3 for fit in fits) and sums["ok"]):
            bad.append({"r": r, "fits": fits, "phase_sum": sums, "law_ok": law_ok})
        rows.append({"r": r, "cycle0": list(z0), "phase_sum": sums["phase_sum"]})
    return {"checked": r_max - r_min + 1, "rows": rows[:5], "bad_count": len(bad), "bad_examples": bad[:10]}


def boundary_thread_phase_rows() -> list[dict[str, object]]:
    obj = json.loads(BOUNDARY_JSON.read_text())
    return [row for row in obj["thread_rows"] if row["p"] >= 9][:5]


def main() -> None:
    payload = {
        "normal_form": {
            "R0_delta": "[u,v,w,x,y,y,x,w,v,u+delta]",
            "R1_delta": "[u,y,v,x,w,w,x,v,y,u+delta]",
            "R2_delta": "[u,w,y,x,v,v,x,y,w,u+delta]",
            "phase_sum_template": "[3u,M,M,3x,M,M,3x,M,M,3u+3delta]",
        },
        "reduced_sector_check": reduced_sector_check(),
        "boundary_tail_check": boundary_tail_check(5, 24),
        "boundary_thread_rows": boundary_thread_phase_rows(),
    }
    OUT_JSON.write_text(json.dumps(payload, indent=2))
    print(f"JSON: {OUT_JSON}")
    print(payload["reduced_sector_check"])
    print(payload["boundary_tail_check"])


if __name__ == "__main__":
    main()
