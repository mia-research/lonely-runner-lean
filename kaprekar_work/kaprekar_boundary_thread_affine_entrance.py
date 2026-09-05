#!/usr/bin/env python3
"""
Verify the exact entrance law from the odd boundary thread K_p into the
delta=3 affine period-3 level.

Claim:
    For every p >= 8,
        K^12(K_p) = Z0(p-4) = R0_3(1, p-4, 4, 4, 4).
"""

from __future__ import annotations

import json
from collections import Counter
from pathlib import Path


ROOT = Path("/Users/trentpalelei/Desktop/Math Ex/kaprekar_work")
OUT_JSON = ROOT / "kaprekar_boundary_thread_affine_entrance_2026-05-19.json"


def number_from_counts(cnt: tuple[int, ...] | list[int]) -> int:
    desc = "".join(str(d) * cnt[d] for d in range(9, -1, -1))
    asc = "".join(str(d) * cnt[d] for d in range(10))
    return int(desc) - int(asc)


def counts_of_number(n: int, d: int) -> tuple[int, ...]:
    c = Counter(map(int, str(n).zfill(d)))
    return tuple(c[i] for i in range(10))


def step(cnt: tuple[int, ...] | list[int]) -> tuple[int, ...]:
    return counts_of_number(number_from_counts(cnt), sum(cnt))


def Kp(p: int) -> tuple[int, ...]:
    return (0, p, 3, 3, 3, 3, 3, 3, p, 3)


def Z0(r: int) -> tuple[int, ...]:
    return (1, r, 4, 4, 4, 4, 4, 4, r, 4)


def entrance_rows(p_min: int, p_max: int) -> dict[str, object]:
    bad = []
    rows = []
    for p in range(p_min, p_max + 1):
        cur = Kp(p)
        path = [list(cur)]
        for _ in range(12):
            cur = step(cur)
            path.append(list(cur))
        target = Z0(p - 4)
        ok = cur == target
        rows.append({"p": p, "d": sum(Kp(p)), "t12": list(cur), "target": list(target), "ok": ok})
        if not ok:
            bad.append({"p": p, "t12": list(cur), "target": list(target), "path": path})
    return {"checked": p_max - p_min + 1, "bad_count": len(bad), "bad_examples": bad[:3], "rows": rows[:8]}


def low_phase_table() -> list[dict[str, object]]:
    rows = []
    for p in range(0, 13):
        cur = Kp(p)
        seen = {}
        path = []
        while cur not in seen:
            seen[cur] = len(path)
            path.append(cur)
            cur = step(cur)
        cyc = path[seen[cur]:]
        rows.append(
            {
                "p": p,
                "d": sum(Kp(p)),
                "preperiod": seen[cur],
                "period": len(cyc),
                "cycle0": list(cyc[0]),
            }
        )
    return rows


def main() -> None:
    payload = {
        "entrance_p_ge_8": entrance_rows(8, 40),
        "low_phase_table": low_phase_table(),
    }
    OUT_JSON.write_text(json.dumps(payload, indent=2))
    print(f"JSON: {OUT_JSON}")
    print(payload["entrance_p_ge_8"])


if __name__ == "__main__":
    main()
