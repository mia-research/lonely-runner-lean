#!/usr/bin/env python3
"""
Boundary thread K_p on the odd cycle side.

Definition:
    K_p = [0, p, 3, 3, 3, 3, 3, 3, p, 3]
    d = 21 + 2p

Observed exact phase diagram:
  p=1,2   -> period-2
  p=3     -> fixed
  p=4..7  -> period-5 after finite preperiod
  p=8     -> fixed
  p>=9    -> exact period-3 family Z_{p-4}

This script verifies the thread directly on a window and separately verifies
the period-3 tail family Z_r for a broader range.
"""

from __future__ import annotations

import json
from collections import Counter
from pathlib import Path


ROOT = Path("/Users/trentpalelei/Desktop/Math Ex/kaprekar_work")
OUT_JSON = ROOT / "kaprekar_boundary_thread_k_family_2026-05-12.json"


def number_from_counts(cnt: list[int] | tuple[int, ...]) -> int:
    desc = "".join(str(d) * cnt[d] for d in range(9, -1, -1))
    asc = "".join(str(d) * cnt[d] for d in range(10))
    return int(desc) - int(asc)


def counts_of_number(n: int, d: int) -> tuple[int, ...]:
    c = Counter(map(int, str(n).zfill(d)))
    return tuple(c[i] for i in range(10))


def step(cnt: list[int] | tuple[int, ...]) -> tuple[int, ...]:
    return counts_of_number(number_from_counts(cnt), sum(cnt))


def K_thread(p: int) -> tuple[int, ...]:
    return (0, p, 3, 3, 3, 3, 3, 3, p, 3)


def Z0(r: int) -> tuple[int, ...]:
    return (1, r, 4, 4, 4, 4, 4, 4, r, 4)


def Z1(r: int) -> tuple[int, ...]:
    return (1, 4, r, 4, 4, 4, 4, r, 4, 4)


def Z2(r: int) -> tuple[int, ...]:
    return (1, 4, 4, 4, r, r, 4, 4, 4, 4)


def classify_thread(p_max: int) -> list[dict[str, object]]:
    rows = []
    for p in range(0, p_max + 1):
        x = K_thread(p)
        path: list[tuple[int, ...]] = []
        idx: dict[tuple[int, ...], int] = {}
        cur = x
        for _ in range(100):
            if cur in idx:
                cyc = path[idx[cur] :]
                rows.append(
                    {
                        "p": p,
                        "d": sum(x),
                        "preperiod": idx[cur],
                        "period": len(cyc),
                        "cycle0": list(cyc[0]),
                    }
                )
                break
            idx[cur] = len(path)
            path.append(cur)
            cur = step(cur)
    return rows


def verify_Z_tail(r_min: int, r_max: int) -> dict[str, object]:
    bad = []
    for r in range(r_min, r_max + 1):
        z0, z1, z2 = Z0(r), Z1(r), Z2(r)
        if not (step(z0) == z1 and step(z1) == z2 and step(z2) == z0):
            bad.append({"r": r, "z0": list(z0), "kz0": list(step(z0))})
    return {"checked": r_max - r_min + 1, "failures": len(bad), "bad_examples": bad[:5]}


def main() -> None:
    thread_rows = classify_thread(20)
    payload = {
        "thread_rows": thread_rows,
        "z_tail_verification": verify_Z_tail(5, 24),
    }
    OUT_JSON.write_text(json.dumps(payload, indent=2))
    print(f"JSON: {OUT_JSON}")
    for row in thread_rows:
        print(
            f"p={row['p']} d={row['d']} pre={row['preperiod']} per={row['period']} cycle0={row['cycle0']}"
        )
    print(payload["z_tail_verification"])


if __name__ == "__main__":
    main()
