#!/usr/bin/env python3
"""
Scan the odd affine-delta period-3 normal form itself.

The goal is not a full odd-cycle census. It is a direct census *inside the
affine normal form* to see how much of the odd period-3 side is already forced
once the affine template is assumed.
"""

from __future__ import annotations

import json
from collections import Counter, defaultdict
from pathlib import Path


ROOT = Path("/Users/trentpalelei/Desktop/Math Ex/kaprekar_work")
OUT_JSON = ROOT / "kaprekar_odd_affine_delta_scan_2026-05-12.json"


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


def compositions(n: int, k: int) -> list[tuple[int, ...]]:
    if k == 1:
        return [(n,)]
    out = []
    for first in range(n + 1):
        for tail in compositions(n - first, k - 1):
            out.append((first,) + tail)
    return out


def R0(delta: int, u: int, v: int, w: int, x: int, y: int) -> tuple[int, ...]:
    return (u, v, w, x, y, y, x, w, v, u + delta)


def R1(delta: int, u: int, v: int, w: int, x: int, y: int) -> tuple[int, ...]:
    return (u, y, v, x, w, w, x, v, y, u + delta)


def R2(delta: int, u: int, v: int, w: int, x: int, y: int) -> tuple[int, ...]:
    return (u, w, y, x, v, v, x, y, w, u + delta)


def scan_delta(delta: int, d_max: int) -> dict[str, object]:
    by_d: dict[int, set[tuple[tuple[int, ...], ...]]] = defaultdict(set)
    samples: dict[int, list[dict[str, object]]] = defaultdict(list)
    for d in range(3, d_max + 1, 2):
        if d < delta or (d - delta) % 2 != 0:
            continue
        total = (d - delta) // 2
        for u, v, w, x, y in compositions(total, 5):
            r0 = R0(delta, u, v, w, x, y)
            r1 = R1(delta, u, v, w, x, y)
            r2 = R2(delta, u, v, w, x, y)
            if (
                step(r0) == r1
                and step(r1) == r2
                and step(r2) == r0
                and len({r0, r1, r2}) == 3
            ):
                cyc = canon_cycle([r0, r1, r2])
                if cyc not in by_d[d] and len(samples[d]) < 5:
                    samples[d].append(
                        {
                            "params": {"u": u, "v": v, "w": w, "x": x, "y": y},
                            "cycle0": list(cyc[0]),
                        }
                    )
                by_d[d].add(cyc)
    rows = []
    for d in sorted(by_d):
        rows.append({"d": d, "count": len(by_d[d]), "samples": samples[d]})
    return {"delta": delta, "rows": rows}


def main() -> None:
    payload = {
        "delta_1": scan_delta(1, 35),
        "delta_3": scan_delta(3, 55),
        "delta_5": scan_delta(5, 65),
    }
    OUT_JSON.write_text(json.dumps(payload, indent=2))
    print(f"JSON: {OUT_JSON}")
    for key in ("delta_1", "delta_3", "delta_5"):
        rows = payload[key]["rows"]
        print(key, [(row["d"], row["count"]) for row in rows[:12]])


if __name__ == "__main__":
    main()
