#!/usr/bin/env python3
"""
Verify the exact delta-lift on the odd affine period-3 normal form.

Lift operator:
    L(R_delta(u,v,w,x,y)) = R_{delta+2}(u, v+2, w+2, x+2, y+2)

This raises dimension by 18.
"""

from __future__ import annotations

import json
from collections import Counter, defaultdict
from pathlib import Path


ROOT = Path("/Users/trentpalelei/Desktop/Math Ex/kaprekar_work")
OUT_JSON = ROOT / "kaprekar_odd_affine_delta_lift_2026-05-19.json"


def number_from_counts(cnt: tuple[int, ...] | list[int]) -> int:
    desc = "".join(str(d) * cnt[d] for d in range(9, -1, -1))
    asc = "".join(str(d) * cnt[d] for d in range(10))
    return int(desc) - int(asc)


def counts_of_number(n: int, d: int) -> tuple[int, ...]:
    c = Counter(map(int, str(n).zfill(d)))
    return tuple(c[i] for i in range(10))


def step(cnt: tuple[int, ...] | list[int]) -> tuple[int, ...]:
    return counts_of_number(number_from_counts(cnt), sum(cnt))


def compositions(n: int, k: int):
    if k == 1:
        yield (n,)
        return
    for first in range(n + 1):
        for tail in compositions(n - first, k - 1):
            yield (first,) + tail


def R0(delta: int, u: int, v: int, w: int, x: int, y: int) -> tuple[int, ...]:
    return (u, v, w, x, y, y, x, w, v, u + delta)


def R1(delta: int, u: int, v: int, w: int, x: int, y: int) -> tuple[int, ...]:
    return (u, y, v, x, w, w, x, v, y, u + delta)


def R2(delta: int, u: int, v: int, w: int, x: int, y: int) -> tuple[int, ...]:
    return (u, w, y, x, v, v, x, y, w, u + delta)


def canon_cycle(cycle: list[tuple[int, ...]]) -> tuple[tuple[int, ...], ...]:
    rots = [tuple(cycle[i:] + cycle[:i]) for i in range(len(cycle))]
    return min(rots)


def exact_params(delta: int, d_max: int) -> list[tuple[int, int, int, int, int, int, tuple[tuple[int, ...], ...]]]:
    seen: set[tuple[tuple[int, ...], ...]] = set()
    out: list[tuple[int, int, int, int, int, int, tuple[tuple[int, ...], ...]]] = []
    for d in range(3, d_max + 1, 2):
        if d < delta or (d - delta) % 2 != 0:
            continue
        total = (d - delta) // 2
        for u, v, w, x, y in compositions(total, 5):
            r0 = R0(delta, u, v, w, x, y)
            r1 = R1(delta, u, v, w, x, y)
            r2 = R2(delta, u, v, w, x, y)
            if step(r0) == r1 and step(r1) == r2 and step(r2) == r0 and len({r0, r1, r2}) == 3:
                cyc = canon_cycle([r0, r1, r2])
                if cyc not in seen:
                    seen.add(cyc)
                    out.append((delta, u, v, w, x, y, cyc))
    return out


def lift_ok(delta: int, u: int, v: int, w: int, x: int, y: int) -> bool:
    s0 = R0(delta + 2, u, v + 2, w + 2, x + 2, y + 2)
    s1 = R1(delta + 2, u, v + 2, w + 2, x + 2, y + 2)
    s2 = R2(delta + 2, u, v + 2, w + 2, x + 2, y + 2)
    return step(s0) == s1 and step(s1) == s2 and step(s2) == s0 and len({s0, s1, s2}) == 3


def lower_ok(delta: int, u: int, v: int, w: int, x: int, y: int) -> bool:
    if delta < 3 or min(v, w, x, y) < 2:
        return False
    s0 = R0(delta - 2, u, v - 2, w - 2, x - 2, y - 2)
    s1 = R1(delta - 2, u, v - 2, w - 2, x - 2, y - 2)
    s2 = R2(delta - 2, u, v - 2, w - 2, x - 2, y - 2)
    return step(s0) == s1 and step(s1) == s2 and step(s2) == s0 and len({s0, s1, s2}) == 3


def verify_lift(delta: int, d_max: int) -> dict[str, object]:
    rows = exact_params(delta, d_max)
    bad = []
    by_dim = defaultdict(int)
    for _, u, v, w, x, y, cyc in rows:
        d = sum(cyc[0])
        by_dim[d] += 1
        if not lift_ok(delta, u, v, w, x, y):
            bad.append({"delta": delta, "params": [u, v, w, x, y], "d": d})
            break
    return {
        "checked": len(rows),
        "bad_count": len(bad),
        "bad_examples": bad[:5],
        "by_dim": dict(sorted(by_dim.items())),
    }


def verify_lower(delta: int, d_max: int) -> dict[str, object]:
    rows = exact_params(delta, d_max)
    lowerable = []
    bad = []
    for _, u, v, w, x, y, _ in rows:
        if min(v, w, x, y) >= 2:
            lowerable.append((u, v, w, x, y))
            if not lower_ok(delta, u, v, w, x, y):
                bad.append({"delta": delta, "params": [u, v, w, x, y]})
                break
    return {
        "checked": len(rows),
        "lowerable": len(lowerable),
        "bad_count": len(bad),
        "bad_examples": bad[:5],
    }


def main() -> None:
    payload = {
        "lift_delta1_to_3": verify_lift(1, 35),
        "lift_delta3_to_5": verify_lift(3, 55),
        "lower_delta3_to_1": verify_lower(3, 55),
        "lower_delta5_to_3": verify_lower(5, 65),
        "base_family": {
            "delta_formula": "odd delta >= 1",
            "params": "(u,v,w,x,y)=(1,delta+1,delta+1,delta,delta+2)",
            "dimension": "d = 9*delta + 10",
        },
    }
    OUT_JSON.write_text(json.dumps(payload, indent=2))
    print(f"JSON: {OUT_JSON}")
    for k, v in payload.items():
        print(k, v)


if __name__ == "__main__":
    main()
