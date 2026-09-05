#!/usr/bin/env python3
"""
Audit the stronger odd period-3 asymmetry profile:

    A(C) = (delta, 0, 0, 0, 0)

for all currently exposed odd period-3 sectors.

This sharpens the earlier "phasewise asymmetry constancy" audit by recording
that the only observed phasewise asymmetry is the outer odd defect itself.
"""

from __future__ import annotations

import json
import random
from collections import Counter
from pathlib import Path


ROOT = Path("/Users/trentpalelei/Desktop/Math Ex/kaprekar_work")
REDUCED_JSON = ROOT / "kaprekar_odd_cycle_census_2026-04-26.json"
OUT_JSON = ROOT / "kaprekar_odd_period3_asymmetry_profile_audit_2026-05-27.json"


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


def asym(cnt: tuple[int, ...] | list[int]) -> tuple[int, int, int, int, int]:
    c = tuple(cnt)
    return (c[9] - c[0], c[8] - c[1], c[7] - c[2], c[6] - c[3], c[5] - c[4])


def profile_ok(cycle: list[tuple[int, ...]]) -> tuple[bool, list[list[int]]]:
    vals = [list(asym(c)) for c in cycle]
    target = vals[0][0]
    ok = all(v == [target, 0, 0, 0, 0] for v in vals)
    return ok, vals


def reduced_exact_check() -> dict[str, object]:
    obj = json.loads(REDUCED_JSON.read_text())
    rows = []
    bad = []
    for row in obj["rows"]:
        d = row["d"]
        if d not in (23, 25, 27, 29):
            continue
        p3 = [tuple(att["cycle0"]) for att in row["attractors"] if att["period"] == 3]
        ok_count = 0
        delta_hist = Counter()
        for c0 in p3:
            cyc = [c0, step(c0), step(step(c0))]
            ok, vals = profile_ok(cyc)
            if ok:
                delta_hist[vals[0][0]] += 1
                ok_count += 1
            else:
                bad.append({"d": d, "cycle0": list(c0), "asymmetries": vals})
        rows.append(
            {
                "d": d,
                "period3_count": len(p3),
                "ok_count": ok_count,
                "delta_histogram": dict(sorted(delta_hist.items())),
            }
        )
    return {"rows": rows, "bad_count": len(bad), "bad_examples": bad[:10]}


def boundary_tail_check(r_min: int, r_max: int) -> dict[str, object]:
    bad = []
    delta_hist = Counter()
    for r in range(r_min, r_max + 1):
        cyc = [
            (1, r, 4, 4, 4, 4, 4, 4, r, 4),
            (1, 4, r, 4, 4, 4, 4, r, 4, 4),
            (1, 4, 4, 4, r, r, 4, 4, 4, 4),
        ]
        ok, vals = profile_ok(cyc)
        if ok:
            delta_hist[vals[0][0]] += 1
        else:
            bad.append({"r": r, "asymmetries": vals})
            break
    return {
        "checked": r_max - r_min + 1,
        "delta_histogram": dict(sorted(delta_hist.items())),
        "bad_count": len(bad),
        "bad_examples": bad[:5],
    }


def sampled_global_check() -> dict[str, object]:
    dims = [19, 21, 23, 25, 27, 29, 31, 33, 39, 45, 55]
    rows = []
    bad = []
    for i, d in enumerate(dims):
        rng = random.Random(20260527 + i)
        seen_period3: set[tuple[tuple[int, ...], ...]] = set()
        delta_hist = Counter()
        asym_set = set()
        for _ in range(5000):
            s = random_composition(d, 10, rng)
            period, cyc = attractor_from_state(s)
            if period == 3 and cyc not in seen_period3:
                seen_period3.add(cyc)
                ok, vals = profile_ok(list(cyc))
                if ok:
                    delta_hist[vals[0][0]] += 1
                    asym_set.add(tuple(vals[0]))
                else:
                    if len(bad) < 10:
                        bad.append({"d": d, "cycle0": list(cyc[0]), "asymmetries": vals})
        rows.append(
            {
                "d": d,
                "distinct_period3_seen": len(seen_period3),
                "delta_histogram": dict(sorted(delta_hist.items())),
                "asymmetry_values": [list(v) for v in sorted(asym_set)],
            }
        )
    return {"rows": rows, "bad_count": len(bad), "bad_examples": bad}


def main() -> None:
    payload = {
        "profile_statement": "A(C) = (delta,0,0,0,0) phasewise on odd period-3 attractors",
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
