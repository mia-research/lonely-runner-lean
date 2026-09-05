#!/usr/bin/env python3
"""
Sample audit of the full odd count-state universe.

Purpose:
  give a disciplined non-exhaustive audit of the current sharp claim:
      every odd period-3 attractor is affine-delta

This does not prove the claim, but it checks for counterexamples outside the
reduced sector and explicit boundary thread.
"""

from __future__ import annotations

import json
import random
from collections import Counter, defaultdict
from pathlib import Path


ROOT = Path("/Users/trentpalelei/Desktop/Math Ex/kaprekar_work")
OUT_JSON = ROOT / "kaprekar_global_odd_period3_sample_audit_2026-05-20.json"


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
    # Uniform stars-and-bars composition.
    cuts = sorted(rng.sample(range(n + k - 1), k - 1))
    pts = [-1] + cuts + [n + k - 1]
    parts = []
    for a, b in zip(pts, pts[1:]):
        parts.append(b - a - 1)
    return tuple(parts)


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


def audit_dimension(d: int, n_samples: int, seed: int) -> dict[str, object]:
    rng = random.Random(seed)
    observed_period3: set[tuple[tuple[int, ...], ...]] = set()
    bad_period3: list[dict[str, object]] = []
    period_hist = Counter()
    delta_hist = Counter()
    imbalance_hist = Counter()
    examples_by_delta: dict[int, list[list[int]]] = defaultdict(list)

    for _ in range(n_samples):
        s = random_composition(d, 10, rng)
        period, cyc = attractor_from_state(s)
        period_hist[period] += 1
        if period == 3 and cyc not in observed_period3:
            observed_period3.add(cyc)
            fits = [affine_delta_fit(state) for state in cyc]
            if any(fit is None for fit in fits):
                bad_period3.append({"cycle": [list(x) for x in cyc], "fits": fits})
            else:
                delta = fits[0]["delta"]
                delta_hist[delta] += 1
                imbalance_hist[sum(cyc[0][5:]) - sum(cyc[0][:5])] += 1
                if len(examples_by_delta[delta]) < 5:
                    examples_by_delta[delta].append(list(cyc[0]))

    return {
        "d": d,
        "samples": n_samples,
        "period_histogram": dict(sorted(period_hist.items())),
        "distinct_period3_seen": len(observed_period3),
        "bad_period3_count": len(bad_period3),
        "bad_period3_examples": bad_period3[:10],
        "delta_histogram": dict(sorted(delta_hist.items())),
        "imbalance_histogram": dict(sorted(imbalance_hist.items())),
        "examples_by_delta": {str(k): v for k, v in sorted(examples_by_delta.items())},
    }


def main() -> None:
    dims = [19, 21, 23, 25, 27, 29, 31, 33, 39, 45, 55]
    rows = []
    for i, d in enumerate(dims):
        rows.append(audit_dimension(d, n_samples=5000, seed=20260520 + i))
    payload = {"dims": dims, "rows": rows}
    OUT_JSON.write_text(json.dumps(payload, indent=2))
    print(f"JSON: {OUT_JSON}")
    for row in rows:
        print(
            f"d={row['d']} samples={row['samples']} p3={row['distinct_period3_seen']} bad={row['bad_period3_count']} deltas={row['delta_histogram']}"
        )


if __name__ == "__main__":
    main()
