#!/usr/bin/env python3
"""
Exact odd-side cycle extension families in base 10.

Families:
  A_m : period-5, dimensions d = 11 + 2m
  B_m : period-2, dimensions d = 13 + 2m
  C_m : period-5, dimensions d = 13 + 2m
  D_m : period-5, dimensions d = 13 + 2m

All four families are preserved by the same shell lift +2_36.

Also checks the unstable period-8 family T_m obtained by lifting the d=11
period-8 orbit: for m >= 1 it falls into B_{m-1} in bounded phase-dependent
time.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path


TMP_JSON = Path("/tmp/kaprekar_odd_cycle_extension_families_2026-04-24.json")


def A_states(m: int) -> list[list[int]]:
    return [
        [0, 2, 0, m + 2, 1, 1, m + 2, 1, 0, 2],
        [0, 2, 1, m + 1, 1, 1, m + 1, 1, 2, 1],
        [0, 1, 2, m + 1, 1, 1, m + 1, 2, 1, 1],
        [0, 1, 1, m + 1, 2, 2, m + 1, 1, 1, 1],
        [1, 0, 2, m + 1, 1, 1, m + 1, 1, 2, 1],
    ]


def B_states(m: int) -> list[list[int]]:
    return [
        [0, 1, 1, m + 2, 2, 2, m + 3, 0, 0, 2],
        [1, 0, 3, m + 2, 0, 0, m + 2, 2, 2, 1],
    ]


def C_states(m: int) -> list[list[int]]:
    return [
        [0, 1, 2, m + 1, 2, 2, m + 1, 2, 1, 1],
        [1, 0, 2, m + 1, 2, 2, m + 1, 1, 2, 1],
        [1, 1, 1, m + 2, 1, 1, m + 2, 1, 1, 2],
        [0, 3, 0, m + 2, 1, 1, m + 2, 1, 1, 2],
        [0, 2, 2, m + 1, 1, 1, m + 1, 2, 2, 1],
    ]


def D_states(m: int) -> list[list[int]]:
    return [
        [0, 2, 1, m + 1, 2, 2, m + 1, 1, 2, 1],
        [1, 0, 3, m + 1, 1, 1, m + 1, 2, 2, 1],
        [0, 2, 0, m + 2, 2, 2, m + 2, 1, 0, 2],
        [1, 1, 2, m + 1, 1, 1, m + 1, 1, 3, 1],
        [0, 2, 1, m + 2, 1, 1, m + 2, 2, 0, 2],
    ]


BASE_T8: list[list[int]] = [
    [0, 1, 1, 2, 1, 1, 3, 0, 0, 2],
    [0, 1, 2, 2, 0, 0, 2, 2, 1, 1],
    [0, 0, 2, 1, 2, 2, 2, 0, 1, 1],
    [1, 0, 1, 3, 0, 0, 2, 2, 1, 1],
    [0, 1, 1, 1, 2, 2, 2, 0, 0, 2],
    [1, 0, 3, 1, 0, 0, 1, 2, 2, 1],
    [0, 1, 0, 3, 1, 2, 2, 0, 0, 2],
    [1, 0, 1, 3, 0, 0, 3, 0, 2, 1],
]


def T_states(m: int) -> list[list[int]]:
    out: list[list[int]] = []
    for s in BASE_T8:
        t = s.copy()
        t[3] += m
        t[6] += m
        out.append(t)
    return out


def number_from_counts(cnt: list[int]) -> int:
    desc = "".join(str(d) * cnt[d] for d in range(9, -1, -1))
    asc = "".join(str(d) * cnt[d] for d in range(10))
    return int(desc) - int(asc)


def counts_of_number(n: int, d: int) -> list[int]:
    c = Counter(map(int, str(n).zfill(d)))
    return [c[i] for i in range(10)]


def shell_gap_profile(cnt: list[int]) -> list[int]:
    desc: list[int] = []
    for d in range(9, -1, -1):
        desc.extend([d] * cnt[d])
    asc = list(reversed(desc))
    g = [a - b for a, b in zip(desc, asc)]
    return g[: (len(desc) + 1) // 2]


def verify_cycle_family(fn, m_max: int) -> dict[str, object]:
    checked = 0
    failures = 0
    samples: list[dict[str, object]] = []
    for m in range(0, m_max + 1):
        states = fn(m)
        d = sum(states[0])
        ok = True
        for i, s in enumerate(states):
            n = number_from_counts(s)
            nxt = counts_of_number(n, d)
            if nxt != states[(i + 1) % len(states)]:
                ok = False
                failures += 1
                break
        checked += 1
        if len(samples) < 6 and ok:
            samples.append(
                {
                    "m": m,
                    "d": d,
                    "numbers": [number_from_counts(s) for s in states],
                    "gap_profiles": [shell_gap_profile(s) for s in states],
                }
            )
    return {"checked": checked, "failures": failures, "samples": samples}


def verify_transient_to_B(m_max: int) -> dict[str, object]:
    checked = 0
    failures = 0
    hit_hist = Counter()
    samples: list[dict[str, object]] = []
    for m in range(1, m_max + 1):
        targets = {tuple(s) for s in B_states(m - 1)}
        for phase, s0 in enumerate(T_states(m)):
            checked += 1
            cur = s0
            hit = None
            for t in range(1, 16):
                cur = counts_of_number(number_from_counts(cur), sum(cur))
                if tuple(cur) in targets:
                    hit = t
                    break
            if hit is None:
                failures += 1
            else:
                hit_hist[hit] += 1
                if len(samples) < 8:
                    samples.append({"m": m, "phase": phase, "hit_step": hit, "landing": cur})
    return {
        "checked": checked,
        "failures": failures,
        "hit_histogram": dict(sorted(hit_hist.items())),
        "samples": samples,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description="Verify exact odd-side cycle extension families.")
    parser.add_argument("--m-max", type=int, default=20)
    parser.add_argument("--json-out", type=Path, default=TMP_JSON)
    args = parser.parse_args()

    payload = {
        "A_period5": verify_cycle_family(A_states, args.m_max),
        "B_period2": verify_cycle_family(B_states, args.m_max),
        "C_period5": verify_cycle_family(C_states, args.m_max),
        "D_period5": verify_cycle_family(D_states, args.m_max),
        "T_to_B_reduction": verify_transient_to_B(args.m_max),
    }
    args.json_out.write_text(json.dumps(payload, indent=2))

    print(f"JSON: {args.json_out}")
    for key, row in payload.items():
        if key == "T_to_B_reduction":
            print(f"{key}: checked={row['checked']} failures={row['failures']} hit_hist={row['hit_histogram']}")
        else:
            print(f"{key}: checked={row['checked']} failures={row['failures']}")


if __name__ == "__main__":
    main()
