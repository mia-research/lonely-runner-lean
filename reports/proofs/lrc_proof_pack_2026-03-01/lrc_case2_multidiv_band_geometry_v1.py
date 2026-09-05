#!/usr/bin/env python3
"""
Gap-2 helper: analyze multi-divisible B_div geometry and candidate band intersections.

For a one-parameter family E = E_fixed U {M} U E_div with |E_div|>=2,
this script computes exact B_div components (by fiber scan over b in [0,L-1]) and
reports intersections with generalized low/high candidate bands:
  I_lo_base = [ceil(L/n), floor(L/e_max)-1]
  I_hi_base = [ceil(L - L/e_max), floor((n-1)L/n)]

Outputs:
- summary CSV (one row per M)
- components CSV (one row per component per M)
"""

from __future__ import annotations

import argparse
import csv
from dataclasses import dataclass
from math import gcd
from pathlib import Path
from typing import Iterable, List, Sequence, Tuple


def parse_int_list(s: str) -> List[int]:
    vals = [int(x.strip()) for x in s.split(",") if x.strip()]
    return vals


def lcm2(a: int, b: int) -> int:
    return a * b // gcd(a, b)


def lcm_list(vals: Iterable[int]) -> int:
    r = 1
    for v in vals:
        r = lcm2(r, int(v))
    return r


def ceil_div(a: int, b: int) -> int:
    return -(-a // b)


def interval_len(lo: int, hi: int) -> int:
    return max(0, hi - lo + 1)


def intersect_len(a0: int, a1: int, b0: int, b1: int) -> int:
    lo = max(a0, b0)
    hi = min(a1, b1)
    return interval_len(lo, hi)


@dataclass
class Component:
    lo: int
    hi: int

    @property
    def length(self) -> int:
        return self.hi - self.lo + 1


def build_components(bits: Sequence[bool]) -> List[Component]:
    comps: List[Component] = []
    n = len(bits)
    i = 0
    while i < n:
        if not bits[i]:
            i += 1
            continue
        j = i
        while j + 1 < n and bits[j + 1]:
            j += 1
        comps.append(Component(i, j))
        i = j + 1
    return comps


def b_div_membership(n: int, L: int, e_div: Sequence[int]) -> List[bool]:
    """Exact B_div indicator over b in [0,L-1].

    Divisible-speed condition for e=n*f:
      L <= (e*(aL+b) mod nL) <= (n-1)L  (independent of a)
    equivalently
      L/n <= (f*b mod L) <= (n-1)L/n.
    """
    lo = L // n
    hi = (n - 1) * L // n

    f_vals = []
    for e in e_div:
        if e % n != 0:
            raise ValueError(f"e_div value {e} is not divisible by n={n}")
        f_vals.append(e // n)

    ok = [False] * L
    for b in range(L):
        good = True
        for f in f_vals:
            x = (f * b) % L
            if not (lo <= x <= hi):
                good = False
                break
        ok[b] = good
    return ok


def run_one(n: int, fixed: Sequence[int], e_div: Sequence[int], M: int) -> Tuple[dict, List[dict]]:
    if len(e_div) < 2:
        raise ValueError("Gap-2 geometry expects |E_div|>=2")

    L = lcm_list(list(fixed) + [M] + list(e_div))
    e_max = max(fixed)
    L0 = lcm_list(list(fixed) + list(e_div))

    bits = b_div_membership(n, L, e_div)
    comps = build_components(bits)
    b_div_count = sum(c.length for c in comps)

    lo_base_lo = ceil_div(L, n)
    lo_base_hi = (L // e_max) - 1

    hi_base_lo = ceil_div((e_max - 1) * L, e_max)
    hi_base_hi = ((n - 1) * L) // n

    lo_total = 0
    hi_total = 0
    lo_comp_hits = 0
    hi_comp_hits = 0
    zeta = 0

    comp_rows: List[dict] = []

    for idx, c in enumerate(comps):
        lo_len = intersect_len(c.lo, c.hi, lo_base_lo, lo_base_hi)
        hi_len = intersect_len(c.lo, c.hi, hi_base_lo, hi_base_hi)

        if lo_len > 0:
            lo_comp_hits += 1
        if hi_len > 0:
            hi_comp_hits += 1

        lo_total += lo_len
        hi_total += hi_len

        # Exceptional fibers for one-parameter floor blocks: L0 | b.
        z0 = 0
        if lo_len > 0:
            lo_i = max(c.lo, lo_base_lo)
            hi_i = min(c.hi, lo_base_hi)
            z0 += hi_i // L0 - (lo_i - 1) // L0
        if hi_len > 0:
            lo_i = max(c.lo, hi_base_lo)
            hi_i = min(c.hi, hi_base_hi)
            z0 += hi_i // L0 - (lo_i - 1) // L0
        zeta += z0

        comp_rows.append(
            {
                "n": n,
                "M": M,
                "L": L,
                "component_idx": idx,
                "comp_lo": c.lo,
                "comp_hi": c.hi,
                "comp_len": c.length,
                "intersects_lo": int(lo_len > 0),
                "lo_intersection_len": lo_len,
                "intersects_hi": int(hi_len > 0),
                "hi_intersection_len": hi_len,
            }
        )

    summary = {
        "n": n,
        "M": M,
        "L": L,
        "L0": L0,
        "e_max": e_max,
        "E_div": "(" + ",".join(map(str, e_div)) + ")",
        "B_div_count": b_div_count,
        "B_div_components": len(comps),
        "min_component_len": min((c.length for c in comps), default=0),
        "max_component_len": max((c.length for c in comps), default=0),
        "lo_base_lo": lo_base_lo,
        "lo_base_hi": lo_base_hi,
        "hi_base_lo": hi_base_lo,
        "hi_base_hi": hi_base_hi,
        "lo_component_hits": lo_comp_hits,
        "lo_total_len": lo_total,
        "hi_component_hits": hi_comp_hits,
        "hi_total_len": hi_total,
        "zeta_candidates": zeta,
    }

    return summary, comp_rows


def write_csv(path: Path, rows: List[dict]) -> None:
    if not rows:
        return
    with path.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=list(rows[0].keys()))
        w.writeheader()
        w.writerows(rows)


def main() -> None:
    ap = argparse.ArgumentParser(description="Analyze multi-divisible B_div component geometry")
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--fixed", type=str, required=True, help="comma list of fixed non-divisible speeds")
    ap.add_argument("--e-div", type=str, required=True, help="comma list of divisible speeds (each multiple of n)")
    ap.add_argument("--m-list", type=str, default="", help="explicit comma list of M values")
    ap.add_argument("--m-max", type=int, default=0, help="if m-list empty, use admissible M in [1,m-max]")
    ap.add_argument("--tag", type=str, default="multidiv_v1")
    ap.add_argument("--out-dir", type=str, default=".")
    args = ap.parse_args()

    n = args.n
    fixed = parse_int_list(args.fixed)
    e_div = parse_int_list(args.e_div)

    if not fixed:
        raise ValueError("fixed must be nonempty")
    if len(e_div) < 2:
        raise ValueError("e-div must contain at least two divisible speeds")

    L0 = lcm_list(fixed + e_div)
    R = n * L0

    if args.m_list:
        M_values = parse_int_list(args.m_list)
    else:
        if args.m_max <= 0:
            raise ValueError("provide --m-list or positive --m-max")
        M_values = [m for m in range(1, args.m_max + 1) if gcd(m, R) == 1]

    summaries: List[dict] = []
    all_components: List[dict] = []

    print(f"[setup] n={n} fixed={fixed} e_div={e_div} L0={L0} R={R} M_count={len(M_values)}")

    for i, M in enumerate(M_values, start=1):
        s, comps = run_one(n, fixed, e_div, M)
        summaries.append(s)
        all_components.extend(comps)
        print(
            f"  [{i}/{len(M_values)}] M={M} L={s['L']} B_div={s['B_div_count']} "
            f"comps={s['B_div_components']} lo_total={s['lo_total_len']} hi_total={s['hi_total_len']}"
        )

    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    summary_csv = out_dir / f"lrc_case2_multidiv_band_geometry_summary_{args.tag}.csv"
    components_csv = out_dir / f"lrc_case2_multidiv_band_geometry_components_{args.tag}.csv"

    write_csv(summary_csv, summaries)
    write_csv(components_csv, all_components)

    print("\n[done]")
    print(f"summary:    {summary_csv}")
    print(f"components: {components_csv}")


if __name__ == "__main__":
    main()
