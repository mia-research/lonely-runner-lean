#!/usr/bin/env python3
"""
M2-drop verifier v1

Outputs per-template pass/fail on structured subclaims:
- SC0: in Case-iiib scope
- SC1: exists any uncovered residue (M2 existence)
- SC2: exists uncovered residue in dropped support Cover_drop (M2-drop)
- SC3: quantitative bound best_miss >= 1/(e_max*(e_max-1))
- SC4: best miss interval is interior (no boundary touch)
- SC5: integer witness at M=1 exists on best dropped-support residue

Note: SC3-5 are supportive; theorem load-bearing is SC2.
"""

from __future__ import annotations

import argparse
import csv
from dataclasses import dataclass
from fractions import Fraction
from functools import reduce
from itertools import combinations
from math import gcd, lcm
from pathlib import Path
from typing import Iterable, List, Sequence, Tuple


def ext_gcd(a: int, b: int) -> Tuple[int, int, int]:
    if a == 0:
        return b, 0, 1
    g, x, y = ext_gcd(b % a, a)
    return g, y - (b // a) * x, x


def modinv(a: int, n: int) -> int | None:
    g, x, _ = ext_gcd(a % n, n)
    if g != 1:
        return None
    return x % n


def bad_set(e: int, t: int, n: int) -> set[int]:
    g = gcd(e, n)
    n1 = n // g
    e1 = e // g
    inv = modinv(e1, n1)
    if inv is None:
        return set()
    out: set[int] = set()
    for rr in ((-t) % n, (-(t + 1)) % n):
        if rr % g != 0:
            continue
        a0 = ((rr // g) * inv) % n1
        for k in range(g):
            out.add((a0 + k * n1) % n)
    return out


def merge_intervals(intervals: Sequence[Tuple[Fraction, Fraction]]) -> List[Tuple[Fraction, Fraction]]:
    xs = sorted((a, b) for a, b in intervals if a < b)
    out: List[List[Fraction]] = []
    for a, b in xs:
        if not out or a > out[-1][1]:
            out.append([a, b])
        elif b > out[-1][1]:
            out[-1][1] = b
    return [(a, b) for a, b in out]


def interval_complement(base: Tuple[Fraction, Fraction], merged: Sequence[Tuple[Fraction, Fraction]]) -> List[Tuple[Fraction, Fraction]]:
    lo, hi = base
    cur = lo
    out: List[Tuple[Fraction, Fraction]] = []
    for a, b in merged:
        aa = max(a, lo)
        bb = min(b, hi)
        if bb <= aa:
            continue
        if cur < aa:
            out.append((cur, aa))
        if bb > cur:
            cur = bb
    if cur < hi:
        out.append((cur, hi))
    return out


def lcm_list(vals: Iterable[int]) -> int:
    return reduce(lcm, vals, 1)


def count_integer_points(L: int, a: Fraction, b: Fraction) -> int:
    lo = (a.numerator * L + a.denominator - 1) // a.denominator
    hi = ((b.numerator * L + b.denominator - 1) // b.denominator) - 1
    return max(0, hi - lo + 1)


def cover_support(e: int, n: int) -> set[int]:
    s: set[int] = set()
    for t in range(e):
        s |= bad_set(e, t, n)
    return s


def is_composite(n: int) -> bool:
    if n < 4:
        return False
    for p in range(2, int(n**0.5) + 1):
        if n % p == 0:
            return True
    return False


@dataclass
class Row:
    n: int
    dropped_a: int
    dropped_b: int
    e_max: int
    G_tot: int
    thresh: int
    sc0_case_iiib: int
    sc1_exists_any_miss: int
    sc2_exists_miss_cover_drop: int
    sc3_bound_best: int
    sc4_best_interior: int
    sc5_integer_witness_m1: int
    best_r_any: int
    best_miss_any: Fraction
    best_r_drop: int
    best_miss_drop: Fraction


def analyze_template(n: int, dropped: Tuple[int, int]) -> Row:
    a, b = dropped
    E_fix = [e for e in range(1, n) if e not in dropped]
    e_max = max(E_fix)

    E_nu = [e for e in E_fix if gcd(e, n) > 1]
    G_tot = sum(gcd(e, n) for e in E_nu)
    thresh = 1 + 2 * len(E_nu)

    sc0 = 0
    if G_tot > thresh and 1 in E_fix and (n - 1) in E_fix:
        U0: set[int] = set()
        for e in E_fix:
            U0 |= bad_set(e, 0, n)
        if len(U0) == n:
            sc0 = 1

    I_div = (Fraction(1, n), Fraction(n - 1, n))

    # Residue supports for dropped runners
    cover_drop = cover_support(a, n) | cover_support(b, n)

    best_r_any = -1
    best_m_any = Fraction(-1, 1)
    best_miss_any: List[Tuple[Fraction, Fraction]] = []

    best_r_drop = -1
    best_m_drop = Fraction(-1, 1)
    best_miss_drop: List[Tuple[Fraction, Fraction]] = []

    exists_any_miss = 0
    exists_drop_miss = 0

    for r in range(n):
        cov: List[Tuple[Fraction, Fraction]] = []
        for e in E_fix:
            for t in range(e):
                if r in bad_set(e, t, n):
                    x0, x1 = Fraction(t, e), Fraction(t + 1, e)
                    a0, b0 = max(x0, I_div[0]), min(x1, I_div[1])
                    if a0 < b0:
                        cov.append((a0, b0))
        miss = interval_complement(I_div, merge_intervals(cov))
        m = sum((q - p) for p, q in miss)

        if m > best_m_any:
            best_m_any = m
            best_r_any = r
            best_miss_any = miss

        if r in cover_drop and m > best_m_drop:
            best_m_drop = m
            best_r_drop = r
            best_miss_drop = miss

        if m > 0:
            exists_any_miss = 1
            if r in cover_drop:
                exists_drop_miss = 1

    bound = Fraction(1, e_max * (e_max - 1))
    sc3 = int(best_m_any >= bound)

    sc4 = 0
    if best_miss_any:
        touches = any(x == I_div[0] or y == I_div[1] for x, y in best_miss_any)
        sc4 = int(not touches)

    L0 = lcm_list(E_fix + [n])
    sc5 = 0
    if best_miss_drop:
        if max(count_integer_points(L0, x, y) for x, y in best_miss_drop) > 0:
            sc5 = 1

    return Row(
        n=n,
        dropped_a=a,
        dropped_b=b,
        e_max=e_max,
        G_tot=G_tot,
        thresh=thresh,
        sc0_case_iiib=sc0,
        sc1_exists_any_miss=exists_any_miss,
        sc2_exists_miss_cover_drop=exists_drop_miss,
        sc3_bound_best=sc3,
        sc4_best_interior=sc4,
        sc5_integer_witness_m1=sc5,
        best_r_any=best_r_any,
        best_miss_any=best_m_any,
        best_r_drop=best_r_drop,
        best_miss_drop=best_m_drop,
    )


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--n-min", type=int, default=10)
    ap.add_argument("--n-max", type=int, default=40)
    ap.add_argument("--out-csv", type=Path, default=Path("/tmp/lrc_m2_drop_verifier_rows_v1.csv"))
    ap.add_argument("--out-summary", type=Path, default=Path("/tmp/lrc_m2_drop_verifier_summary_v1.md"))
    args = ap.parse_args()

    all_rows: List[Row] = []
    for n in range(args.n_min, args.n_max + 1):
        if not is_composite(n):
            continue
        for d in combinations(range(1, n), 2):
            all_rows.append(analyze_template(n, d))

    case_iiib = [r for r in all_rows if r.sc0_case_iiib == 1]

    args.out_csv.parent.mkdir(parents=True, exist_ok=True)
    with args.out_csv.open("w", newline="") as f:
        w = csv.writer(f)
        w.writerow([
            "n", "dropped_a", "dropped_b", "e_max", "G_tot", "thresh",
            "sc0_case_iiib", "sc1_exists_any_miss", "sc2_exists_miss_cover_drop",
            "sc3_bound_best", "sc4_best_interior", "sc5_integer_witness_m1",
            "best_r_any", "best_miss_any", "best_r_drop", "best_miss_drop",
        ])
        for r in case_iiib:
            w.writerow([
                r.n, r.dropped_a, r.dropped_b, r.e_max, r.G_tot, r.thresh,
                r.sc0_case_iiib, r.sc1_exists_any_miss, r.sc2_exists_miss_cover_drop,
                r.sc3_bound_best, r.sc4_best_interior, r.sc5_integer_witness_m1,
                r.best_r_any, f"{r.best_miss_any.numerator}/{r.best_miss_any.denominator}",
                r.best_r_drop, f"{r.best_miss_drop.numerator}/{r.best_miss_drop.denominator}",
            ])

    def fail_count(field: str) -> int:
        return sum(1 for r in case_iiib if getattr(r, field) == 0)

    lines: List[str] = []
    lines.append("# M2-drop Verifier Summary (v1)")
    lines.append("")
    lines.append(f"Range: composite n in [{args.n_min}, {args.n_max}]")
    lines.append(f"Case-iiib templates: {len(case_iiib)}")
    lines.append("")
    lines.append("## Subclaim pass/fail")
    lines.append("")
    lines.append(f"- SC1 exists any miss residue: fails={fail_count('sc1_exists_any_miss')}")
    lines.append(f"- SC2 exists miss in Cover_drop (M2-drop core): fails={fail_count('sc2_exists_miss_cover_drop')}")
    lines.append(f"- SC3 quantitative bound on best miss: fails={fail_count('sc3_bound_best')}")
    lines.append(f"- SC4 best miss interior: fails={fail_count('sc4_best_interior')}")
    lines.append(f"- SC5 integer witness at M=1: fails={fail_count('sc5_integer_witness_m1')}")
    lines.append("")

    by_n: dict[int, List[Row]] = {}
    for r in case_iiib:
        by_n.setdefault(r.n, []).append(r)

    lines.append("## Per-n SC2 status")
    lines.append("")
    lines.append("| n | templates | SC2 fails |")
    lines.append("|---:|---:|---:|")
    for n in sorted(by_n):
        rr = by_n[n]
        fails = sum(1 for r in rr if r.sc2_exists_miss_cover_drop == 0)
        lines.append(f"| {n} | {len(rr)} | {fails} |")

    args.out_summary.parent.mkdir(parents=True, exist_ok=True)
    args.out_summary.write_text("\n".join(lines) + "\n")

    print(f"wrote csv: {args.out_csv}")
    print(f"wrote summary: {args.out_summary}")


if __name__ == "__main__":
    main()
