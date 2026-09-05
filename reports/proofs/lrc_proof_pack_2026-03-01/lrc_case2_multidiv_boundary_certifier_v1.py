#!/usr/bin/env python3
"""
Gap-2 prototype: exact multi-divisible boundary/event certifier.

Purpose
- Use multi-divisible B_div components from interval intersections (no per-b B_div scan).
- Compute exact x0 and B_safe by boundary/event aggregation over component cells.
- Emit a component-wise D.2-style lower-bound diagnostic per M.

This is a gap-closure engineering artifact, not a universal theorem claim.
"""

from __future__ import annotations

import argparse
import csv
from dataclasses import dataclass
from fractions import Fraction
from math import gcd
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple


# ---------- basic arithmetic ----------


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


def parse_int_list(s: str) -> List[int]:
    return [int(x.strip()) for x in s.split(",") if x.strip()]


# ---------- masks / class counting ----------


def precompute_runner_masks(n: int, e: int) -> List[List[int]]:
    """masks[t][z], t in 0..e-1, z in {0,1}, bit a=1 means a is bad for this runner."""
    masks = [[0, 0] for _ in range(e)]
    for t in range(e):
        for z in (0, 1):
            mask = 0
            for a in range(n):
                q = (e * a + t) % n
                bad = (q == 0) or (q == n - 1 and z == 0)
                if bad:
                    mask |= 1 << a
            masks[t][z] = mask
    return masks


def precompute_free_masks_mod(n: int, m_mod: int) -> List[List[int]]:
    masks = [[0, 0] for _ in range(n)]
    for r in range(n):
        for z in (0, 1):
            mask = 0
            for a in range(n):
                q = (m_mod * a + r) % n
                bad = (q == 0) or (q == n - 1 and z == 0)
                if bad:
                    mask |= 1 << a
            masks[r][z] = mask
    return masks


def residue_counts_interval(a: int, b: int, n: int) -> List[int]:
    out = [0] * n
    if a > b:
        return out
    for r in range(n):
        first = a + ((r - a) % n)
        if first <= b:
            out[r] = 1 + (b - first) // n
    return out


def count_free_classes_in_segment(lo: int, hi: int, L0: int, n: int) -> Tuple[List[int], List[int]]:
    """Count b in [lo,hi] by (t_M mod n, z_M), t_M=floor(b/L0), z_M=1[b mod L0==0]."""
    z0 = [0] * n
    z1 = [0] * n

    u0 = lo // L0
    u1 = hi // L0

    def add_block(u: int, length: int, z1_cnt: int) -> None:
        r = u % n
        z1[r] += z1_cnt
        z0[r] += length - z1_cnt

    if u0 == u1:
        length = hi - lo + 1
        z1_cnt = 1 if lo <= u0 * L0 <= hi else 0
        add_block(u0, length, z1_cnt)
        return z0, z1

    first_len = (u0 + 1) * L0 - lo
    first_z1 = 1 if lo == u0 * L0 else 0
    add_block(u0, first_len, first_z1)

    a = u0 + 1
    b = u1 - 1
    if a <= b:
        counts = residue_counts_interval(a, b, n)
        for r, c in enumerate(counts):
            if c:
                z1[r] += c
                z0[r] += c * (L0 - 1)

    last_len = hi - u1 * L0 + 1
    add_block(u1, last_len, 1)

    return z0, z1


# ---------- multi-divisible B_div geometry ----------


@dataclass
class Component:
    lo: int
    hi: int

    @property
    def length(self) -> int:
        return self.hi - self.lo + 1


def intervals_for_f(n: int, f: int) -> List[Tuple[Fraction, Fraction]]:
    """S_f = {x in [0,1): frac(fx) in [1/n, (n-1)/n]} as rational intervals."""
    out: List[Tuple[Fraction, Fraction]] = []
    fn = f * n
    for m in range(f):
        lo = Fraction(m * n + 1, fn)
        hi = Fraction(m * n + (n - 1), fn)
        out.append((lo, hi))
    return out


def merge_fraction_intervals(iv: List[Tuple[Fraction, Fraction]]) -> List[Tuple[Fraction, Fraction]]:
    if not iv:
        return []
    iv = sorted(iv, key=lambda t: (t[0], t[1]))
    out: List[Tuple[Fraction, Fraction]] = [iv[0]]
    for lo, hi in iv[1:]:
        plo, phi = out[-1]
        if lo <= phi:
            if hi > phi:
                out[-1] = (plo, hi)
        else:
            out.append((lo, hi))
    return out


def intersect_fraction_lists(
    a: List[Tuple[Fraction, Fraction]],
    b: List[Tuple[Fraction, Fraction]],
) -> List[Tuple[Fraction, Fraction]]:
    i = 0
    j = 0
    out: List[Tuple[Fraction, Fraction]] = []
    while i < len(a) and j < len(b):
        lo = max(a[i][0], b[j][0])
        hi = min(a[i][1], b[j][1])
        if lo <= hi:
            out.append((lo, hi))
        if a[i][1] < b[j][1]:
            i += 1
        else:
            j += 1
    return merge_fraction_intervals(out)


def divisible_feasible_intervals(n: int, e_div: Sequence[int]) -> List[Tuple[Fraction, Fraction]]:
    f_vals = []
    for e in e_div:
        if e % n != 0:
            raise ValueError(f"e_div value {e} is not divisible by n={n}")
        f_vals.append(e // n)

    if not f_vals:
        return []

    s = merge_fraction_intervals(intervals_for_f(n, f_vals[0]))
    for f in f_vals[1:]:
        s = intersect_fraction_lists(s, merge_fraction_intervals(intervals_for_f(n, f)))
        if not s:
            return []
    return s


def ceil_frac_times_int(x: Fraction, L: int) -> int:
    return ceil_div(x.numerator * L, x.denominator)


def floor_frac_times_int(x: Fraction, L: int) -> int:
    return (x.numerator * L) // x.denominator


def components_from_intervals(intervals: List[Tuple[Fraction, Fraction]], L: int) -> List[Component]:
    comps: List[Component] = []
    for lo_x, hi_x in intervals:
        lo = ceil_frac_times_int(lo_x, L)
        hi = floor_frac_times_int(hi_x, L)
        if lo <= hi:
            comps.append(Component(lo, hi))

    if not comps:
        return comps

    comps.sort(key=lambda c: (c.lo, c.hi))
    merged: List[Component] = [comps[0]]
    for c in comps[1:]:
        last = merged[-1]
        if c.lo <= last.hi + 1:
            merged[-1] = Component(last.lo, max(last.hi, c.hi))
        else:
            merged.append(c)
    return merged


def b_div_components(n: int, e_div: Sequence[int], L: int) -> List[Component]:
    x_int = divisible_feasible_intervals(n, e_div)
    return components_from_intervals(x_int, L)


def b_div_membership_scan(n: int, e_div: Sequence[int], L: int) -> List[bool]:
    """Validation kernel only."""
    lo = L // n
    hi = (n - 1) * L // n
    f_vals = [e // n for e in e_div]
    out = [False] * L
    for b in range(L):
        ok = True
        for f in f_vals:
            x = (f * b) % L
            if not (lo <= x <= hi):
                ok = False
                break
        out[b] = ok
    return out


def components_from_bits(bits: Sequence[bool]) -> List[Component]:
    comps: List[Component] = []
    i = 0
    n = len(bits)
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


# ---------- exact boundary/event x0 over component union ----------


def component_event_segments(L: int, comp: Component, fixed: List[int]) -> List[Tuple[int, int]]:
    boundaries = {comp.lo, comp.hi + 1}
    for e in fixed:
        for k in range(e + 1):
            x = (k * L) // e
            if comp.lo <= x <= comp.hi:
                boundaries.add(x)
            xp = x + 1
            if comp.lo <= xp <= comp.hi + 1:
                boundaries.add(xp)

    pts = sorted(boundaries)
    segs: List[Tuple[int, int]] = []
    for a, b in zip(pts, pts[1:]):
        lo = a
        hi = b - 1
        if lo <= hi:
            segs.append((lo, hi))
    return segs


def compute_exact_counts_multidiv(
    n: int,
    fixed: List[int],
    e_div: List[int],
    M: int,
    L0: int,
) -> Dict[str, int]:
    L = L0 * M
    comps = b_div_components(n, e_div, L)

    fixed_tables: Dict[int, List[List[int]]] = {e: precompute_runner_masks(n, e) for e in fixed}
    free_masks = precompute_free_masks_mod(n, M % n)

    x0 = 0
    B_safe = 0
    seg_count = 0

    for comp in comps:
        for lo, hi in component_event_segments(L, comp, fixed):
            seg_count += 1
            b = lo

            fixed_mask = 0
            for e in fixed:
                eb = e * b
                t = eb // L
                s = eb - t * L
                z = 1 if s == 0 else 0
                fixed_mask |= fixed_tables[e][t][z]

            c0, c1 = count_free_classes_in_segment(lo, hi, L0, n)
            for r in range(n):
                n0 = c0[r]
                if n0:
                    cover = fixed_mask | free_masks[r][0]
                    A_b = n - cover.bit_count()
                    x0 += n0 * A_b
                    if A_b > 0:
                        B_safe += n0

                n1 = c1[r]
                if n1:
                    cover = fixed_mask | free_masks[r][1]
                    A_b = n - cover.bit_count()
                    x0 += n1 * A_b
                    if A_b > 0:
                        B_safe += n1

    B_div = sum(c.length for c in comps)
    return {
        "x0": x0,
        "B_safe": B_safe,
        "B_div": B_div,
        "B_div_components": len(comps),
        "segment_count": seg_count,
    }


def compute_exact_counts_multidiv_bruteforce(
    n: int,
    fixed: List[int],
    e_div: List[int],
    M: int,
    L0: int,
) -> Dict[str, int]:
    """Validation kernel only."""
    L = L0 * M
    non_div = fixed + [M]
    tables = {e: precompute_runner_masks(n, e) for e in non_div}

    bits = b_div_membership_scan(n, e_div, L)

    x0 = 0
    B_safe = 0
    B_div = 0

    for b, ok_div in enumerate(bits):
        if not ok_div:
            continue
        B_div += 1
        union_mask = 0
        for e in non_div:
            eb = e * b
            t = eb // L
            s = eb - t * L
            z = 1 if s == 0 else 0
            union_mask |= tables[e][t][z]
        A_b = n - union_mask.bit_count()
        x0 += A_b
        if A_b > 0:
            B_safe += 1

    comps = components_from_bits(bits)
    return {
        "x0": x0,
        "B_safe": B_safe,
        "B_div": B_div,
        "B_div_components": len(comps),
    }


# ---------- component-wise D.2-style bound diagnostics ----------


def d2_component_bound(n: int, e_max: int, L: int, L0: int, comps: List[Component]) -> Dict[str, int | str]:
    lo_base_lo = ceil_div(L, n)
    lo_base_hi = (L // e_max) - 1

    hi_base_lo = ceil_div((e_max - 1) * L, e_max)
    hi_base_hi = ((n - 1) * L) // n

    lo_total = 0
    hi_total = 0
    lo_hits = 0
    hi_hits = 0
    zeta = 0

    for c in comps:
        lo_len = intersect_len(c.lo, c.hi, lo_base_lo, lo_base_hi)
        hi_len = intersect_len(c.lo, c.hi, hi_base_lo, hi_base_hi)

        if lo_len > 0:
            lo_hits += 1
            lo_i = max(c.lo, lo_base_lo)
            hi_i = min(c.hi, lo_base_hi)
            zeta += hi_i // L0 - (lo_i - 1) // L0

        if hi_len > 0:
            hi_hits += 1
            lo_i = max(c.lo, hi_base_lo)
            hi_i = min(c.hi, hi_base_hi)
            zeta += hi_i // L0 - (lo_i - 1) // L0

        lo_total += lo_len
        hi_total += hi_len

    # Per-interval D.1'-style cap aggregated over component-band intersections.
    # This is a diagnostic lower bound used for tracking, not asserted as a new theorem here.
    intervals = lo_hits + hi_hits
    frac = Fraction(n - 1, n) * Fraction(lo_total + hi_total, 1) - Fraction(2 * L0 * intervals + zeta, 1)
    lb_floor = frac.numerator // frac.denominator

    return {
        "lo_total_len": lo_total,
        "hi_total_len": hi_total,
        "lo_component_hits": lo_hits,
        "hi_component_hits": hi_hits,
        "zeta_candidates": zeta,
        "d2_lb_frac": str(frac),
        "d2_lb_floor": lb_floor,
    }


# ---------- driver ----------


@dataclass
class Row:
    n: int
    fixed: str
    e_div: str
    M: int
    L: int
    L0: int
    B_div: int
    B_div_components: int
    segment_count: int
    lo_total_len: int
    hi_total_len: int
    lo_component_hits: int
    hi_component_hits: int
    zeta_candidates: int
    d2_lb_floor: int
    B_safe: int
    x0: int
    phi_n: int
    ok_phi: int
    ok_d2_lb: int


def run_one(
    n: int,
    fixed: List[int],
    e_div: List[int],
    M: int,
    validate_bruteforce: bool,
) -> Row:
    L0 = lcm_list(fixed + e_div)
    L = L0 * M

    exact = compute_exact_counts_multidiv(n, fixed, e_div, M, L0)

    comps = b_div_components(n, e_div, L)
    bnd = d2_component_bound(n, max(fixed), L, L0, comps)

    if validate_bruteforce:
        ref = compute_exact_counts_multidiv_bruteforce(n, fixed, e_div, M, L0)
        keys = ["x0", "B_safe", "B_div", "B_div_components"]
        if any(exact[k] != ref[k] for k in keys):
            raise RuntimeError(
                f"mismatch at M={M}: exact={{{', '.join(f'{k}:{exact[k]}' for k in keys)}}} "
                f"ref={{{', '.join(f'{k}:{ref[k]}' for k in keys)}}}"
            )

    phi_n = sum(1 for j in range(1, n + 1) if gcd(j, n) == 1)

    return Row(
        n=n,
        fixed="(" + ",".join(map(str, fixed)) + ")",
        e_div="(" + ",".join(map(str, e_div)) + ")",
        M=M,
        L=L,
        L0=L0,
        B_div=exact["B_div"],
        B_div_components=exact["B_div_components"],
        segment_count=exact["segment_count"],
        lo_total_len=int(bnd["lo_total_len"]),
        hi_total_len=int(bnd["hi_total_len"]),
        lo_component_hits=int(bnd["lo_component_hits"]),
        hi_component_hits=int(bnd["hi_component_hits"]),
        zeta_candidates=int(bnd["zeta_candidates"]),
        d2_lb_floor=int(bnd["d2_lb_floor"]),
        B_safe=exact["B_safe"],
        x0=exact["x0"],
        phi_n=phi_n,
        ok_phi=int(exact["x0"] >= phi_n),
        ok_d2_lb=int(exact["B_safe"] >= int(bnd["d2_lb_floor"])),
    )


def write_outputs(out_dir: Path, tag: str, rows: List[Row]) -> Tuple[Path, Path]:
    rows_csv = out_dir / f"lrc_case2_multidiv_boundary_rows_{tag}.csv"
    summary_md = out_dir / f"lrc_case2_multidiv_boundary_summary_{tag}.md"

    with rows_csv.open("w", newline="", encoding="utf-8") as f:
        fieldnames = list(Row.__dataclass_fields__.keys())
        w = csv.DictWriter(f, fieldnames=fieldnames)
        w.writeheader()
        for r in rows:
            w.writerow(r.__dict__)

    xs = [r.x0 for r in rows]
    bs = [r.B_safe for r in rows]
    d2m = [r.B_safe - r.d2_lb_floor for r in rows]

    with summary_md.open("w", encoding="utf-8") as f:
        f.write("# Multi-Divisible Boundary Certifier Summary\n\n")
        if rows:
            head = rows[0]
            f.write(f"- n: {head.n}\n")
            f.write(f"- fixed: `{head.fixed}`\n")
            f.write(f"- e_div: `{head.e_div}`\n")
            f.write(f"- M_count: {len(rows)}\n")
            f.write(f"- min x0: {min(xs)}\n")
            f.write(f"- min B_safe: {min(bs)}\n")
            f.write(f"- min (B_safe - d2_lb_floor): {min(d2m)}\n")
            f.write(f"- phi violations: {sum(1 for r in rows if r.ok_phi == 0)}\n")
            f.write(f"- d2_lb violations: {sum(1 for r in rows if r.ok_d2_lb == 0)}\n\n")
        f.write("## Artifacts\n")
        f.write(f"- rows: `{rows_csv.name}`\n")
        f.write(f"- summary: `{summary_md.name}`\n")

    return rows_csv, summary_md


def main() -> None:
    ap = argparse.ArgumentParser(description="Multi-divisible boundary/event certifier")
    ap.add_argument("--n", type=int, required=True)
    ap.add_argument("--fixed", type=str, required=True, help="comma list of fixed non-divisible speeds")
    ap.add_argument("--e-div", type=str, required=True, help="comma list of divisible speeds (each multiple of n)")
    ap.add_argument("--m-list", type=str, default="", help="explicit comma list of M values")
    ap.add_argument("--m-max", type=int, default=0, help="if m-list empty, use admissible M in [1,m-max]")
    ap.add_argument("--tag", type=str, default="multidiv_boundary_v1")
    ap.add_argument("--out-dir", type=str, default=".")
    ap.add_argument("--validate-bruteforce", action="store_true")
    args = ap.parse_args()

    n = args.n
    fixed = parse_int_list(args.fixed)
    e_div = parse_int_list(args.e_div)

    if not fixed:
        raise ValueError("fixed must be nonempty")
    if not e_div:
        raise ValueError("e_div must be nonempty")
    if any(e % n != 0 for e in e_div):
        raise ValueError("all entries in e_div must be divisible by n")

    L0 = lcm_list(fixed + e_div)
    R = n * L0

    if args.m_list:
        M_values = parse_int_list(args.m_list)
    else:
        if args.m_max <= 0:
            raise ValueError("provide --m-list or positive --m-max")
        M_values = [m for m in range(1, args.m_max + 1) if gcd(m, R) == 1]

    rows: List[Row] = []
    print(f"[setup] n={n} fixed={fixed} e_div={e_div} L0={L0} R={R} M_count={len(M_values)}")

    for i, M in enumerate(M_values, start=1):
        r = run_one(n, fixed, e_div, M, args.validate_bruteforce)
        rows.append(r)
        print(
            f"  [{i}/{len(M_values)}] M={M} x0={r.x0} B_safe={r.B_safe} "
            f"B_div={r.B_div} comps={r.B_div_components} segs={r.segment_count} d2_lb={r.d2_lb_floor}"
        )

    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    rows_csv, summary_md = write_outputs(out_dir, args.tag, rows)

    print("\n[done]")
    print(f"rows:    {rows_csv}")
    print(f"summary: {summary_md}")


if __name__ == "__main__":
    main()
