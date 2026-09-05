#!/usr/bin/env python3
from __future__ import annotations

import argparse
import csv
from collections import defaultdict
from fractions import Fraction
from pathlib import Path
from typing import Dict, List, Sequence, Set, Tuple


def parse_fixed(s: str) -> Tuple[int, ...]:
    s = s.strip()
    if s.startswith("(") and s.endswith(")"):
        s = s[1:-1]
    if not s:
        return tuple()
    return tuple(int(x.strip()) for x in s.split(",") if x.strip())


def inv_mod(a: int, n: int) -> int:
    return pow(a, -1, n)


def precompute_runner_masks(n: int, e: int) -> List[List[int]]:
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


def fixed_event_segments(L: int, b_lo: int, b_hi: int, fixed: Sequence[int]) -> List[Tuple[int, int]]:
    boundaries = {b_lo, b_hi + 1}
    for e in fixed:
        for k in range(e + 1):
            x = (k * L) // e
            if b_lo <= x <= b_hi:
                boundaries.add(x)
            xp = x + 1
            if b_lo <= xp <= b_hi + 1:
                boundaries.add(xp)

    pts = sorted(boundaries)
    segs: List[Tuple[int, int]] = []
    for a, b in zip(pts, pts[1:]):
        lo = a
        hi = b - 1
        if lo <= hi:
            segs.append((lo, hi))
    return segs


def canonical_intervals(n: int, L: int, e_max: int) -> Tuple[int, int, int, int]:
    lo_a = (L + n - 1) // n
    lo_b = L // e_max - 1
    hi_a = L - (L // e_max)
    hi_b = ((n - 1) * L) // n
    return lo_a, lo_b, hi_a, hi_b


def fixed_mask_for_b(n: int, fixed_tables: Dict[int, List[List[int]]], fixed: Sequence[int], L: int, b: int) -> int:
    mask = 0
    for e in fixed:
        eb = e * b
        t = eb // L
        s = eb - t * L
        z = 1 if s == 0 else 0
        mask |= fixed_tables[e][t][z]
    return mask


def mask_to_rfix(mask: int, n: int) -> List[int]:
    return [a for a in range(n) if ((mask >> a) & 1) == 0]


def fmt_list(vals: Sequence[int]) -> str:
    return "(" + ",".join(str(x) for x in vals) + ")"


def load_check_rows(paths: Sequence[Path]) -> Dict[Tuple[int, str, int, int], dict]:
    out: Dict[Tuple[int, str, int, int], dict] = {}
    for path in paths:
        with path.open(newline="", encoding="utf-8") as f:
            rd = csv.DictReader(f)
            for r in rd:
                key = (int(r["n"]), r["fixed"], int(r["M"]), int(r["L0"]))
                out[key] = r
    return out


def main() -> None:
    ap = argparse.ArgumentParser(description="Probe Gap-1 residual structure for GIL/two-class route")
    ap.add_argument("--rows", type=str, default="lrc_gap1_delta_tr_mtot3_rows_v1.csv")
    ap.add_argument(
        "--checks",
        type=str,
        default=(
            "lrc_case2_d3_batch_checks_n7n11_v2.csv,"
            "lrc_case2_d3_batch_checks_n13_boundary_v1.csv,"
            "lrc_case2_d3_batch_checks_n17_boundary_v1.csv,"
            "lrc_case2_d3_batch_checks_n19_boundary_v1.csv"
        ),
        help="Comma-separated check CSV paths",
    )
    ap.add_argument("--out-dir", type=str, default=".")
    ap.add_argument("--tag", type=str, default="v1")
    args = ap.parse_args()

    rows_path = Path(args.rows)
    check_paths = [Path(x.strip()) for x in args.checks.split(",") if x.strip()]

    all_rows = list(csv.DictReader(rows_path.open(newline="", encoding="utf-8")))
    residual_rows = [r for r in all_rows if Fraction(r["Xi_tr"]) > 0]

    check_map = load_check_rows(check_paths)

    residual_templates: Set[Tuple[int, str, int]] = {
        (int(r["n"]), r["fixed"], int(r["L0"])) for r in residual_rows
    }

    fixed_tables_cache: Dict[Tuple[int, Tuple[int, ...]], Dict[int, List[List[int]]]] = {}
    free_masks_cache: Dict[Tuple[int, int], List[List[int]]] = {}

    def get_fixed_tables(n: int, fixed: Tuple[int, ...]) -> Dict[int, List[List[int]]]:
        key = (n, fixed)
        if key not in fixed_tables_cache:
            fixed_tables_cache[key] = {e: precompute_runner_masks(n, e) for e in fixed}
        return fixed_tables_cache[key]

    def get_free_masks(n: int, m_mod: int) -> List[List[int]]:
        key = (n, m_mod)
        if key not in free_masks_cache:
            free_masks_cache[key] = precompute_free_masks_mod(n, m_mod)
        return free_masks_cache[key]

    # Residual-row analysis
    out_rows: List[dict] = []
    gil_match = 0
    gil_total = 0
    gap_ge_n_minus_2 = 0
    x0_non_danger_ge_phi = 0
    bsafe_non_danger_ge_phi = 0
    bsafe_outliers: List[dict] = []

    by_n: Dict[int, List[dict]] = defaultdict(list)

    for r in residual_rows:
        n = int(r["n"])
        fixed_s = r["fixed"]
        fixed = parse_fixed(fixed_s)
        M = int(r["M"])
        L0 = int(r["L0"])
        L = L0 * M
        e_max = max(fixed)

        key = (n, fixed_s, M, L0)
        if key not in check_map:
            raise RuntimeError(f"Missing check row for {key}")
        c = check_map[key]
        x0 = int(c["x0"])
        phi_n = int(c["phi_n"])
        B_div = int(c["B_div"])

        fixed_tables = get_fixed_tables(n, fixed)
        free_masks = get_free_masks(n, M % n)

        b_lo = (L + n - 1) // n
        b_hi = ((n - 1) * L) // n

        # GIL check on representative lower-canonical fiber.
        lo_a, lo_b, _, _ = canonical_intervals(n, L, e_max)
        gil_lower_match = 1
        pred_low_rfix = ""
        obs_low_rfix = ""
        missing_pair = ""
        if lo_a <= lo_b:
            b0 = lo_a
            mask0 = fixed_mask_for_b(n, fixed_tables, fixed, L, b0)
            obs = sorted(mask_to_rfix(mask0, n))
            miss = sorted(set(range(1, n)) - set(e % n for e in fixed))
            if len(miss) != 2:
                raise RuntimeError(f"Unexpected missing-speed count !=2 for {key}: {miss}")
            pred = sorted([(-inv_mod(miss[0], n)) % n, (-inv_mod(miss[1], n)) % n])
            gil_total += 1
            if obs == pred:
                gil_match += 1
            else:
                gil_lower_match = 0
            pred_low_rfix = fmt_list(pred)
            obs_low_rfix = fmt_list(obs)
            missing_pair = fmt_list(miss)

        invM = inv_mod(M % n, n)
        dangerous_gap = min(invM, n - invM)

        distinct_gaps: Set[int] = set()
        dangerous_b_mass = 0
        bsafe_non_danger = 0
        x0_non_danger = 0

        for seg_lo, seg_hi in fixed_event_segments(L, b_lo, b_hi, fixed):
            length = seg_hi - seg_lo + 1
            fmask = fixed_mask_for_b(n, fixed_tables, fixed, L, seg_lo)
            R_fix = mask_to_rfix(fmask, n)

            dangerous = False
            if len(R_fix) == 2:
                d = (R_fix[1] - R_fix[0]) % n
                g = min(d, n - d)
                distinct_gaps.add(g)
                if g == dangerous_gap:
                    dangerous = True

            if dangerous:
                dangerous_b_mass += length

            c0, c1 = count_free_classes_in_segment(seg_lo, seg_hi, L0, n)
            for rr in range(n):
                n0 = c0[rr]
                if n0:
                    A = n - (fmask | free_masks[rr][0]).bit_count()
                    if not dangerous:
                        if A > 0:
                            bsafe_non_danger += n0
                        x0_non_danger += A * n0
                n1 = c1[rr]
                if n1:
                    A = n - (fmask | free_masks[rr][1]).bit_count()
                    if not dangerous:
                        if A > 0:
                            bsafe_non_danger += n1
                        x0_non_danger += A * n1

        gap_count = len(distinct_gaps)
        if gap_count >= n - 2:
            gap_ge_n_minus_2 += 1

        x0_nd_ok = int(x0_non_danger >= phi_n)
        bsafe_nd_ok = int(bsafe_non_danger >= phi_n)
        if x0_nd_ok:
            x0_non_danger_ge_phi += 1
        if bsafe_nd_ok:
            bsafe_non_danger_ge_phi += 1
        else:
            bsafe_outliers.append(
                {
                    "n": n,
                    "fixed": fixed_s,
                    "M": M,
                    "L0": L0,
                    "Bsafe_non_danger": bsafe_non_danger,
                    "phi_n": phi_n,
                    "x0_non_danger": x0_non_danger,
                    "x0": x0,
                }
            )

        row_out = {
            "n": n,
            "fixed": fixed_s,
            "M": M,
            "L0": L0,
            "Xi_tr": r["Xi_tr"],
            "phi_n": phi_n,
            "x0": x0,
            "B_div": B_div,
            "missing_pair": missing_pair,
            "gil_lower_match": gil_lower_match,
            "pred_low_R_fix": pred_low_rfix,
            "obs_low_R_fix": obs_low_rfix,
            "distinct_gap_count": gap_count,
            "dangerous_b_mass": dangerous_b_mass,
            "dangerous_b_frac": f"{(dangerous_b_mass / B_div):.10f}" if B_div else "0",
            "Bsafe_non_danger": bsafe_non_danger,
            "x0_non_danger": x0_non_danger,
            "x0_non_danger_ge_phi": x0_nd_ok,
            "Bsafe_non_danger_ge_phi": bsafe_nd_ok,
        }
        out_rows.append(row_out)
        by_n[n].append(row_out)

    # Template-level low-band residue class analysis.
    checks_by_template: Dict[Tuple[int, str, int], List[dict]] = defaultdict(list)
    for key, row in check_map.items():
        n, fixed_s, M, L0 = key
        tpl = (n, fixed_s, L0)
        if tpl in residual_templates:
            checks_by_template[tpl].append(row)

    template_rows: List[dict] = []
    two_class_count = 0
    two_class_complementary = 0
    two_class_pred_match = 0
    one_class_count = 0

    for tpl in sorted(checks_by_template):
        n, fixed_s, L0 = tpl
        fixed = parse_fixed(fixed_s)
        e_max = max(fixed)
        fixed_tables = get_fixed_tables(n, fixed)

        bad_low_residues: Set[int] = set()
        all_residues: Set[int] = set()

        for row in checks_by_template[tpl]:
            M = int(row["M"])
            m_mod = M % n
            all_residues.add(m_mod)

            L = L0 * M
            lo_a, lo_b, _, _ = canonical_intervals(n, L, e_max)
            if lo_a > lo_b:
                continue

            free_masks = get_free_masks(n, m_mod)
            bad_exists = False
            for seg_lo, seg_hi in fixed_event_segments(L, lo_a, lo_b, fixed):
                fmask = fixed_mask_for_b(n, fixed_tables, fixed, L, seg_lo)
                c0, c1 = count_free_classes_in_segment(seg_lo, seg_hi, L0, n)
                for rr in range(n):
                    n0 = c0[rr]
                    if n0:
                        A = n - (fmask | free_masks[rr][0]).bit_count()
                        if A == 0:
                            bad_exists = True
                            break
                    n1 = c1[rr]
                    if n1:
                        A = n - (fmask | free_masks[rr][1]).bit_count()
                        if A == 0:
                            bad_exists = True
                            break
                if bad_exists:
                    break

            if bad_exists:
                bad_low_residues.add(m_mod)

        miss = sorted(set(range(1, n)) - set(e % n for e in fixed))
        if len(miss) != 2:
            raise RuntimeError(f"Unexpected missing-speed count !=2 for template {tpl}: {miss}")
        d = (inv_mod(miss[1], n) - inv_mod(miss[0], n)) % n
        if d == 0:
            raise RuntimeError(f"Unexpected zero inverse-difference for template {tpl}")
        c = inv_mod(d, n)
        pred_pm = {c, (-c) % n}

        bad_sorted = sorted(bad_low_residues)
        class_count = len(bad_low_residues)
        is_two = class_count == 2
        is_one = class_count == 1
        comp = int(is_two and ((bad_sorted[0] + bad_sorted[1]) % n == 0))
        pm_match = int(is_two and bad_low_residues == pred_pm)

        if is_two:
            two_class_count += 1
            two_class_complementary += comp
            two_class_pred_match += pm_match
        if is_one:
            one_class_count += 1

        template_rows.append(
            {
                "n": n,
                "fixed": fixed_s,
                "L0": L0,
                "rows_scanned": len(checks_by_template[tpl]),
                "all_M_residues_seen": fmt_list(sorted(all_residues)),
                "bad_low_M_residues": fmt_list(bad_sorted),
                "low_bad_class_count": class_count,
                "two_class_complementary": comp,
                "pred_pm_c": fmt_list(sorted(pred_pm)),
                "pred_two_class_match": pm_match,
            }
        )

    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    rows_csv = out_dir / f"lrc_gap1_gil_two_class_probe_rows_{args.tag}.csv"
    tpl_csv = out_dir / f"lrc_gap1_gil_two_class_probe_templates_{args.tag}.csv"
    summary_md = out_dir / f"lrc_gap1_gil_two_class_probe_summary_{args.tag}.md"

    if out_rows:
        with rows_csv.open("w", newline="", encoding="utf-8") as f:
            wr = csv.DictWriter(f, fieldnames=list(out_rows[0].keys()))
            wr.writeheader()
            wr.writerows(out_rows)

    if template_rows:
        with tpl_csv.open("w", newline="", encoding="utf-8") as f:
            wr = csv.DictWriter(f, fieldnames=list(template_rows[0].keys()))
            wr.writeheader()
            wr.writerows(template_rows)

    total_residual = len(out_rows)
    gap_fail = total_residual - gap_ge_n_minus_2

    with summary_md.open("w", encoding="utf-8") as f:
        f.write("# Gap-1 GIL / Two-Class Probe Summary\n")
        f.write("**Date:** 2026-03-03\n")
        f.write("**Scope:** residual rows where `Xi_tr>0` from `lrc_gap1_delta_tr_mtot3_rows_v1.csv`.\n\n")

        f.write("## Inputs\n")
        f.write(f"- rows: `{rows_path.name}`\n")
        for p in check_paths:
            f.write(f"- checks: `{p.name}`\n")
        f.write("\n")

        f.write("## Residual-row checks\n")
        f.write(f"- residual rows analyzed: `{total_residual}`\n")
        f.write(f"- GIL lower-band match count: `{gil_match}/{gil_total}`\n")
        f.write(f"- strong gap-diversity (`distinct_gaps >= n-2`) rows: `{gap_ge_n_minus_2}/{total_residual}`\n")
        f.write(f"- strong gap-diversity failures: `{gap_fail}`\n")
        f.write(f"- rows with `x0_non_danger >= phi(n)`: `{x0_non_danger_ge_phi}/{total_residual}`\n")
        f.write(f"- rows with `Bsafe_non_danger >= phi(n)`: `{bsafe_non_danger_ge_phi}/{total_residual}`\n\n")

        f.write("## Template-level low-band residue law\n")
        f.write(f"- residual templates scanned: `{len(template_rows)}`\n")
        f.write(f"- templates with exactly one bad-low residue class: `{one_class_count}`\n")
        f.write(f"- templates with exactly two bad-low residue classes: `{two_class_count}`\n")
        f.write(f"- two-class templates with complementary classes: `{two_class_complementary}/{two_class_count}`\n")
        f.write(
            f"- two-class templates matching predicted `M mod n in {{+c,-c}}` law: `{two_class_pred_match}/{two_class_count}`\n\n"
        )

        f.write("## By n (residual rows)\n")
        f.write("| n | rows | avg_distinct_gaps | min_distinct_gaps | avg_dangerous_frac | max_dangerous_frac |\n")
        f.write("|--:|----:|------------------:|------------------:|-------------------:|-------------------:|\n")
        for n in sorted(by_n):
            arr = by_n[n]
            gaps = [int(x["distinct_gap_count"]) for x in arr]
            dfr = [float(x["dangerous_b_frac"]) for x in arr]
            f.write(
                f"| {n} | {len(arr)} | {sum(gaps)/len(gaps):.2f} | {min(gaps)} | "
                f"{sum(dfr)/len(dfr):.4f} | {max(dfr):.4f} |\n"
            )

        f.write("\n## Bsafe Non-Danger Outliers\n")
        if bsafe_outliers:
            for o in bsafe_outliers:
                f.write(
                    f"- n={o['n']}, fixed={o['fixed']}, M={o['M']}, L0={o['L0']}: "
                    f"`Bsafe_non_danger={o['Bsafe_non_danger']} < phi={o['phi_n']}`, "
                    f"but `x0_non_danger={o['x0_non_danger']} >= phi={o['phi_n']}` "
                    f"(and `x0_non_danger <= x0={o['x0']}`).\n"
                )
        else:
            f.write("- none\n")

        f.write("\n## Artifacts\n")
        f.write(f"- rows: `{rows_csv.name}`\n")
        f.write(f"- templates: `{tpl_csv.name}`\n")
        f.write(f"- summary: `{summary_md.name}`\n")

    print(f"rows: {rows_csv}")
    print(f"templates: {tpl_csv}")
    print(f"summary: {summary_md}")


if __name__ == "__main__":
    main()
