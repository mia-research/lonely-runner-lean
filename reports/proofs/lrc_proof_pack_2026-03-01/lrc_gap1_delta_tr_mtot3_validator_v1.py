#!/usr/bin/env python3
from __future__ import annotations

import argparse
import csv
from fractions import Fraction
from math import isqrt
from pathlib import Path
from typing import Dict, List, Tuple


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    r = isqrt(n)
    f = 3
    while f <= r:
        if n % f == 0:
            return False
        f += 2
    return True


def parse_fixed(s: str) -> Tuple[int, ...]:
    s = s.strip()
    if s.startswith("(") and s.endswith(")"):
        s = s[1:-1]
    if not s:
        return tuple()
    return tuple(int(x.strip()) for x in s.split(",") if x.strip())


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


def fixed_event_segments(L: int, b_lo: int, b_hi: int, fixed: List[int]) -> List[Tuple[int, int]]:
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


def count_bad_interval(n: int, fixed: List[int], M: int, L0: int, lo: int, hi: int) -> int:
    if lo > hi:
        return 0
    L = L0 * M
    fixed_tables: Dict[int, List[List[int]]] = {e: precompute_runner_masks(n, e) for e in fixed}
    free_masks = precompute_free_masks_mod(n, M % n)

    bad = 0
    for seg_lo, seg_hi in fixed_event_segments(L, lo, hi, fixed):
        b = seg_lo
        fixed_mask = 0
        for e in fixed:
            eb = e * b
            t = eb // L
            s = eb - t * L
            z = 1 if s == 0 else 0
            fixed_mask |= fixed_tables[e][t][z]

        c0, c1 = count_free_classes_in_segment(seg_lo, seg_hi, L0, n)
        for r in range(n):
            n0 = c0[r]
            if n0:
                cover = fixed_mask | free_masks[r][0]
                A_b = n - cover.bit_count()
                if A_b == 0:
                    bad += n0
            n1 = c1[r]
            if n1:
                cover = fixed_mask | free_masks[r][1]
                A_b = n - cover.bit_count()
                if A_b == 0:
                    bad += n1
    return bad


def canonical_intervals(n: int, L: int, e_max: int):
    lo_a = (L + n - 1) // n
    lo_b = L // e_max - 1
    hi_a = L - (L // e_max)
    hi_b = ((n - 1) * L) // n
    return lo_a, lo_b, hi_a, hi_b


def cell_count_mtot(n: int, L: int, e_max: int) -> int:
    lo_a, lo_b, hi_a, hi_b = canonical_intervals(n, L, e_max)
    m = 0
    if lo_a <= lo_b:
        m += 1
    if hi_a <= hi_b:
        b_star = L - (L // e_max)
        if hi_a <= b_star <= hi_b and b_star < hi_b:
            m += 2
        else:
            m += 1
    return m


def process_row(n: int, fixed: Tuple[int, ...], M: int, L0: int) -> dict:
    fixed_list = list(fixed)
    e_max = max(fixed_list)
    L = L0 * M

    lo_a, lo_b, hi_a, hi_b = canonical_intervals(n, L, e_max)
    len_lo = max(0, lo_b - lo_a + 1)
    len_hi = max(0, hi_b - hi_a + 1)
    len_tot = len_lo + len_hi

    bad_lo = count_bad_interval(n, fixed_list, M, L0, lo_a, lo_b) if len_lo > 0 else 0
    bad_hi = count_bad_interval(n, fixed_list, M, L0, hi_a, hi_b) if len_hi > 0 else 0
    bad_tot = bad_lo + bad_hi

    b_safe = len_tot - bad_tot
    m_tot = cell_count_mtot(n, L, e_max)
    k_loc = 2 * L0 * m_tot

    delta = Fraction(len_tot, n) + k_loc - bad_tot
    rhs = k_loc - (Fraction(n - 1, n) * len_tot - (n - 1))
    xi = rhs - delta
    if xi < 0:
        xi = Fraction(0, 1)

    crit_delta = delta >= rhs
    crit_bsafe = b_safe >= (n - 1)

    return {
        "n": n,
        "fixed": "(" + ",".join(str(x) for x in fixed) + ")",
        "M": M,
        "L0": L0,
        "e_max": e_max,
        "len_I_tot": len_tot,
        "C_bad_I_tot": bad_tot,
        "B_safe_I_tot": b_safe,
        "m_tot": m_tot,
        "K_loc_sh": k_loc,
        "Delta_tr_sh": str(delta),
        "rhs_G1K4": str(rhs),
        "Xi_tr": str(xi),
        "delta_nonneg": int(delta >= 0),
        "criterion_match": int(crit_delta == crit_bsafe),
        "criterion_delta": int(crit_delta),
        "criterion_bsafe": int(crit_bsafe),
    }


def main():
    ap = argparse.ArgumentParser(description='Support validator for G1.K reduced Delta_tr formulation')
    ap.add_argument('--checks', type=str, required=True,
                    help='Comma-separated check CSV paths (existing artifacts)')
    ap.add_argument('--out-dir', type=str, default='.')
    ap.add_argument('--tag', type=str, default='v1')
    args = ap.parse_args()

    check_paths = [Path(x.strip()) for x in args.checks.split(',') if x.strip()]
    rows = []
    source_ok_fail = 0
    source_phi_fail = 0

    for path in check_paths:
        with path.open(newline='', encoding='utf-8') as f:
            rd = csv.DictReader(f)
            for r in rd:
                n = int(r['n'])
                if not is_prime(n):
                    continue
                fixed = parse_fixed(r['fixed'])
                M = int(r['M'])
                L0 = int(r['L0'])
                if 'ok' in r and r['ok'] != '':
                    if int(r['ok']) == 0:
                        source_ok_fail += 1
                if 'x0' in r and 'phi_n' in r and r['x0'] != '' and r['phi_n'] != '':
                    if int(r['x0']) < int(r['phi_n']):
                        source_phi_fail += 1
                rows.append(process_row(n, fixed, M, L0))

    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    rows_csv = out_dir / f'lrc_gap1_delta_tr_mtot3_rows_{args.tag}.csv'
    md = out_dir / f'lrc_gap1_delta_tr_mtot3_validation_{args.tag}.md'

    if rows:
        fields = list(rows[0].keys())
        with rows_csv.open('w', newline='', encoding='utf-8') as f:
            wr = csv.DictWriter(f, fieldnames=fields)
            wr.writeheader()
            wr.writerows(rows)

    total = len(rows)
    nonneg_fail = sum(1 for r in rows if int(r['delta_nonneg']) == 0)
    crit_mismatch = sum(1 for r in rows if int(r['criterion_match']) == 0)
    xi_vals = [Fraction(r['Xi_tr']) for r in rows]
    xi_zero = sum(1 for x in xi_vals if x == 0)
    xi_pos = sum(1 for x in xi_vals if x > 0)
    max_xi = max(xi_vals, default=Fraction(0, 1))

    by_n = {}
    for r in rows:
        n = int(r['n'])
        by_n.setdefault(n, []).append(r)

    with md.open('w', encoding='utf-8') as f:
        f.write('# Gap-1 Reduced Delta_tr (m_tot<=3) Support Validation\n')
        f.write('**Date:** 2026-03-03\n\n')
        f.write('## Scope\n')
        f.write('Prime-window support check over existing certified check artifacts.\n')
        f.write('This is a consistency artifact only (not a proof dependency).\n\n')
        f.write('## Inputs\n')
        for pth in check_paths:
            f.write(f'- `{pth.name}`\n')
        f.write('\n')
        f.write('## Global results\n')
        f.write(f'- rows processed (prime n only): `{total}`\n')
        f.write(f'- `Delta_tr^sh >= 0` failures: `{nonneg_fail}`\n')
        f.write(
            f'- criterion equivalence mismatches (`G1.K.4` vs `B_safe>=n-1`): `{crit_mismatch}` '
            '(algebraic consistency check on computed quantities)\n'
        )
        f.write(f'- rows with `Xi_tr = 0`: `{xi_zero}`\n')
        f.write(f'- rows with `Xi_tr > 0`: `{xi_pos}`\n')
        f.write(f'- max observed `Xi_tr`: `{max_xi}`\n')
        f.write(f'- input-row certifier failures (`ok=0`): `{source_ok_fail}`\n')
        f.write(f'- input-row theorem failures (`x0 < phi_n`): `{source_phi_fail}`\n\n')

        f.write('## By n\n')
        f.write('| n | rows | Delta_nonneg_fail | criterion_mismatch | Xi_tr=0 |\n')
        f.write('|--:|----:|------------------:|-------------------:|--------:|\n')
        for n in sorted(by_n):
            arr = by_n[n]
            f_nonneg = sum(1 for r in arr if int(r['delta_nonneg']) == 0)
            f_match = sum(1 for r in arr if int(r['criterion_match']) == 0)
            f_xi = sum(1 for r in arr if Fraction(r['Xi_tr']) == 0)
            f.write(f'| {n} | {len(arr)} | {f_nonneg} | {f_match} | {f_xi} |\n')

        f.write('\n## Artifacts\n')
        f.write(f'- rows: `{rows_csv.name}`\n')
        f.write(f'- summary: `{md.name}`\n')

    print(f'rows: {rows_csv}')
    print(f'summary: {md}')


if __name__ == '__main__':
    main()
