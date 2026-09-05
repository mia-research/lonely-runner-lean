#!/usr/bin/env python3
"""
Boundary/event-cell batch D.3 certification for all-distinct one-divisible templates.

Goal:
- Avoid per-fiber scans over all b in B_div.
- Use exact boundary cells induced by fixed-floor changes, plus arithmetic counting
  over free-floor blocks (t_M = floor(b/L0)).

This script keeps the same output schema as existing batch certifiers:
- rows CSV
- checks CSV
- summary MD
"""

from __future__ import annotations

import argparse
import csv
from concurrent.futures import ProcessPoolExecutor, as_completed
from dataclasses import dataclass
from fractions import Fraction
from itertools import combinations
from math import ceil, gcd
from pathlib import Path
from typing import Dict, List, Tuple


def lcm2(a: int, b: int) -> int:
    return a * b // gcd(a, b)


def lcm_list(vals: List[int]) -> int:
    r = 1
    for v in vals:
        r = lcm2(r, int(v))
    return r


def precompute_runner_masks(n: int, e: int) -> List[List[int]]:
    """Return masks[t][z] for t in 0..e-1 and z in {0,1}.

    z = 1 means s == 0 where s = e*b mod L.
    bad iff q == 0 OR (q == n-1 and z == 0), q = (e*a + t) mod n.
    """
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
    """Return free-runner masks[r][z] for r = t_M mod n, z in {0,1}."""
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
    """Count integers u in [a,b] by residue class mod n."""
    out = [0] * n
    if a > b:
        return out
    for r in range(n):
        first = a + ((r - a) % n)
        if first <= b:
            out[r] = 1 + (b - first) // n
    return out


def count_free_classes_in_segment(lo: int, hi: int, L0: int, n: int) -> Tuple[List[int], List[int]]:
    """Count b in [lo,hi] by (t_M mod n, z_M) where t_M=floor(b/L0), z_M=1[b mod L0==0].

    Returns:
      (counts_z0, counts_z1), each length n indexed by residue class r=t_M mod n.
    """
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

    # first partial block
    first_len = (u0 + 1) * L0 - lo
    first_z1 = 1 if lo == u0 * L0 else 0
    add_block(u0, first_len, first_z1)

    # middle full blocks
    a = u0 + 1
    b = u1 - 1
    if a <= b:
        counts = residue_counts_interval(a, b, n)
        for r, c in enumerate(counts):
            if c:
                z1[r] += c
                z0[r] += c * (L0 - 1)

    # last partial block
    last_len = hi - u1 * L0 + 1
    add_block(u1, last_len, 1)

    return z0, z1


def fixed_event_segments(L: int, b_lo: int, b_hi: int, fixed: List[int]) -> List[Tuple[int, int]]:
    """Build segments where all fixed-runner (t_e, z_e) states are constant.

    Boundaries include:
      - B_div endpoints (b_lo, b_hi+1)
      - each fixed-floor event x = k*L/e
      - x+1 to isolate the event point itself
    """
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


def compute_x0_boundary(n: int, fixed: List[int], M: int, L0: int):
    """Exact x0 via boundary/event aggregation (single divisible speed n)."""
    L = L0 * M
    b_lo = L // n
    b_hi = (n - 1) * L // n

    fixed_tables: Dict[int, List[List[int]]] = {e: precompute_runner_masks(n, e) for e in fixed}
    free_masks = precompute_free_masks_mod(n, M % n)

    x0 = 0
    B_safe = 0

    for lo, hi in fixed_event_segments(L, b_lo, b_hi, fixed):
        # fixed signature is constant on this segment by construction
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

    B_div = b_hi - b_lo + 1
    return {"x0": x0, "B_safe": B_safe, "B_div": B_div}


def compute_x0_bruteforce(n: int, fixed: List[int], M: int, L0: int):
    """Reference exact kernel (used only for validation mode)."""
    L = L0 * M
    b_lo = L // n
    b_hi = (n - 1) * L // n

    non_div = fixed + [M]
    tables: Dict[int, List[List[int]]] = {e: precompute_runner_masks(n, e) for e in non_div}

    x0 = 0
    B_safe = 0

    for b in range(b_lo, b_hi + 1):
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

    B_div = b_hi - b_lo + 1
    return {"x0": x0, "B_safe": B_safe, "B_div": B_div}


@dataclass
class TemplateCert:
    n: int
    fixed: Tuple[int, ...]
    e_max: int
    L0: int
    A: str
    lam: int
    beta: int
    a_F: str
    b_F: str
    M0: int
    R: int
    T_size: int
    violations: int
    worst_M: int
    worst_x0: int
    worst_Bsafe: int


def certify_template(task):
    n, fixed, validate_with_bruteforce = task
    fixed = tuple(fixed)
    fixed_list = list(fixed)
    e_max = max(fixed_list)

    L0 = lcm_list(fixed_list + [n])
    A = Fraction(n - 1, n) - Fraction(1, L0)
    lam = int(2 * L0 * Fraction(n - e_max, n * e_max))
    beta = 1

    if lam <= 0:
        # Defensive fallback; expected not to trigger for the template class in scope.
        a_F = Fraction(1, 1)
        b_F = Fraction(-(10**6), 1)
        M0 = 1
    else:
        a_F = A * lam
        b_F = A * beta - (4 * L0 + 2)
        rhs = Fraction(n - 1) - b_F
        M0 = max(1, ceil(rhs / a_F))

    R = n * L0
    T = [m for m in range(1, M0) if gcd(m, R) == 1]

    checks = []
    violations = 0
    worst = None

    for M in T:
        out = compute_x0_boundary(n, fixed_list, M, L0)

        if validate_with_bruteforce:
            ref = compute_x0_bruteforce(n, fixed_list, M, L0)
            if out != ref:
                raise RuntimeError(
                    f"boundary mismatch n={n} fixed={fixed} M={M}: boundary={out} ref={ref}"
                )

        phi = sum(1 for j in range(1, n + 1) if gcd(j, n) == 1)
        ok = out["x0"] >= phi

        checks.append({
            "n": n,
            "fixed": "(" + ",".join(map(str, fixed)) + ")",
            "L0": L0,
            "e_max": e_max,
            "M": M,
            "M0": M0,
            "R": R,
            "x0": out["x0"],
            "phi_n": phi,
            "B_safe": out["B_safe"],
            "B_div": out["B_div"],
            "ok": int(ok),
        })

        if not ok:
            violations += 1
        if worst is None or out["x0"] < worst["x0"]:
            worst = {"M": M, "x0": out["x0"], "B_safe": out["B_safe"]}

    if worst is None:
        worst = {"M": -1, "x0": 10**9, "B_safe": -1}

    cert = TemplateCert(
        n=n,
        fixed=fixed,
        e_max=e_max,
        L0=L0,
        A=str(A),
        lam=lam,
        beta=beta,
        a_F=str(a_F),
        b_F=str(b_F),
        M0=M0,
        R=R,
        T_size=len(T),
        violations=violations,
        worst_M=worst["M"],
        worst_x0=worst["x0"],
        worst_Bsafe=worst["B_safe"],
    )
    return cert, checks


def write_outputs(base_dir: Path, certs: List[TemplateCert], checks: List[dict], tag: str):
    rows_csv = base_dir / f"lrc_case2_d3_batch_rows_{tag}.csv"
    checks_csv = base_dir / f"lrc_case2_d3_batch_checks_{tag}.csv"
    summary_md = base_dir / f"lrc_case2_d3_batch_summary_{tag}.md"

    with rows_csv.open("w", newline="", encoding="utf-8") as f:
        w = csv.writer(f)
        w.writerow([
            "n", "fixed", "e_max", "L0", "A", "lambda", "beta",
            "a_F", "b_F", "M0", "R", "T_size", "violations",
            "worst_M", "worst_x0", "worst_Bsafe",
        ])
        for c in sorted(certs, key=lambda x: (x.n, x.fixed)):
            w.writerow([
                c.n,
                "(" + ",".join(map(str, c.fixed)) + ")",
                c.e_max,
                c.L0,
                c.A,
                c.lam,
                c.beta,
                c.a_F,
                c.b_F,
                c.M0,
                c.R,
                c.T_size,
                c.violations,
                c.worst_M,
                c.worst_x0,
                c.worst_Bsafe,
            ])

    if checks:
        with checks_csv.open("w", newline="", encoding="utf-8") as f:
            fields = list(checks[0].keys())
            w = csv.DictWriter(f, fieldnames=fields)
            w.writeheader()
            w.writerows(checks)

    by_n: Dict[int, List[TemplateCert]] = {}
    for c in certs:
        by_n.setdefault(c.n, []).append(c)

    with summary_md.open("w", encoding="utf-8") as f:
        f.write("# D.3 Boundary Batch Certification Summary\n\n")
        for n in sorted(by_n):
            arr = by_n[n]
            v = sum(c.violations for c in arr)
            t = sum(c.T_size for c in arr)
            worst_x0 = min(c.worst_x0 for c in arr)
            max_M0 = max(c.M0 for c in arr)
            f.write(f"## n={n}\n")
            f.write(f"- templates: {len(arr)}\n")
            f.write(f"- total finite checks |T|: {t}\n")
            f.write(f"- total violations: {v}\n")
            f.write(f"- min worst_x0 across templates: {worst_x0}\n")
            f.write(f"- max M0 across templates: {max_M0}\n\n")

        f.write("## Artifacts\n")
        f.write(f"- rows: `{rows_csv.name}`\n")
        f.write(f"- checks: `{checks_csv.name}`\n")
        f.write(f"- summary: `{summary_md.name}`\n")

    return rows_csv, checks_csv, summary_md


def compare_rows(certs: List[TemplateCert], expected_paths: List[Path]) -> Tuple[int, int]:
    """Compare core cert fields against existing rows artifacts.

    Returns (matched, mismatched).
    """
    expected: Dict[Tuple[int, Tuple[int, ...]], dict] = {}
    for p in expected_paths:
        with p.open(newline="", encoding="utf-8") as f:
            r = csv.DictReader(f)
            for row in r:
                n = int(row["n"])
                fixed = tuple(int(x) for x in row["fixed"].strip("()").split(",") if x)
                expected[(n, fixed)] = row

    matched = 0
    mismatched = 0

    for c in certs:
        key = (c.n, c.fixed)
        e = expected.get(key)
        if e is None:
            continue

        checks = {
            "M0": (c.M0, int(e["M0"])),
            "T_size": (c.T_size, int(e["T_size"])),
            "violations": (c.violations, int(e["violations"])),
            "worst_M": (c.worst_M, int(e["worst_M"])),
            "worst_x0": (c.worst_x0, int(e["worst_x0"])),
            "worst_Bsafe": (c.worst_Bsafe, int(e["worst_Bsafe"])),
        }
        bad = [k for k, (a, b) in checks.items() if a != b]
        if bad:
            mismatched += 1
            print(f"[mismatch] n={c.n} fixed={c.fixed} fields={bad}")
        else:
            matched += 1

    return matched, mismatched


def main():
    ap = argparse.ArgumentParser(description="Boundary/event batch D.3 certification")
    ap.add_argument("--n-list", type=str, default="7,11")
    ap.add_argument("--workers", type=int, default=6)
    ap.add_argument("--tag", type=str, default="boundary_v1")
    ap.add_argument("--out-dir", type=str, default=".")
    ap.add_argument("--validate-with-bruteforce", action="store_true",
                    help="Cross-check each computed check against brute-force kernel.")
    ap.add_argument("--compare-rows", type=str, default="",
                    help="Comma-separated existing rows CSVs for exact-match comparison.")
    ap.add_argument("--strict-compare", action="store_true",
                    help="Exit nonzero if any row mismatch is found in --compare-rows.")
    args = ap.parse_args()

    n_values = [int(x.strip()) for x in args.n_list.split(",") if x.strip()]
    tasks = []
    for n in n_values:
        temps = list(combinations(range(1, n), n - 3))
        print(f"[build] n={n} templates={len(temps)}")
        tasks.extend([(n, t, args.validate_with_bruteforce) for t in temps])

    certs: List[TemplateCert] = []
    checks: List[dict] = []

    print(f"[run] total templates={len(tasks)} workers={args.workers}")
    done = 0

    if args.workers <= 1:
        # Sandbox-safe fallback: avoid process-semaphore requirements.
        for task in tasks:
            cert, crows = certify_template(task)
            certs.append(cert)
            checks.extend(crows)
            done += 1
            print(
                f"  [{done}/{len(tasks)}] n={cert.n} fixed={cert.fixed} "
                f"|T|={cert.T_size} violations={cert.violations} worst_x0={cert.worst_x0}"
            )
    else:
        with ProcessPoolExecutor(max_workers=args.workers) as ex:
            futs = {ex.submit(certify_template, task): task for task in tasks}
            for fut in as_completed(futs):
                cert, crows = fut.result()
                certs.append(cert)
                checks.extend(crows)
                done += 1
                print(
                    f"  [{done}/{len(tasks)}] n={cert.n} fixed={cert.fixed} "
                    f"|T|={cert.T_size} violations={cert.violations} worst_x0={cert.worst_x0}"
                )

    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    rows_csv, checks_csv, summary_md = write_outputs(out_dir, certs, checks, args.tag)

    if args.compare_rows:
        expected_paths = [Path(x.strip()) for x in args.compare_rows.split(",") if x.strip()]
        matched, mismatched = compare_rows(certs, expected_paths)
        print(f"[compare] matched={matched} mismatched={mismatched}")
        if args.strict_compare and mismatched > 0:
            raise SystemExit(2)

    print("\n[done]")
    print(f"rows:    {rows_csv}")
    print(f"checks:  {checks_csv}")
    print(f"summary: {summary_md}")


if __name__ == "__main__":
    main()
