#!/usr/bin/env python3
"""
Batch finite-window certification for multi-divisible Case-2 templates (|E_div|>=2).

Scope
- Engineering/checkset layer for Gap 2.
- Enumerates template families and runs exact boundary/event checks per admissible M.
- Produces D.3-style artifacts: rows/checks/summary.

Non-claim
- This script does not assert full theorem closure. It certifies within a finite M window.
"""

from __future__ import annotations

import argparse
import csv
import importlib.util
import sys
from concurrent.futures import ProcessPoolExecutor, as_completed
from dataclasses import asdict, dataclass
from itertools import combinations
from math import gcd
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple


def parse_int_list(s: str) -> List[int]:
    return [int(x.strip()) for x in s.split(",") if x.strip()]


def lcm2(a: int, b: int) -> int:
    return a * b // gcd(a, b)


def lcm_list(vals: Iterable[int]) -> int:
    r = 1
    for v in vals:
        r = lcm2(r, int(v))
    return r


def phi(n: int) -> int:
    return sum(1 for j in range(1, n + 1) if gcd(j, n) == 1)


def load_multidiv_kernel(kernel_path: Path):
    name = "lrc_multidiv_boundary"
    spec = importlib.util.spec_from_file_location(name, str(kernel_path))
    if spec is None or spec.loader is None:
        raise RuntimeError(f"failed to load kernel from {kernel_path}")
    mod = importlib.util.module_from_spec(spec)
    # Python 3.14 dataclass internals expect module registration during execution.
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


@dataclass
class TemplateRow:
    template_id: str
    n: int
    d: int
    fixed: str
    e_div: str
    fixed_size: int
    L0: int
    R: int
    M_cap: int
    T_size: int
    violations_phi: int
    worst_M: int
    worst_x0: int
    worst_Bsafe: int
    min_d2_margin: int
    first_d2_nonneg_M: int


@dataclass
class CheckRow:
    template_id: str
    n: int
    d: int
    fixed: str
    e_div: str
    M: int
    L: int
    L0: int
    R: int
    x0: int
    phi_n: int
    B_safe: int
    B_div: int
    B_div_components: int
    segment_count: int
    d2_lb_floor: int
    d2_margin: int
    ok_phi: int
    ok_d2_lb: int


def template_id_for(n: int, fixed: Tuple[int, ...], e_div: Tuple[int, ...]) -> str:
    return (
        f"n{n}_f{','.join(map(str, fixed))}_d{','.join(map(str, e_div))}"
    )


def enumerate_templates(
    n: int,
    d: int,
    f_pool: Sequence[int],
    fixed_pool: Sequence[int],
) -> List[Tuple[Tuple[int, ...], Tuple[int, ...]]]:
    if d < 2:
        return []

    fixed_size = n - 2 - d
    if fixed_size <= 0:
        return []

    # Standard-case profiles: e = n*f with gcd(f,n)=1.
    f_ok = sorted({f for f in f_pool if f > 0 and gcd(f, n) == 1})
    if len(f_ok) < d:
        return []

    fixed_sets = list(combinations(sorted(set(fixed_pool)), fixed_size))
    f_sets = list(combinations(f_ok, d))

    out: List[Tuple[Tuple[int, ...], Tuple[int, ...]]] = []
    for fs in f_sets:
        e_div = tuple(sorted(n * f for f in fs))
        for fixed in fixed_sets:
            out.append((fixed, e_div))
    return out


def build_checkset(M_cap: int, R: int) -> List[int]:
    return [m for m in range(1, M_cap + 1) if gcd(m, R) == 1]


def eval_template(task):
    (
        kernel_path,
        n,
        fixed,
        e_div,
        M_cap,
        validate_bruteforce,
    ) = task

    mod = load_multidiv_kernel(Path(kernel_path))
    run_one = mod.run_one

    fixed_list = list(fixed)
    e_div_list = list(e_div)

    d = len(e_div_list)
    fixed_size = len(fixed_list)
    L0 = lcm_list(fixed_list + e_div_list)
    R = n * L0
    T = build_checkset(M_cap, R)
    phi_n = phi(n)

    tid = template_id_for(n, fixed, e_div)

    checks: List[CheckRow] = []
    violations = 0
    worst_M = -1
    worst_x0 = 10**18
    worst_Bsafe = 10**18
    min_d2_margin = 10**18
    first_d2_nonneg = -1

    for M in T:
        out = run_one(n, fixed_list, e_div_list, M, validate_bruteforce)
        d2_margin = out.B_safe - out.d2_lb_floor

        if d2_margin < min_d2_margin:
            min_d2_margin = d2_margin

        if first_d2_nonneg == -1 and d2_margin >= 0:
            first_d2_nonneg = M

        if out.x0 < worst_x0:
            worst_x0 = out.x0
            worst_M = M
            worst_Bsafe = out.B_safe

        ok_phi = int(out.x0 >= phi_n)
        if ok_phi == 0:
            violations += 1

        checks.append(
            CheckRow(
                template_id=tid,
                n=n,
                d=d,
                fixed=out.fixed,
                e_div=out.e_div,
                M=M,
                L=out.L,
                L0=out.L0,
                R=R,
                x0=out.x0,
                phi_n=out.phi_n,
                B_safe=out.B_safe,
                B_div=out.B_div,
                B_div_components=out.B_div_components,
                segment_count=out.segment_count,
                d2_lb_floor=out.d2_lb_floor,
                d2_margin=d2_margin,
                ok_phi=ok_phi,
                ok_d2_lb=out.ok_d2_lb,
            )
        )

    if worst_x0 == 10**18:
        worst_x0 = -1
        worst_Bsafe = -1
    if min_d2_margin == 10**18:
        min_d2_margin = 0

    row = TemplateRow(
        template_id=tid,
        n=n,
        d=d,
        fixed="(" + ",".join(map(str, fixed)) + ")",
        e_div="(" + ",".join(map(str, e_div)) + ")",
        fixed_size=fixed_size,
        L0=L0,
        R=R,
        M_cap=M_cap,
        T_size=len(T),
        violations_phi=violations,
        worst_M=worst_M,
        worst_x0=worst_x0,
        worst_Bsafe=worst_Bsafe,
        min_d2_margin=min_d2_margin,
        first_d2_nonneg_M=first_d2_nonneg,
    )

    return row, checks


def write_outputs(
    out_dir: Path,
    tag: str,
    rows: List[TemplateRow],
    checks: List[CheckRow],
    notes: Dict[str, str],
) -> Tuple[Path, Path, Path]:
    rows_csv = out_dir / f"lrc_case2_multidiv_batch_rows_{tag}.csv"
    checks_csv = out_dir / f"lrc_case2_multidiv_batch_checks_{tag}.csv"
    summary_md = out_dir / f"lrc_case2_multidiv_batch_summary_{tag}.md"

    with rows_csv.open("w", newline="", encoding="utf-8") as f:
        fieldnames = list(TemplateRow.__dataclass_fields__.keys())
        w = csv.DictWriter(f, fieldnames=fieldnames)
        w.writeheader()
        for r in sorted(rows, key=lambda x: (x.n, x.d, x.fixed, x.e_div)):
            w.writerow(asdict(r))

    with checks_csv.open("w", newline="", encoding="utf-8") as f:
        fieldnames = list(CheckRow.__dataclass_fields__.keys())
        w = csv.DictWriter(f, fieldnames=fieldnames)
        w.writeheader()
        for c in sorted(checks, key=lambda x: (x.n, x.d, x.template_id, x.M)):
            w.writerow(asdict(c))

    by_group: Dict[Tuple[int, int], List[TemplateRow]] = {}
    for r in rows:
        by_group.setdefault((r.n, r.d), []).append(r)

    with summary_md.open("w", encoding="utf-8") as f:
        f.write("# Multi-Divisible Batch Certification Summary (Finite Window)\n\n")
        f.write("- Scope: finite-window exact checks per template.\n")
        f.write("- This artifact is computational certification over `M <= M_cap`, not a full asymptotic closure theorem.\n\n")

        for (n, d) in sorted(by_group):
            arr = by_group[(n, d)]
            total_checks = sum(x.T_size for x in arr)
            total_v = sum(x.violations_phi for x in arr)
            min_worst = min(x.worst_x0 for x in arr)
            min_d2_margin = min(x.min_d2_margin for x in arr)
            max_L0 = max(x.L0 for x in arr)
            f.write(f"## n={n}, |E_div|={d}\n")
            f.write(f"- templates: {len(arr)}\n")
            f.write(f"- total finite checks |T|: {total_checks}\n")
            f.write(f"- total phi violations: {total_v}\n")
            f.write(f"- min template worst_x0: {min_worst}\n")
            f.write(f"- min template d2 margin (B_safe-d2_lb_floor): {min_d2_margin}\n")
            f.write(f"- max L0: {max_L0}\n\n")

        f.write("## Run Notes\n")
        for k, v in notes.items():
            f.write(f"- {k}: `{v}`\n")

        f.write("\n## Artifacts\n")
        f.write(f"- rows: `{rows_csv.name}`\n")
        f.write(f"- checks: `{checks_csv.name}`\n")
        f.write(f"- summary: `{summary_md.name}`\n")

    return rows_csv, checks_csv, summary_md


def main() -> None:
    ap = argparse.ArgumentParser(description="Batch finite-window multi-divisible certification")
    ap.add_argument("--n-list", type=str, default="13")
    ap.add_argument("--d-list", type=str, default="2", help="comma list of |E_div| sizes (>=2)")
    ap.add_argument("--f-pool", type=str, default="1,2,3", help="factor pool for e_div = n*f")
    ap.add_argument("--fixed-pool", type=str, default="", help="default 1..n-1")
    ap.add_argument("--m-cap", type=int, default=80)
    ap.add_argument("--workers", type=int, default=1)
    ap.add_argument("--max-templates", type=int, default=0, help="optional cap for smoke runs")
    ap.add_argument("--validate-bruteforce", action="store_true")
    ap.add_argument("--tag", type=str, default="v1")
    ap.add_argument("--out-dir", type=str, default=".")
    ap.add_argument("--kernel-path", type=str, default="")
    args = ap.parse_args()

    n_list = parse_int_list(args.n_list)
    d_list = parse_int_list(args.d_list)
    f_pool = parse_int_list(args.f_pool)

    if not n_list:
        raise ValueError("n-list is empty")
    if not d_list:
        raise ValueError("d-list is empty")
    if args.m_cap < 1:
        raise ValueError("m-cap must be >=1")

    if args.kernel_path:
        kernel_path = Path(args.kernel_path)
    else:
        kernel_path = Path(__file__).with_name("lrc_case2_multidiv_boundary_certifier_v1.py")

    if not kernel_path.exists():
        raise FileNotFoundError(f"kernel not found: {kernel_path}")

    tasks = []

    for n in n_list:
        fixed_pool = parse_int_list(args.fixed_pool) if args.fixed_pool else list(range(1, n))
        for d in d_list:
            templates = enumerate_templates(n, d, f_pool, fixed_pool)
            if args.max_templates > 0:
                templates = templates[: args.max_templates]
            print(f"[build] n={n} d={d} templates={len(templates)}")
            for fixed, e_div in templates:
                tasks.append(
                    (
                        str(kernel_path),
                        n,
                        fixed,
                        e_div,
                        args.m_cap,
                        args.validate_bruteforce,
                    )
                )

    if not tasks:
        raise SystemExit("no templates to evaluate")

    rows: List[TemplateRow] = []
    checks: List[CheckRow] = []

    print(f"[run] templates={len(tasks)} workers={args.workers}")

    done = 0
    if args.workers <= 1:
        for task in tasks:
            row, crows = eval_template(task)
            rows.append(row)
            checks.extend(crows)
            done += 1
            print(
                f"  [{done}/{len(tasks)}] n={row.n} d={row.d} fixed={row.fixed} e_div={row.e_div} "
                f"|T|={row.T_size} violations={row.violations_phi} worst_x0={row.worst_x0}"
            )
    else:
        with ProcessPoolExecutor(max_workers=args.workers) as ex:
            futs = {ex.submit(eval_template, task): task for task in tasks}
            for fut in as_completed(futs):
                row, crows = fut.result()
                rows.append(row)
                checks.extend(crows)
                done += 1
                print(
                    f"  [{done}/{len(tasks)}] n={row.n} d={row.d} fixed={row.fixed} e_div={row.e_div} "
                    f"|T|={row.T_size} violations={row.violations_phi} worst_x0={row.worst_x0}"
                )

    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)

    notes = {
        "n_list": args.n_list,
        "d_list": args.d_list,
        "f_pool": args.f_pool,
        "m_cap": str(args.m_cap),
        "workers": str(args.workers),
        "validate_bruteforce": str(int(args.validate_bruteforce)),
        "kernel_path": str(kernel_path),
        "max_templates": str(args.max_templates),
    }

    rows_csv, checks_csv, summary_md = write_outputs(out_dir, args.tag, rows, checks, notes)

    print("\n[done]")
    print(f"rows:    {rows_csv}")
    print(f"checks:  {checks_csv}")
    print(f"summary: {summary_md}")


if __name__ == "__main__":
    main()
