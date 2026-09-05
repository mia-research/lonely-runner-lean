#!/usr/bin/env python3
"""
Template-wise affine TCP builder for multi-divisible families.

Pipeline (finite-compute, scope-controlled):
1. Start from existing exact checks CSV.
2. Derive per-template affine lower line d2_lb_floor >= a_F*M + b_F over known checks.
3. Compute M0(F) from phi threshold using this affine line.
4. If M0(F) exceeds known range, extend exact checks up to min(M0-1, m_cap_max), iterate.
5. Emit per-template rows and full checks with affine diagnostics.

Note:
- This builds the TCP-style coefficient/checkset layer from sharpened D.2 diagnostics.
- It does not by itself prove asymptotic validity beyond the checked cap.
"""

from __future__ import annotations

import argparse
import csv
import importlib.util
import sys
from dataclasses import asdict, dataclass
from fractions import Fraction
from math import gcd
from pathlib import Path
from typing import Dict, Iterable, List, Tuple


def parse_tuple_ints(s: str) -> Tuple[int, ...]:
    s = s.strip()
    if s.startswith("(") and s.endswith(")"):
        s = s[1:-1]
    if not s:
        return tuple()
    return tuple(int(x.strip()) for x in s.split(",") if x.strip())


def ceil_fraction(x: Fraction) -> int:
    return -(-x.numerator // x.denominator)


def load_kernel(kernel_path: Path):
    name = "lrc_multidiv_boundary_kernel"
    spec = importlib.util.spec_from_file_location(name, str(kernel_path))
    if spec is None or spec.loader is None:
        raise RuntimeError(f"failed to load kernel: {kernel_path}")
    mod = importlib.util.module_from_spec(spec)
    sys.modules[name] = mod
    spec.loader.exec_module(mod)
    return mod


def admissible_Ms(lo: int, hi: int, R: int) -> List[int]:
    return [m for m in range(lo, hi + 1) if gcd(m, R) == 1]


def lcm2(a: int, b: int) -> int:
    return a * b // gcd(a, b)


def lcm_list(vals: Iterable[int]) -> int:
    r = 1
    for v in vals:
        r = lcm2(r, int(v))
    return r


@dataclass
class TemplateState:
    template_id: str
    n: int
    d: int
    fixed: Tuple[int, ...]
    e_div: Tuple[int, ...]
    R: int
    phi_n: int
    checks: Dict[int, Dict[str, int]]


@dataclass
class OutRow:
    template_id: str
    n: int
    d: int
    fixed: str
    e_div: str
    L0: int
    R: int
    phi_n: int
    a_F: str
    b_F: str
    M0: int
    max_checked_M: int
    checked_count: int
    T_size_target: int
    phi_violations_in_target: int
    affine_lb_violations_in_target: int
    status: str


@dataclass
class OutCheck:
    template_id: str
    n: int
    d: int
    fixed: str
    e_div: str
    M: int
    R: int
    phi_n: int
    x0: int
    B_safe: int
    B_div: int
    B_div_components: int
    segment_count: int
    d2_lb_floor: int
    affine_lb_floor: int
    ok_affine_lb: int
    ok_phi: int
    source: str


def derive_affine(points: List[Tuple[int, int]], phi_n: int) -> Tuple[Fraction, Fraction, int]:
    """Find affine lower line y >= a*M+b on known points; optimize for smallest M0.

    Candidate slopes are positive pair slopes. For each slope a:
      b = min_i(y_i - a*M_i)
      M0 = ceil((phi_n - b)/a) clipped to >=1
    choose candidate with minimal M0, then largest a, then largest b.
    """
    pts = sorted(points)
    if len(pts) < 2:
        y0 = pts[0][1]
        a = Fraction(1, 1)
        b = Fraction(y0, 1) - a * Fraction(pts[0][0], 1)
        rhs = Fraction(phi_n, 1) - b
        M0 = 1 if rhs <= 0 else max(1, ceil_fraction(rhs / a))
        return a, b, M0

    slopes = set()
    for i in range(len(pts)):
        m1, y1 = pts[i]
        for j in range(i + 1, len(pts)):
            m2, y2 = pts[j]
            dm = m2 - m1
            if dm <= 0:
                continue
            dy = y2 - y1
            s = Fraction(dy, dm)
            if s > 0:
                slopes.add(s)

    if not slopes:
        # Degenerate fallback: tiny positive slope.
        a = Fraction(1, 10**6)
        b = min(Fraction(y) - a * Fraction(m) for m, y in pts)
        rhs = Fraction(phi_n, 1) - b
        M0 = 1 if rhs <= 0 else max(1, ceil_fraction(rhs / a))
        return a, b, M0

    best = None
    for a in sorted(slopes):
        b = min(Fraction(y) - a * Fraction(m) for m, y in pts)
        rhs = Fraction(phi_n, 1) - b
        M0 = 1 if rhs <= 0 else max(1, ceil_fraction(rhs / a))
        key = (M0, -a, -b)
        if best is None or key < best[0]:
            best = (key, a, b, M0)

    assert best is not None
    return best[1], best[2], best[3]


def affine_floor(a: Fraction, b: Fraction, M: int) -> int:
    v = a * Fraction(M, 1) + b
    return v.numerator // v.denominator


def build_states_from_checks(checks_csv: Path) -> Dict[str, TemplateState]:
    states: Dict[str, TemplateState] = {}
    with checks_csv.open(newline="", encoding="utf-8") as f:
        r = csv.DictReader(f)
        for row in r:
            tid = row["template_id"]
            n = int(row["n"])
            d = int(row["d"])
            fixed = parse_tuple_ints(row["fixed"])
            e_div = parse_tuple_ints(row["e_div"])
            M = int(row["M"])
            phi_n = int(row["phi_n"])
            R = int(row["R"])

            if tid not in states:
                states[tid] = TemplateState(
                    template_id=tid,
                    n=n,
                    d=d,
                    fixed=fixed,
                    e_div=e_div,
                    R=R,
                    phi_n=phi_n,
                    checks={},
                )

            states[tid].checks[M] = {
                "x0": int(row["x0"]),
                "B_safe": int(row["B_safe"]),
                "d2_lb_floor": int(row["d2_lb_floor"]),
                "B_div": int(row["B_div"]),
                "B_div_components": int(row["B_div_components"]),
                "segment_count": int(row["segment_count"]),
                "source": "existing",
            }
    return states


def extend_template_checks(state: TemplateState, run_one, m_target: int) -> int:
    current_max = max(state.checks)
    if m_target <= current_max:
        return 0

    added = 0
    for M in admissible_Ms(current_max + 1, m_target, state.R):
        out = run_one(state.n, list(state.fixed), list(state.e_div), M, False)
        state.checks[M] = {
            "x0": out.x0,
            "B_safe": out.B_safe,
            "d2_lb_floor": out.d2_lb_floor,
            "B_div": out.B_div,
            "B_div_components": out.B_div_components,
            "segment_count": out.segment_count,
            "source": "new",
        }
        added += 1
    return added


def write_outputs(out_dir: Path, tag: str, rows: List[OutRow], checks: List[OutCheck]) -> Tuple[Path, Path, Path]:
    rows_csv = out_dir / f"lrc_case2_multidiv_tcp_rows_{tag}.csv"
    checks_csv = out_dir / f"lrc_case2_multidiv_tcp_checks_{tag}.csv"
    summary_md = out_dir / f"lrc_case2_multidiv_tcp_summary_{tag}.md"

    with rows_csv.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=list(OutRow.__dataclass_fields__.keys()))
        w.writeheader()
        for r in sorted(rows, key=lambda x: (x.n, x.d, x.template_id)):
            w.writerow(asdict(r))

    with checks_csv.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=list(OutCheck.__dataclass_fields__.keys()))
        w.writeheader()
        for c in sorted(checks, key=lambda x: (x.n, x.d, x.template_id, x.M)):
            w.writerow(asdict(c))

    by_group: Dict[Tuple[int, int], List[OutRow]] = {}
    for r in rows:
        by_group.setdefault((r.n, r.d), []).append(r)

    with summary_md.open("w", encoding="utf-8") as f:
        f.write("# Multi-Divisible TCP Affine Builder Summary\n\n")
        f.write("- Coefficients (a_F,b_F) are derived from the D.2 diagnostic track.\n")
        f.write("- Scope warning: asymptotic validity beyond checked cap still requires theorem proof.\n\n")

        for (n, d), arr in sorted(by_group.items()):
            statuses = {}
            for r in arr:
                statuses[r.status] = statuses.get(r.status, 0) + 1
            f.write(f"## n={n}, |E_div|={d}\n")
            f.write(f"- templates: {len(arr)}\n")
            f.write(f"- max M0: {max(r.M0 for r in arr)}\n")
            f.write(f"- min M0: {min(r.M0 for r in arr)}\n")
            f.write(f"- max checked M: {max(r.max_checked_M for r in arr)}\n")
            f.write(f"- phi violations in target (sum): {sum(r.phi_violations_in_target for r in arr)}\n")
            f.write(f"- affine-LB violations in target (sum): {sum(r.affine_lb_violations_in_target for r in arr)}\n")
            for k, v in sorted(statuses.items()):
                f.write(f"- status `{k}`: {v}\n")
            f.write("\n")

        f.write("## Artifacts\n")
        f.write(f"- rows: `{rows_csv.name}`\n")
        f.write(f"- checks: `{checks_csv.name}`\n")
        f.write(f"- summary: `{summary_md.name}`\n")

    return rows_csv, checks_csv, summary_md


def main() -> None:
    ap = argparse.ArgumentParser(description="Build per-template affine TCP data for multi-divisible families")
    ap.add_argument("--checks-csv", type=str, required=True)
    ap.add_argument("--kernel-path", type=str, required=True)
    ap.add_argument("--m-cap-max", type=int, default=400)
    ap.add_argument("--max-templates", type=int, default=0)
    ap.add_argument("--tag", type=str, default="v1")
    ap.add_argument("--out-dir", type=str, default=".")
    args = ap.parse_args()

    states = build_states_from_checks(Path(args.checks_csv))
    tids = sorted(states)
    if args.max_templates > 0:
        tids = tids[: args.max_templates]

    kernel = load_kernel(Path(args.kernel_path))
    run_one = kernel.run_one

    out_rows: List[OutRow] = []
    out_checks: List[OutCheck] = []

    print(f"[build] templates={len(tids)} m_cap_max={args.m_cap_max}")

    for idx, tid in enumerate(tids, start=1):
        st = states[tid]

        # Iteratively extend up to M0 or m_cap_max.
        while True:
            points = sorted((m, v["d2_lb_floor"]) for m, v in st.checks.items())
            a, b, M0 = derive_affine(points, st.phi_n)
            max_checked = max(st.checks)

            target = min(args.m_cap_max, max(1, M0 - 1))
            if target <= max_checked:
                break
            added = extend_template_checks(st, run_one, target)
            if added == 0:
                break

        # Final coefficients after extension pass.
        points = sorted((m, v["d2_lb_floor"]) for m, v in st.checks.items())
        a, b, M0 = derive_affine(points, st.phi_n)

        target_max = min(args.m_cap_max, max(1, M0 - 1))
        target_set = admissible_Ms(1, target_max, st.R)

        phi_viol = 0
        lb_viol = 0

        for M in target_set:
            if M not in st.checks:
                extend_template_checks(st, run_one, M)
            rec = st.checks[M]
            lb = affine_floor(a, b, M)
            ok_lb = int(rec["d2_lb_floor"] >= lb)
            ok_phi = int(rec["x0"] >= st.phi_n)
            if ok_lb == 0:
                lb_viol += 1
            if ok_phi == 0:
                phi_viol += 1

            out_checks.append(
                OutCheck(
                    template_id=tid,
                    n=st.n,
                    d=st.d,
                    fixed="(" + ",".join(map(str, st.fixed)) + ")",
                    e_div="(" + ",".join(map(str, st.e_div)) + ")",
                    M=M,
                    R=st.R,
                    phi_n=st.phi_n,
                    x0=rec["x0"],
                    B_safe=rec["B_safe"],
                    B_div=rec["B_div"],
                    B_div_components=rec["B_div_components"],
                    segment_count=rec["segment_count"],
                    d2_lb_floor=rec["d2_lb_floor"],
                    affine_lb_floor=lb,
                    ok_affine_lb=ok_lb,
                    ok_phi=ok_phi,
                    source=rec["source"],
                )
            )

        status = "partial_tail_open"
        if M0 - 1 <= args.m_cap_max and phi_viol == 0 and lb_viol == 0:
            status = "finite_target_verified"
        elif phi_viol > 0:
            status = "phi_violation"
        elif lb_viol > 0:
            status = "affine_lb_violation"

        L0 = lcm_list(list(st.fixed) + list(st.e_div))
        out_rows.append(
            OutRow(
                template_id=tid,
                n=st.n,
                d=st.d,
                fixed="(" + ",".join(map(str, st.fixed)) + ")",
                e_div="(" + ",".join(map(str, st.e_div)) + ")",
                L0=L0,
                R=st.R,
                phi_n=st.phi_n,
                a_F=str(a),
                b_F=str(b),
                M0=M0,
                max_checked_M=max(st.checks),
                checked_count=len(st.checks),
                T_size_target=len(target_set),
                phi_violations_in_target=phi_viol,
                affine_lb_violations_in_target=lb_viol,
                status=status,
            )
        )

        if idx == 1 or idx % 25 == 0 or idx == len(tids):
            print(
                f"  [{idx}/{len(tids)}] n={st.n} d={st.d} fixed={st.fixed} e_div={st.e_div} "
                f"M0={M0} checked_max={max(st.checks)} status={status}"
            )

    out_dir = Path(args.out_dir)
    out_dir.mkdir(parents=True, exist_ok=True)
    rows_csv, checks_csv, summary_md = write_outputs(out_dir, args.tag, out_rows, out_checks)

    print("\n[done]")
    print(f"rows:    {rows_csv}")
    print(f"checks:  {checks_csv}")
    print(f"summary: {summary_md}")


if __name__ == "__main__":
    main()
