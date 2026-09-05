#!/usr/bin/env python3
"""Execute theorem dependency + refuter task pack.

Produces for each claim:
- reports/theorem/<claim_id>/dependency_graph.md
- reports/theorem/<claim_id>/assumption_inventory.md
- reports/theorem/<claim_id>/refuter_results.md

Also updates task pack CSV statuses and writes cycle summary.
"""

from __future__ import annotations

import argparse
import csv
import json
import re
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, List, Sequence, Tuple


FORMAL_PATTERNS = [
    re.compile(r"^\s*(theorem|lemma|proposition|claim|corollary)\b[:\s-]*(.*)$", re.IGNORECASE),
    re.compile(r"\\begin\{(theorem|lemma|proposition|corollary)\}", re.IGNORECASE),
]

ASSUMPTION_PATTERNS = [
    re.compile(r"\bassume\b([^\n\.]*)", re.IGNORECASE),
    re.compile(r"\bsuppose\b([^\n\.]*)", re.IGNORECASE),
    re.compile(r"\blet\b([^\n\.]*)", re.IGNORECASE),
    re.compile(r"\bfor all\b([^\n\.]*)", re.IGNORECASE),
    re.compile(r"\bthere exists\b([^\n\.]*)", re.IGNORECASE),
]

SYMBOL_RE = re.compile(r"\b(phi|delta|epsilon|sigma|k|n|v_i|vj|vi|t)\b", re.IGNORECASE)


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Run theorem dependency/refuter task pack")
    p.add_argument("--task-pack", required=True, help="Input task pack CSV")
    p.add_argument("--claims", required=True, help="Claims CSV")
    p.add_argument("--output-root", required=True, help="Root path for theorem outputs")
    p.add_argument("--task-pack-out", required=True, help="Updated task pack CSV output")
    p.add_argument("--summary-md", required=True, help="Summary markdown path")
    p.add_argument("--summary-csv", required=True, help="Summary CSV path")
    return p.parse_args()


def read_csv(path: Path) -> List[Dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as f:
        return list(csv.DictReader(f))


def write_csv(path: Path, rows: List[Dict[str, str]], fieldnames: Sequence[str] | None = None) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    if not rows:
        path.write_text("", encoding="utf-8")
        return
    if fieldnames is None:
        seen: List[str] = []
        for r in rows:
            for k in r.keys():
                if k not in seen:
                    seen.append(k)
        fieldnames = seen
    with path.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fieldnames)
        w.writeheader()
        w.writerows(rows)


def read_text_file(path: Path) -> str:
    suf = path.suffix.lower()
    if suf in {".txt", ".md", ".tex", ".csv", ".json", ".py", ".html"}:
        return path.read_text(encoding="utf-8", errors="replace")
    # Fallback for uncommon text-like files.
    return path.read_text(encoding="utf-8", errors="replace")


def extract_statements(text: str) -> List[str]:
    lines = text.splitlines()
    out: List[str] = []
    for ln in lines:
        clean = ln.strip()
        if not clean:
            continue
        for pat in FORMAL_PATTERNS:
            m = pat.search(clean)
            if m:
                label = m.group(1).lower()
                tail = (m.group(2) if len(m.groups()) >= 2 and m.group(2) is not None else "").strip()
                out.append(f"{label}: {tail}".strip())
                break
    if out:
        return out[:24]

    # Fallback: treat heading-like lines as pseudo-statements.
    pseudo = []
    for ln in lines:
        clean = ln.strip()
        if len(clean) < 8:
            continue
        if clean.startswith("#") or clean.endswith(":") or clean.isupper():
            pseudo.append(f"section_claim: {clean[:140]}")
        if len(pseudo) >= 12:
            break

    if pseudo:
        return pseudo

    # Last resort: one root claim from first non-empty chunk.
    for ln in lines:
        clean = ln.strip()
        if clean:
            return [f"root_claim: {clean[:180]}"]
    return ["root_claim: unavailable"]


def build_dependency_edges(statements: Sequence[str]) -> List[Tuple[str, str, str]]:
    # Create node IDs and simple chained edges + keyword links.
    nodes = [f"S{i+1}" for i in range(len(statements))]
    edges: List[Tuple[str, str, str]] = []

    for i in range(len(nodes) - 1):
        edges.append((nodes[i], nodes[i + 1], "sequential_dependency"))

    # Weak lexical linkage: statements mentioning lemma/theorem refer to prior nodes.
    for i, st in enumerate(statements):
        s = st.lower()
        if any(k in s for k in ["lemma", "theorem", "proposition", "corollary"]):
            if i > 0:
                edges.append((nodes[max(0, i - 1)], nodes[i], "formal_reference"))

    # dedupe
    dedup = []
    seen = set()
    for e in edges:
        if e not in seen:
            seen.add(e)
            dedup.append(e)
    return dedup


def extract_assumptions(text: str) -> List[str]:
    out: List[str] = []
    for pat in ASSUMPTION_PATTERNS:
        for m in pat.finditer(text):
            frag = (m.group(0) or "").strip()
            if frag:
                out.append(frag[:220])
    # Keep unique order.
    uniq: List[str] = []
    for a in out:
        if a not in uniq:
            uniq.append(a)
    return uniq[:30]


def refuter_checks(text: str, statements: Sequence[str], assumptions: Sequence[str]) -> List[Dict[str, str]]:
    checks: List[Dict[str, str]] = []
    low = text.lower()

    # 1) Definition coverage for common symbols.
    symbols = sorted({m.group(1).lower() for m in SYMBOL_RE.finditer(text)})
    def_count = low.count("define") + low.count("definition") + low.count("let ")
    missing_defs = symbols and def_count == 0
    checks.append(
        {
            "check": "symbol_definition_coverage",
            "result": "fail" if missing_defs else "pass",
            "severity": "high" if missing_defs else "low",
            "details": f"symbols={symbols}; definition_markers={def_count}",
        }
    )

    # 2) Boundary condition presence.
    boundary_terms = ["n=", "n <=", "base case", "edge case", "boundary", "k=", "n = 1", "n = 2"]
    has_boundary = any(t in low for t in boundary_terms)
    checks.append(
        {
            "check": "boundary_case_coverage",
            "result": "pass" if has_boundary else "warn",
            "severity": "medium" if not has_boundary else "low",
            "details": "boundary terms present" if has_boundary else "no explicit boundary/base-case markers found",
        }
    )

    # 3) Empirical-only evidence masquerading as theorem.
    empirical_terms = ["sample", "simulation", "experiment", "csv", "runtime", "dataset"]
    empirical_hits = sum(1 for t in empirical_terms if t in low)
    theorem_markers = sum(1 for t in ["theorem", "lemma", "proof", "qed"] if t in low)
    empirical_overreach = empirical_hits >= 2 and theorem_markers <= 1
    checks.append(
        {
            "check": "empirical_overreach_risk",
            "result": "fail" if empirical_overreach else "pass",
            "severity": "high" if empirical_overreach else "low",
            "details": f"empirical_hits={empirical_hits}; theorem_markers={theorem_markers}",
        }
    )

    # 4) Dependency depth sufficiency.
    dep_ok = len(statements) >= 2
    checks.append(
        {
            "check": "dependency_depth",
            "result": "pass" if dep_ok else "warn",
            "severity": "medium" if not dep_ok else "low",
            "details": f"statement_nodes={len(statements)}",
        }
    )

    # 5) Assumption explicitness.
    has_assumptions = len(assumptions) > 0
    checks.append(
        {
            "check": "assumption_explicitness",
            "result": "pass" if has_assumptions else "warn",
            "severity": "medium" if not has_assumptions else "low",
            "details": f"assumption_count={len(assumptions)}",
        }
    )

    return checks


def decide_status(checks: Sequence[Dict[str, str]], statements: Sequence[str]) -> Tuple[str, bool, str]:
    fails = [c for c in checks if c["result"] == "fail"]
    warns = [c for c in checks if c["result"] == "warn"]

    unresolved_critical = any(c["severity"] == "high" and c["result"] == "fail" for c in checks)
    if unresolved_critical:
        return "needs_followup", True, "high_severity_refuter_failures"
    if len(statements) < 2:
        return "needs_followup", True, "insufficient_dependency_structure"
    if len(warns) >= 2:
        return "needs_followup", False, "multiple_medium_risks"
    return "executed", False, "criteria_pass_first_pass"


def write_dependency_graph(path: Path, claim_id: str, statements: Sequence[str], edges: Sequence[Tuple[str, str, str]]) -> None:
    lines: List[str] = []
    lines.append(f"# Dependency Graph: {claim_id}")
    lines.append("")
    lines.append(f"Generated: {utc_now()}")
    lines.append("")
    lines.append("## Nodes")
    for i, st in enumerate(statements, start=1):
        lines.append(f"- S{i}: {st}")
    lines.append("")
    lines.append("## Edges")
    if not edges:
        lines.append("- none")
    else:
        for s, t, k in edges:
            lines.append(f"- {s} -> {t} ({k})")
    lines.append("")
    lines.append("## Machine Graph (Mermaid)")
    lines.append("```mermaid")
    lines.append("graph TD")
    for i, st in enumerate(statements, start=1):
        label = st.replace('"', "'")[:80]
        lines.append(f"  S{i}[\"{label}\"]")
    for s, t, k in edges:
        lines.append(f"  {s} -->|{k}| {t}")
    lines.append("```")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_assumptions(path: Path, claim_id: str, assumptions: Sequence[str], text: str) -> None:
    symbol_hits = Counter(m.group(1).lower() for m in SYMBOL_RE.finditer(text))
    lines: List[str] = []
    lines.append(f"# Assumption Inventory: {claim_id}")
    lines.append("")
    lines.append(f"Generated: {utc_now()}")
    lines.append("")
    lines.append("## Explicit Assumptions")
    if assumptions:
        for i, a in enumerate(assumptions, start=1):
            lines.append(f"{i}. {a}")
    else:
        lines.append("1. No explicit assumption marker found in source text.")
    lines.append("")
    lines.append("## Symbol Frequency (heuristic)")
    if symbol_hits:
        for k, v in sorted(symbol_hits.items()):
            lines.append(f"- {k}: {v}")
    else:
        lines.append("- none")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def write_refuter(path: Path, claim_id: str, checks: Sequence[Dict[str, str]], status: str, unresolved_critical: bool, rationale: str) -> None:
    lines: List[str] = []
    lines.append(f"# Refuter Results: {claim_id}")
    lines.append("")
    lines.append(f"Generated: {utc_now()}")
    lines.append(f"Execution status: {status}")
    lines.append(f"Unresolved critical nodes: {'yes' if unresolved_critical else 'no'}")
    lines.append(f"Rationale: {rationale}")
    lines.append("")
    lines.append("## Checks")
    lines.append("| Check | Result | Severity | Details |")
    lines.append("|---|---|---|---|")
    for c in checks:
        lines.append(f"| {c['check']} | {c['result']} | {c['severity']} | {c['details']} |")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    args = parse_args()

    tasks = read_csv(Path(args.task_pack))
    claims = read_csv(Path(args.claims))
    claims_map = {r.get("claim_id", ""): r for r in claims}

    out_root = Path(args.output_root)

    result_rows: List[Dict[str, str]] = []
    updated_tasks: List[Dict[str, str]] = []

    for t in tasks:
        status_in = (t.get("status") or "").strip().lower()
        if status_in not in {"queued", "retry", ""}:
            updated_tasks.append(dict(t))
            continue

        claim_id = t.get("claim_id", "")
        task_id = t.get("task_id", "")
        source_path = Path(t.get("source_path", ""))
        claim = claims_map.get(claim_id, {})

        claim_dir = out_root / claim_id
        dep_path = claim_dir / "dependency_graph.md"
        asm_path = claim_dir / "assumption_inventory.md"
        ref_path = claim_dir / "refuter_results.md"

        if not source_path.exists():
            row = dict(t)
            row["status"] = "error"
            row["updated_utc"] = utc_now()
            row["execution_notes"] = f"missing_source:{source_path}"
            row["output_artifacts"] = str(claim_dir)
            updated_tasks.append(row)

            result_rows.append(
                {
                    "task_id": task_id,
                    "claim_id": claim_id,
                    "status": "error",
                    "unresolved_critical_nodes": "yes",
                    "checks_passed": "0",
                    "checks_warn": "0",
                    "checks_failed": "1",
                    "rationale": "missing_source",
                    "output_dir": str(claim_dir),
                    "updated_utc": utc_now(),
                }
            )
            continue

        text = read_text_file(source_path)
        statements = extract_statements(text)
        edges = build_dependency_edges(statements)
        assumptions = extract_assumptions(text)
        checks = refuter_checks(text, statements, assumptions)
        status, unresolved_critical, rationale = decide_status(checks, statements)

        write_dependency_graph(dep_path, claim_id, statements, edges)
        write_assumptions(asm_path, claim_id, assumptions, text)
        write_refuter(ref_path, claim_id, checks, status, unresolved_critical, rationale)

        c_pass = sum(1 for c in checks if c["result"] == "pass")
        c_warn = sum(1 for c in checks if c["result"] == "warn")
        c_fail = sum(1 for c in checks if c["result"] == "fail")

        row = dict(t)
        row["status"] = status
        row["updated_utc"] = utc_now()
        row["execution_notes"] = rationale
        row["output_artifacts"] = f"{dep_path}|{asm_path}|{ref_path}"
        row["checks_passed"] = str(c_pass)
        row["checks_warn"] = str(c_warn)
        row["checks_failed"] = str(c_fail)
        row["unresolved_critical_nodes"] = "yes" if unresolved_critical else "no"
        updated_tasks.append(row)

        result_rows.append(
            {
                "task_id": task_id,
                "claim_id": claim_id,
                "status": status,
                "unresolved_critical_nodes": "yes" if unresolved_critical else "no",
                "checks_passed": str(c_pass),
                "checks_warn": str(c_warn),
                "checks_failed": str(c_fail),
                "rationale": rationale,
                "output_dir": str(claim_dir),
                "updated_utc": utc_now(),
            }
        )

    # outputs
    write_csv(Path(args.task_pack_out), updated_tasks)
    write_csv(
        Path(args.summary_csv),
        result_rows,
        fieldnames=[
            "task_id",
            "claim_id",
            "status",
            "unresolved_critical_nodes",
            "checks_passed",
            "checks_warn",
            "checks_failed",
            "rationale",
            "output_dir",
            "updated_utc",
        ],
    )

    status_counts = Counter(r["status"] for r in result_rows)
    unresolved_count = sum(1 for r in result_rows if r["unresolved_critical_nodes"] == "yes")

    lines: List[str] = []
    lines.append("# Theorem Dependency/Refuter Pack Execution")
    lines.append("")
    lines.append(f"Generated: {utc_now()}")
    lines.append(f"Tasks executed: {len(result_rows)}")
    lines.append(f"Unresolved critical nodes: {unresolved_count}")
    lines.append("")
    lines.append("## Status Counts")
    for k, v in sorted(status_counts.items()):
        lines.append(f"- {k}: {v}")
    lines.append("")
    lines.append("## Task Results")
    lines.append("| Task | Claim | Status | Critical | Checks (p/w/f) | Rationale |")
    lines.append("|---|---|---|---|---|---|")
    for r in result_rows:
        lines.append(
            f"| {r['task_id']} | {r['claim_id']} | {r['status']} | {r['unresolved_critical_nodes']} | "
            f"{r['checks_passed']}/{r['checks_warn']}/{r['checks_failed']} | {r['rationale']} |"
        )

    md_path = Path(args.summary_md)
    md_path.parent.mkdir(parents=True, exist_ok=True)
    md_path.write_text("\n".join(lines) + "\n", encoding="utf-8")

    print(f"wrote_task_pack={args.task_pack_out}")
    print(f"wrote_summary_md={args.summary_md}")
    print(f"wrote_summary_csv={args.summary_csv} rows={len(result_rows)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
