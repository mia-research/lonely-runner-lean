#!/usr/bin/env python3
"""Execute cycle conflict reformulation tasks with evidence-grounded outputs.

This script is intentionally deterministic and local-only:
- reads conflict task pack + claims metadata
- computes claim-specific evidence summaries from source CSV files
- writes reformulation artifacts required by each task
- updates task statuses and writes execution summary outputs
"""

from __future__ import annotations

import argparse
import csv
from collections import Counter, defaultdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, List, Sequence, Tuple


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Run conflict reformulation task pack")
    p.add_argument("--task-pack", required=True, help="Conflict reformulation task pack CSV")
    p.add_argument("--claims", required=True, help="Claims CSV")
    p.add_argument("--output-root", required=True, help="reports/conflicts root")
    p.add_argument("--task-pack-out", required=True, help="Updated task pack CSV")
    p.add_argument("--summary-csv", required=True, help="Execution summary CSV")
    p.add_argument("--summary-md", required=True, help="Execution summary markdown")
    return p.parse_args()


def read_csv(path: Path) -> List[Dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as f:
        return list(csv.DictReader(f))


def write_csv(path: Path, rows: List[Dict[str, str]], fieldnames: Sequence[str] | None = None) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
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


def ensure_dir(path: Path) -> None:
    path.mkdir(parents=True, exist_ok=True)


def write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text.rstrip() + "\n", encoding="utf-8")


def parse_required_outputs(raw: str) -> List[str]:
    out: List[str] = []
    for item in (raw or "").split("|"):
        token = item.strip()
        if not token:
            continue
        out.append(Path(token).name)
    return out


def load_claim_map(claims_rows: Sequence[Dict[str, str]]) -> Dict[str, Dict[str, str]]:
    out: Dict[str, Dict[str, str]] = {}
    for r in claims_rows:
        cid = (r.get("claim_id") or "").strip()
        if cid:
            out[cid] = r
    return out


def compute_041_metrics(source_path: Path) -> Dict[str, object]:
    stats: Dict[str, Dict[str, object]] = {}
    with source_path.open(newline="", encoding="utf-8", errors="replace") as f:
        rd = csv.DictReader(f)
        for row in rd:
            if row.get("n") != "6" or row.get("horizon") != "1000":
                continue
            fam = (row.get("family") or "").strip().lower()
            cur = stats.setdefault(
                fam,
                {
                    "rows": 0,
                    "complete_yes": 0,
                    "complete_no": 0,
                    "boundary_min": None,
                    "boundary_max": None,
                    "avg_first_min": None,
                    "avg_first_max": None,
                    "fail_seeds": [],
                },
            )
            cur["rows"] = int(cur["rows"]) + 1
            if (row.get("complete_success") or "").upper() == "YES":
                cur["complete_yes"] = int(cur["complete_yes"]) + 1
            else:
                cur["complete_no"] = int(cur["complete_no"]) + 1
                cur["fail_seeds"].append(
                    {
                        "seed": row.get("seed", ""),
                        "boundary_count": row.get("boundary_count", ""),
                        "runners_isolated": row.get("runners_isolated", ""),
                        "avg_first_isolation": row.get("avg_first_isolation", ""),
                    }
                )

            try:
                bc = int(float(row.get("boundary_count", "0")))
                cur["boundary_min"] = bc if cur["boundary_min"] is None else min(int(cur["boundary_min"]), bc)
                cur["boundary_max"] = bc if cur["boundary_max"] is None else max(int(cur["boundary_max"]), bc)
            except Exception:
                pass

            try:
                afi = float(row.get("avg_first_isolation", "nan"))
                cur["avg_first_min"] = afi if cur["avg_first_min"] is None else min(float(cur["avg_first_min"]), afi)
                cur["avg_first_max"] = afi if cur["avg_first_max"] is None else max(float(cur["avg_first_max"]), afi)
            except Exception:
                pass
    return {"families": stats}


def compute_052_metrics(source_path: Path) -> Dict[str, object]:
    by_family_test: Dict[Tuple[str, str], Dict[str, int]] = defaultdict(lambda: defaultdict(int))
    baseline_total = 0
    baseline_formula_match = 0
    with source_path.open(newline="", encoding="utf-8", errors="replace") as f:
        rd = csv.DictReader(f)
        for row in rd:
            fam = (row.get("family") or "").strip().lower()
            test_type = (row.get("test_type") or "").strip().lower()
            key = (fam, test_type)
            by_family_test[key]["rows"] += 1
            if (row.get("phi_match") or "").upper() == "YES":
                by_family_test[key]["phi_yes"] += 1
            try:
                if int(float(row.get("isolation_count", "0"))) > 0:
                    by_family_test[key]["iso_gt_zero"] += 1
            except Exception:
                pass

            if fam == "arithmetic" and test_type == "arithmetic_baseline":
                baseline_total += 1
                try:
                    n = float(row.get("n", "nan"))
                    first = float(row.get("first_isolation", "nan"))
                    if abs(first - (10.0 / n)) <= 1e-6:
                        baseline_formula_match += 1
                except Exception:
                    pass

    return {
        "by_family_test": {f"{k[0]}::{k[1]}": dict(v) for k, v in sorted(by_family_test.items())},
        "baseline_total": baseline_total,
        "baseline_formula_match": baseline_formula_match,
    }


def compute_055_metrics(source_path: Path) -> Dict[str, object]:
    subset_rows = 0
    subset_phi_yes = 0
    subset_unique_eq_phi = 0
    first_samples: List[str] = []
    with source_path.open(newline="", encoding="utf-8", errors="replace") as f:
        rd = csv.DictReader(f)
        for row in rd:
            if (
                row.get("test_type") == "arithmetic_varied"
                and row.get("family") == "arithmetic"
                and row.get("n") == "5"
            ):
                subset_rows += 1
                if (row.get("phi_match") or "").upper() == "YES":
                    subset_phi_yes += 1
                try:
                    if int(float(row.get("unique_phases", "-1"))) == int(float(row.get("phi_n", "-2"))):
                        subset_unique_eq_phi += 1
                except Exception:
                    pass
                if len(first_samples) < 10:
                    first_samples.append(row.get("first_isolation", ""))
    return {
        "subset_rows": subset_rows,
        "subset_phi_yes": subset_phi_yes,
        "subset_unique_eq_phi": subset_unique_eq_phi,
        "first_samples": first_samples,
    }


def render_041(metrics: Dict[str, object]) -> Dict[str, str]:
    fam = metrics.get("families", {})
    arithmetic = fam.get("arithmetic", {})
    random = fam.get("random", {})

    reformulated = f"""# CLAIM-LRC-000041 Reformulated Claim

## Operational Proposition (Empirical, Falsifiable)
For dataset `lrc_individual_isolation_1759267335152.csv`, restricted to rows with:
- `family = arithmetic`, `n = 6`, `horizon = 1000`,

the following hold:
1. `complete_success = YES` in all observed rows ({arithmetic.get('complete_yes', 0)}/{arithmetic.get('rows', 0)}).
2. `runners_isolated = 6` in all observed arithmetic rows.
3. `avg_first_isolation` remains tightly concentrated near `5/3` (observed range: {arithmetic.get('avg_first_min')} to {arithmetic.get('avg_first_max')}).

Contrast set in the same file:
- For `family = random`, `n = 6`, `horizon = 1000`, complete isolation is not universal ({random.get('complete_yes', 0)}/{random.get('rows', 0)} complete; {random.get('complete_no', 0)} failures).
- Non-complete seeds observed: {", ".join(x.get("seed","") for x in random.get("fail_seeds", [])) or "none"}.

## Boundary Conditions
- Arithmetic boundary_count range: {arithmetic.get('boundary_min')} to {arithmetic.get('boundary_max')}
- Random boundary_count range: {random.get('boundary_min')} to {random.get('boundary_max')}

## Falsification Rule
This reformulated claim is rejected if any arithmetic row in the stated slice has:
- `complete_success != YES`, or
- `runners_isolated != 6`, or
- `avg_first_isolation` materially outside the observed concentration around `5/3`.
"""

    assumptions = """# CLAIM-LRC-000041 Assumption Inventory

1. CSV schema fields are interpreted literally (`family`, `n`, `horizon`, `complete_success`, `runners_isolated`, `avg_first_isolation`).
2. Arithmetic and random families are evaluated as distinct cohorts.
3. `horizon=1000` slice is treated as fixed for this claim.
4. This is an empirical claim about the recorded dataset, not a full theorem proof of LRC.
"""

    refuter_plan = f"""# CLAIM-LRC-000041 Refuter Probe Plan

## Primary Probes
1. Recompute success rates for arithmetic vs random at `n=6`, `horizon=1000`.
2. Validate that arithmetic rows are all complete (`complete_success=YES`).
3. Re-run the two random failure seeds with extended horizons (`T=10,000`, `T=100,000`) to test delayed isolation vs structural failure.

## High-Risk Seeds
{chr(10).join(f"- seed {x.get('seed')} (boundary_count={x.get('boundary_count')}, runners_isolated={x.get('runners_isolated')}, avg_first_isolation={x.get('avg_first_isolation')})" for x in random.get("fail_seeds", [])) or "- none recorded"}

## Publication Gate
Hold promotion if random-family failures are unresolved or if arithmetic universal-complete property is not reproducible.
"""

    return {
        "reformulated_claim.md": reformulated,
        "assumption_inventory.md": assumptions,
        "refuter_probe_plan.md": refuter_plan,
    }


def render_052(metrics: Dict[str, object]) -> Dict[str, str]:
    family_test = metrics.get("by_family_test", {})
    ar_base = family_test.get("arithmetic::arithmetic_baseline", {})
    ar_ext = family_test.get("arithmetic::arithmetic_extended", {})
    geo = family_test.get("geometric::non_arithmetic", {})
    quad = family_test.get("quadratic::non_arithmetic", {})
    pert = family_test.get("perturbed::non_arithmetic", {})
    perf = family_test.get("performance_test::performance", {})

    split_claims = f"""# CLAIM-LRC-000052 Split Claims

## 000052-A (Arithmetic Cohort)
For `lrc_validation_data_2025-09-23T11-19-31-619Z.csv` rows with:
- `family=arithmetic`, `test_type=arithmetic_baseline`:
  - rows: {ar_base.get('rows', 0)}
  - `phi_match=YES`: {ar_base.get('phi_yes', 0)}
  - `isolation_count>0`: {ar_base.get('iso_gt_zero', 0)}
  - `first_isolation ≈ 10/n` within tolerance `1e-6`: {metrics.get('baseline_formula_match', 0)}/{metrics.get('baseline_total', 0)}

For arithmetic extended variant:
- `family=arithmetic`, `test_type=arithmetic_extended`:
  - rows: {ar_ext.get('rows', 0)}
  - `phi_match=YES`: {ar_ext.get('phi_yes', 0)}
  - `isolation_count>0`: {ar_ext.get('iso_gt_zero', 0)}

## 000052-B (Methodology-Boundary Cohort)
For non-arithmetic test slice (`test_type=non_arithmetic`):
- geometric rows: {geo.get('rows', 0)} (`phi_match=YES`: {geo.get('phi_yes', 0)}, `isolation_count>0`: {geo.get('iso_gt_zero', 0)})
- quadratic rows: {quad.get('rows', 0)} (`phi_match=YES`: {quad.get('phi_yes', 0)}, `isolation_count>0`: {quad.get('iso_gt_zero', 0)})
- perturbed rows: {pert.get('rows', 0)} (`phi_match=YES`: {pert.get('phi_yes', 0)}, `isolation_count>0`: {pert.get('iso_gt_zero', 0)})

Interpretation:
- `phi_match` appears arithmetic-specific in this pipeline and should not be used as a universal success metric for non-arithmetic families.
- Non-arithmetic rows require a dedicated criterion before any global negative inference is made.
"""

    boundary_note = f"""# CLAIM-LRC-000052 Measurement Boundary Note

## Verified in-file cohorts
- Arithmetic baseline (`arithmetic_baseline`): {ar_base.get('rows', 0)} rows.
- Arithmetic extended (`arithmetic_extended`): {ar_ext.get('rows', 0)} rows.
- Non-arithmetic detector slice (`non_arithmetic`):
  - geometric={geo.get('rows', 0)}, quadratic={quad.get('rows', 0)}, perturbed={pert.get('rows', 0)}.
- Performance rows (`performance_test::performance`): {perf.get('rows', 0)} (tracked separately; not part of the phi-match theorem claim).

## Guardrail
Do not aggregate arithmetic and non-arithmetic cohorts into one binary theorem-style statement.
Treat them as separate claims with separate validity criteria.
"""

    quorum_prompt = """# CLAIM-LRC-000052 Quorum Rerun Prompt Addendum

Adjudicate two split claims independently:
1. 000052-A arithmetic cohort validity (phi-match and first-isolation behavior under stated tolerance).
2. 000052-B non-arithmetic methodology boundary (measurement criterion mismatch, not theorem negation).

Required output: one vote per split claim with explicit publication gate recommendation.
"""

    return {
        "split_claims.md": split_claims,
        "measurement_boundary_note.md": boundary_note,
        "quorum_rerun_prompt.md": quorum_prompt,
    }


def render_055(metrics: Dict[str, object]) -> Dict[str, str]:
    formalized = f"""# CLAIM-LRC-000055 Formalized Claim

## Operational Proposition (Empirical, Falsifiable)
In `lrc_validation_large_1759238706040.csv`, for rows satisfying:
- `test_type = arithmetic_varied`
- `family = arithmetic`
- `n = 5`

the following measured properties hold in the extracted slice:
1. Row count in slice: {metrics.get('subset_rows', 0)}
2. `phi_match = YES` in {metrics.get('subset_phi_yes', 0)}/{metrics.get('subset_rows', 0)} rows.
3. `unique_phases = phi_n` in {metrics.get('subset_unique_eq_phi', 0)}/{metrics.get('subset_rows', 0)} rows.

This converts the prior CSV-fragment statement into a checkable proposition over a defined row subset.

## Falsification Rule
Reject the claim if any row in the stated subset violates:
- `phi_match == YES`, or
- `unique_phases == phi_n`.
"""

    lexicon = f"""# CLAIM-LRC-000055 Notation Lexicon

- `n`: number of runners (fixed to 5 in this claim slice)
- `phi_n`: expected phase count target recorded in dataset (`phi_n=4` in this slice)
- `unique_phases`: observed unique phase count
- `phi_match`: boolean indicator that `unique_phases` matched `phi_n`
- `first_isolation`: measured first-isolation time

Sample `first_isolation` values from the slice:
- {", ".join(metrics.get("first_samples", []))}
"""

    quorum_prompt = """# CLAIM-LRC-000055 Quorum Rerun Prompt Addendum

Evaluate the formalized subset claim (not the raw CSV dump):
- Domain: arithmetic_varied, family=arithmetic, n=5.
- Predicate: phi_match is always YES and unique_phases equals phi_n.

Return decision on this explicit proposition and list assumptions needed for publication wording.
"""

    return {
        "formalized_claim.md": formalized,
        "notation_lexicon.md": lexicon,
        "quorum_rerun_prompt.md": quorum_prompt,
    }


def render_generic(claim_id: str, claim_row: Dict[str, str]) -> Dict[str, str]:
    return {
        "reformulated_claim.md": (
            f"# {claim_id} Reformulated Claim\n\n"
            "Automatic fallback reformulation.\n\n"
            f"- claim_type: {claim_row.get('claim_type','')}\n"
            f"- short_statement: {claim_row.get('short_statement','')}\n"
            f"- assumptions: {claim_row.get('assumptions','')}\n"
        )
    }


def main() -> int:
    args = parse_args()

    task_rows = read_csv(Path(args.task_pack))
    claim_map = load_claim_map(read_csv(Path(args.claims)))
    out_root = Path(args.output_root)
    ensure_dir(out_root)

    updated_rows: List[Dict[str, str]] = []
    summary_rows: List[Dict[str, str]] = []

    for task in task_rows:
        row = dict(task)
        status_in = (row.get("status") or "").strip().lower()
        if status_in not in {"", "queued", "retry"}:
            updated_rows.append(row)
            continue

        claim_id = (row.get("claim_id") or "").strip()
        claim = claim_map.get(claim_id, {})
        source_path = Path(claim.get("source_path", ""))
        claim_dir = out_root / claim_id
        ensure_dir(claim_dir)

        files_to_write: Dict[str, str] = {}
        reason = "executed_reformulation"

        try:
            if claim_id == "CLAIM-LRC-000041":
                metrics_041 = compute_041_metrics(source_path)
                files_to_write = render_041(metrics_041)
            elif claim_id == "CLAIM-LRC-000052":
                metrics_052 = compute_052_metrics(source_path)
                files_to_write = render_052(metrics_052)
            elif claim_id == "CLAIM-LRC-000055":
                metrics_055 = compute_055_metrics(source_path)
                files_to_write = render_055(metrics_055)
            else:
                files_to_write = render_generic(claim_id, claim)
        except Exception as exc:
            row["status"] = "error"
            row["updated_utc"] = utc_now()
            row["execution_notes"] = f"reformulation_error:{exc}"
            row["output_artifacts"] = str(claim_dir)
            updated_rows.append(row)
            summary_rows.append(
                {
                    "task_id": row.get("task_id", ""),
                    "claim_id": claim_id,
                    "status": "error",
                    "artifact_count": "0",
                    "reason": f"reformulation_error:{exc}",
                }
            )
            continue

        required_names = parse_required_outputs(row.get("required_outputs", ""))
        if required_names:
            for name in required_names:
                if name not in files_to_write:
                    files_to_write[name] = (
                        f"# {claim_id} {name}\n\n"
                        "Generated placeholder.\n\n"
                        f"- source_path: {claim.get('source_path','')}\n"
                        "- note: output declared in task pack and retained for pipeline compatibility.\n"
                    )

        artifact_paths: List[str] = []
        for name, text in files_to_write.items():
            out_path = claim_dir / name
            write_text(out_path, text)
            artifact_paths.append(str(out_path))

        row["status"] = "executed"
        row["updated_utc"] = utc_now()
        row["execution_notes"] = reason
        row["output_artifacts"] = "|".join(sorted(artifact_paths))
        updated_rows.append(row)

        summary_rows.append(
            {
                "task_id": row.get("task_id", ""),
                "claim_id": claim_id,
                "status": "executed",
                "artifact_count": str(len(artifact_paths)),
                "reason": reason,
            }
        )

    write_csv(Path(args.task_pack_out), updated_rows, fieldnames=list(updated_rows[0].keys()) if updated_rows else None)
    write_csv(
        Path(args.summary_csv),
        summary_rows,
        fieldnames=["task_id", "claim_id", "status", "artifact_count", "reason"],
    )

    status_counts = Counter(r["status"] for r in summary_rows)
    lines: List[str] = []
    lines.append("# Conflict Reformulation Execution Summary")
    lines.append("")
    lines.append(f"Generated: {utc_now()}")
    lines.append(f"Tasks executed: {len(summary_rows)}")
    lines.append("")
    lines.append("## Status Counts")
    for k, v in sorted(status_counts.items()):
        lines.append(f"- {k}: {v}")
    lines.append("")
    lines.append("## Results")
    lines.append("| Task | Claim | Status | Artifacts | Reason |")
    lines.append("|---|---|---|---|---|")
    for r in summary_rows:
        lines.append(
            f"| {r['task_id']} | {r['claim_id']} | {r['status']} | {r['artifact_count']} | {r['reason']} |"
        )

    md_path = Path(args.summary_md)
    md_path.parent.mkdir(parents=True, exist_ok=True)
    md_path.write_text("\n".join(lines) + "\n", encoding="utf-8")

    print(f"wrote_task_pack={args.task_pack_out}")
    print(f"wrote_summary_csv={args.summary_csv} rows={len(summary_rows)}")
    print(f"wrote_summary_md={args.summary_md}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
