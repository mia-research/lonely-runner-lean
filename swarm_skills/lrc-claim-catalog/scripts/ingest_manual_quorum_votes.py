#!/usr/bin/env python3
"""Validate and ingest manual quorum votes into task pack status.

This script expects a manual packet CSV plus manual vote JSON files.
It validates schema, checks claim/provider consistency, and promotes blocked
quorum tasks to executed_live when cross-provider quorum is satisfied.
"""

from __future__ import annotations

import argparse
import csv
import json
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

ALLOWED_STATUS = {"approve_promote", "approve_with_caveats", "escalate"}
ALLOWED_GATE = {"promote", "hold", "escalate"}
REQUIRED_KEYS = {
    "claim_id",
    "provider",
    "status_class",
    "confidence",
    "rationale",
    "critical_risks",
    "publication_gate_recommendation",
    "notes",
    "submitted_utc",
}


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Ingest manual quorum votes")
    p.add_argument("--task-pack", required=True, help="Quorum task pack CSV")
    p.add_argument("--packet-csv", required=True, help="Manual packet CSV")
    p.add_argument("--submission-ledger", required=True, help="Manual submission ledger CSV")
    p.add_argument("--output-root", required=True, help="reports/quorum root")
    p.add_argument("--task-pack-out", required=True, help="Output updated task pack CSV")
    p.add_argument("--summary-csv", required=True, help="Output ingestion summary CSV")
    p.add_argument("--summary-md", required=True, help="Output ingestion summary markdown")
    p.add_argument("--submission-ledger-out", default="", help="Updated ledger CSV path (defaults in place)")
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
        for r in rows:
            w.writerow(r)


def parse_json(path: Path) -> Tuple[bool, Dict[str, object], str]:
    if not path.exists():
        return False, {}, "missing_vote_file"
    try:
        obj = json.loads(path.read_text(encoding="utf-8"))
    except Exception as e:
        return False, {}, f"invalid_json:{e}"
    if not isinstance(obj, dict):
        return False, {}, "json_not_object"
    return True, obj, ""


def normalize_list(value: object) -> List[str]:
    if isinstance(value, list):
        return [str(x) for x in value][:12]
    if isinstance(value, str):
        return [v.strip() for v in value.split("|") if v.strip()][:12]
    return []


def validate_vote(vote: Dict[str, object], claim_id: str) -> Tuple[bool, str]:
    missing = sorted(list(REQUIRED_KEYS - set(vote.keys())))
    if missing:
        return False, f"missing_keys:{'|'.join(missing)}"

    if str(vote.get("claim_id", "")).strip() != claim_id:
        return False, "claim_id_mismatch"

    status = str(vote.get("status_class", "")).strip().lower()
    if status not in ALLOWED_STATUS:
        return False, "invalid_status_class"

    gate = str(vote.get("publication_gate_recommendation", "")).strip().lower()
    if gate not in ALLOWED_GATE:
        return False, "invalid_publication_gate_recommendation"

    try:
        conf = float(vote.get("confidence", 0.0))
    except Exception:
        return False, "invalid_confidence"
    if conf < 0.0 or conf > 1.0:
        return False, "invalid_confidence_range"

    rationale = normalize_list(vote.get("rationale"))
    if not rationale:
        return False, "empty_rationale"

    _ = normalize_list(vote.get("critical_risks"))
    return True, ""


def parse_existing_live_votes(claim_dir: Path) -> Tuple[Dict[str, object], Dict[str, object]]:
    a_path = claim_dir / "model_a_vote.json"
    b_path = claim_dir / "model_b_vote.json"
    a_obj: Dict[str, object] = {}
    b_obj: Dict[str, object] = {}
    if a_path.exists():
        try:
            a_obj = json.loads(a_path.read_text(encoding="utf-8"))
        except Exception:
            a_obj = {}
    if b_path.exists():
        try:
            b_obj = json.loads(b_path.read_text(encoding="utf-8"))
        except Exception:
            b_obj = {}
    return a_obj, b_obj


def pick_success_vote(a_obj: Dict[str, object], b_obj: Dict[str, object]) -> Dict[str, object]:
    if bool(a_obj.get("model_call_success", False)):
        return a_obj
    if bool(b_obj.get("model_call_success", False)):
        return b_obj
    return {}


def canonical_provider(name: str) -> str:
    p = (name or "").strip().lower()
    if p.startswith("codex"):
        return "codex"
    if p.startswith("claude"):
        return "claude"
    if p.startswith("gemini"):
        return "gemini"
    if p.startswith("deepseek"):
        return "deepseek"
    if p.startswith("kimi") or p.startswith("moonshot"):
        return "kimi"
    return p or "unknown"


def merge_decision(v1: str, v2: str) -> Tuple[str, str]:
    if v1 == v2:
        if v1 == "approve_promote":
            return "consensus_promote", "Codex + manual vote agree on promotion."
        if v1 == "approve_with_caveats":
            return "consensus_caveated", "Codex + manual vote agree on caveated promotion."
        return "consensus_escalate", "Codex + manual vote agree on escalation."
    return "conflict_escalate", "Codex and manual vote disagree; escalate for stronger adjudication."


def write_merged_md(
    path: Path,
    claim_id: str,
    task_id: str,
    codex_vote: Dict[str, object],
    manual_vote: Dict[str, object],
    merged_status: str,
    merged_note: str,
    quorum_complete: str,
) -> None:
    lines: List[str] = []
    lines.append(f"# Quorum Decision: {claim_id}")
    lines.append("")
    lines.append(f"Generated: {utc_now()}")
    lines.append(f"Task: {task_id}")
    lines.append("Mode: hybrid_live_human")
    lines.append("")
    lines.append("## Votes")
    lines.append(
        f"- Codex vote: {codex_vote.get('status_class','')} (provider={codex_vote.get('provider','')}, confidence={codex_vote.get('confidence','')})"
    )
    lines.append(
        f"- Manual vote: {manual_vote.get('status_class','')} (provider={manual_vote.get('provider','')}, confidence={manual_vote.get('confidence','')})"
    )
    lines.append("")
    lines.append("## Merged Result")
    lines.append(f"- merged_status: {merged_status}")
    lines.append(f"- note: {merged_note}")
    lines.append(f"- external_quorum_complete: {quorum_complete}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    args = parse_args()

    task_rows = read_csv(Path(args.task_pack))
    packet_rows = read_csv(Path(args.packet_csv))
    ledger_rows = read_csv(Path(args.submission_ledger))

    packet_map = {r.get("claim_id", ""): r for r in packet_rows}
    ledger_map = {r.get("claim_id", ""): r for r in ledger_rows}

    out_root = Path(args.output_root)

    summary_rows: List[Dict[str, str]] = []
    updated_tasks: List[Dict[str, str]] = []
    updated_ledger: List[Dict[str, str]] = []

    for lr in ledger_rows:
        updated_ledger.append(dict(lr))

    for t in task_rows:
        row = dict(t)
        claim_id = (row.get("claim_id") or "").strip()
        status = (row.get("status") or "").strip()

        if claim_id not in packet_map:
            updated_tasks.append(row)
            continue

        packet = packet_map[claim_id]
        ledger = ledger_map.get(claim_id, {})
        vote_path = Path((ledger.get("vote_json_path") or packet.get("target_manual_vote_path") or "").strip())

        ok_json, vote_obj, json_err = parse_json(vote_path)
        if not ok_json:
            row["status"] = "blocked_provider_auth"
            row["external_quorum_complete"] = "no"
            row["execution_mode"] = "hybrid_live_human_pending"
            row["execution_notes"] = f"manual_vote_missing_or_invalid:{json_err}"
            updated_tasks.append(row)
            summary_rows.append(
                {
                    "task_id": row.get("task_id", ""),
                    "claim_id": claim_id,
                    "ingest_status": "pending_manual_vote",
                    "result_status": row["status"],
                    "external_quorum_complete": row.get("external_quorum_complete", ""),
                    "reason": json_err,
                }
            )
            continue

        valid, val_err = validate_vote(vote_obj, claim_id)
        if not valid:
            row["status"] = "blocked_provider_auth"
            row["external_quorum_complete"] = "no"
            row["execution_mode"] = "hybrid_live_human_pending"
            row["execution_notes"] = f"manual_vote_validation_failed:{val_err}"
            updated_tasks.append(row)
            summary_rows.append(
                {
                    "task_id": row.get("task_id", ""),
                    "claim_id": claim_id,
                    "ingest_status": "invalid_manual_vote",
                    "result_status": row["status"],
                    "external_quorum_complete": row.get("external_quorum_complete", ""),
                    "reason": val_err,
                }
            )
            continue

        claim_quorum_dir = out_root / claim_id
        a_obj, b_obj = parse_existing_live_votes(claim_quorum_dir)
        codex_vote = pick_success_vote(a_obj, b_obj)

        if not codex_vote:
            row["status"] = "blocked_provider_auth"
            row["external_quorum_complete"] = "no"
            row["execution_mode"] = "hybrid_live_human_pending"
            row["execution_notes"] = "missing_existing_codex_vote"
            updated_tasks.append(row)
            summary_rows.append(
                {
                    "task_id": row.get("task_id", ""),
                    "claim_id": claim_id,
                    "ingest_status": "blocked_missing_codex_vote",
                    "result_status": row["status"],
                    "external_quorum_complete": row.get("external_quorum_complete", ""),
                    "reason": "missing_existing_codex_vote",
                }
            )
            continue

        codex_provider = canonical_provider(str(codex_vote.get("provider", "")))
        manual_provider = canonical_provider(str(vote_obj.get("provider", "")))

        if manual_provider == codex_provider:
            row_status = "executed_live_same_provider"
            quorum_complete = "partial_same_provider"
            same_provider_reason = "manual_provider_matches_codex_provider"
        else:
            row_status = "executed_live"
            quorum_complete = "yes"
            same_provider_reason = ""

        normalized_manual_vote = {
            "claim_id": claim_id,
            "task_id": row.get("task_id", ""),
            "model_lane": "human_operator",
            "execution_mode": "manual_human",
            "external_api_called": True,
            "provider": str(vote_obj.get("provider", "")).strip(),
            "model_call_success": True,
            "blocked_reason": "",
            "status_class": str(vote_obj.get("status_class", "")).strip().lower(),
            "confidence": float(vote_obj.get("confidence", 0.0)),
            "rationale": normalize_list(vote_obj.get("rationale")),
            "critical_risks": normalize_list(vote_obj.get("critical_risks")),
            "publication_gate_recommendation": str(vote_obj.get("publication_gate_recommendation", "")).strip().lower(),
            "notes": str(vote_obj.get("notes", "")).strip(),
            "submitted_utc": str(vote_obj.get("submitted_utc", "")).strip(),
            "source_ref": str(vote_obj.get("source_ref", "")).strip(),
            "operator_lane": str(vote_obj.get("operator_lane", "")).strip(),
            "generated_utc": utc_now(),
        }

        manual_vote_path = claim_quorum_dir / "model_manual_vote.json"
        manual_vote_path.write_text(json.dumps(normalized_manual_vote, indent=2), encoding="utf-8")

        merged_status, merged_note = merge_decision(
            str(codex_vote.get("status_class", "")).strip().lower(),
            normalized_manual_vote["status_class"],
        )

        merged_md_path = claim_quorum_dir / "merged_quorum_decision.md"
        write_merged_md(
            merged_md_path,
            claim_id,
            row.get("task_id", ""),
            codex_vote,
            normalized_manual_vote,
            merged_status,
            merged_note,
            quorum_complete,
        )

        row["status"] = row_status
        row["execution_mode"] = "hybrid_live_human"
        row["external_quorum_complete"] = quorum_complete
        row["merged_status"] = merged_status
        notes = merged_note
        if same_provider_reason:
            notes = f"{notes} | {same_provider_reason}"
        row["execution_notes"] = notes

        existing_artifacts = (row.get("output_artifacts") or "").strip()
        add_artifacts = f"{manual_vote_path}|{merged_md_path}"
        if existing_artifacts:
            row["output_artifacts"] = f"{existing_artifacts}|{add_artifacts}"
        else:
            row["output_artifacts"] = add_artifacts

        row["updated_utc"] = utc_now()
        updated_tasks.append(row)

        summary_rows.append(
            {
                "task_id": row.get("task_id", ""),
                "claim_id": claim_id,
                "ingest_status": "ingested",
                "result_status": row_status,
                "external_quorum_complete": quorum_complete,
                "reason": same_provider_reason or "ok",
            }
        )

        # update ledger
        for lrow in updated_ledger:
            if (lrow.get("claim_id") or "").strip() == claim_id:
                lrow["ingest_status"] = "ingested" if row_status == "executed_live" else "partial_same_provider"
                lrow["ingest_notes"] = notes
                if not lrow.get("submitted_utc"):
                    lrow["submitted_utc"] = str(vote_obj.get("submitted_utc", "")).strip()

    write_csv(Path(args.task_pack_out), updated_tasks)
    write_csv(
        Path(args.summary_csv),
        summary_rows,
        fieldnames=["task_id", "claim_id", "ingest_status", "result_status", "external_quorum_complete", "reason"],
    )

    status_counts = Counter(r["result_status"] for r in summary_rows)
    ingest_counts = Counter(r["ingest_status"] for r in summary_rows)

    lines: List[str] = []
    lines.append("# Manual Quorum Ingestion Summary")
    lines.append("")
    lines.append(f"Generated: {utc_now()}")
    lines.append(f"Rows processed: {len(summary_rows)}")
    lines.append("")
    lines.append("## Ingest Status Counts")
    for k, v in sorted(ingest_counts.items()):
        lines.append(f"- {k}: {v}")
    lines.append("")
    lines.append("## Result Status Counts")
    for k, v in sorted(status_counts.items()):
        lines.append(f"- {k}: {v}")
    lines.append("")
    lines.append("## Rows")
    lines.append("| Task | Claim | Ingest Status | Result Status | External Quorum Complete | Reason |")
    lines.append("|---|---|---|---|---|---|")
    for r in summary_rows:
        lines.append(
            f"| {r['task_id']} | {r['claim_id']} | {r['ingest_status']} | {r['result_status']} | {r['external_quorum_complete']} | {r['reason']} |"
        )

    summary_md_path = Path(args.summary_md)
    summary_md_path.parent.mkdir(parents=True, exist_ok=True)
    summary_md_path.write_text("\n".join(lines) + "\n", encoding="utf-8")

    ledger_out = Path(args.submission_ledger_out) if args.submission_ledger_out else Path(args.submission_ledger)
    write_csv(
        ledger_out,
        updated_ledger,
        fieldnames=[
            "task_id",
            "claim_id",
            "provider",
            "operator_lane",
            "source_ref",
            "vote_json_path",
            "raw_response_path",
            "submitted_utc",
            "ingest_status",
            "ingest_notes",
        ],
    )

    print(f"wrote_task_pack={args.task_pack_out}")
    print(f"wrote_summary_csv={args.summary_csv} rows={len(summary_rows)}")
    print(f"wrote_summary_md={args.summary_md}")
    print(f"wrote_submission_ledger={ledger_out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
