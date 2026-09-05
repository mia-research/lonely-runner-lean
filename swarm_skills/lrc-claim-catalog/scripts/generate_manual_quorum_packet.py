#!/usr/bin/env python3
"""Generate manual quorum packet for blocked claims.

Creates per-claim prompt packs so a human operator can run a second provider
vote in web/UI and return structured JSON for ingestion.
"""

from __future__ import annotations

import argparse
import csv
import json
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, List, Sequence


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Generate manual quorum packet for blocked claims")
    p.add_argument("--task-pack", required=True, help="Quorum task pack CSV")
    p.add_argument("--dossier-index", required=True, help="Dossier index CSV")
    p.add_argument("--ranking", required=True, help="Ranking CSV")
    p.add_argument("--queue", required=True, help="Promotion queue CSV")
    p.add_argument("--template", required=True, help="Manual prompt template markdown")
    p.add_argument("--quorum-root", required=True, help="Root reports/quorum dir")
    p.add_argument("--packet-root", required=True, help="Output packet root dir")
    p.add_argument("--packet-csv", required=True, help="Output packet summary CSV")
    p.add_argument("--packet-md", required=True, help="Output packet summary markdown")
    p.add_argument("--submission-ledger", required=True, help="Output submission ledger CSV")
    p.add_argument("--manual-votes-dir", required=True, help="Target directory for manual vote JSON files")
    p.add_argument("--dossier-snippet-chars", type=int, default=6000, help="Dossier snippet size")
    return p.parse_args()


def read_csv(path: Path) -> List[Dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as f:
        return list(csv.DictReader(f))


def write_csv(path: Path, rows: List[Dict[str, str]], fieldnames: Sequence[str]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as f:
        w = csv.DictWriter(f, fieldnames=fieldnames)
        w.writeheader()
        for r in rows:
            w.writerow(r)


def load_map(rows: List[Dict[str, str]], key: str) -> Dict[str, Dict[str, str]]:
    out: Dict[str, Dict[str, str]] = {}
    for r in rows:
        k = (r.get(key) or "").strip()
        if k:
            out[k] = r
    return out


def parse_float(s: str, default: float = 0.0) -> float:
    try:
        return float(s)
    except Exception:
        return default


def safe_read_text(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8", errors="replace")
    except Exception:
        return ""


def choose_manual_provider(task: Dict[str, str]) -> str:
    lane_a = (task.get("model_a") or "").lower()
    lane_b = (task.get("model_b") or "").lower()
    lanes = f"{lane_a} {lane_b}"
    if "claude" in lanes:
        return "gemini"
    if "gemini" in lanes:
        return "deepseek"
    if "deepseek" in lanes:
        return "kimi"
    return "gemini"


def extract_blocked_reasons(claim_quorum_dir: Path) -> str:
    reasons: List[str] = []
    for name in ("model_a_vote.json", "model_b_vote.json"):
        p = claim_quorum_dir / name
        if not p.exists():
            continue
        try:
            obj = json.loads(p.read_text(encoding="utf-8"))
        except Exception:
            continue
        success = bool(obj.get("model_call_success", obj.get("external_api_called", False)))
        if not success:
            reason = str(obj.get("blocked_reason", "")).strip()
            provider = str(obj.get("provider", "")).strip()
            lane = str(obj.get("model_lane", "")).strip()
            if reason:
                reasons.append(f"{name}:{provider}:{lane}:{reason}")
    return " | ".join(reasons)


def render_prompt(
    template: str,
    claim_id: str,
    review_score: float,
    ladder_status: str,
    metric_match: str,
    dossier_snippet: str,
) -> str:
    txt = template
    txt = txt.replace("{{CLAIM_ID}}", claim_id)
    txt = txt.replace("{{REVIEW_SCORE}}", f"{review_score:.3f}")
    txt = txt.replace("{{LADDER_STATUS}}", ladder_status or "unknown")
    txt = txt.replace("{{METRIC_MATCH}}", metric_match or "unknown")
    txt = txt.replace("{{DOSSIER_EXCERPT}}", dossier_snippet)
    return txt


def write_json(path: Path, obj: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2), encoding="utf-8")


def main() -> int:
    args = parse_args()

    task_rows = read_csv(Path(args.task_pack))
    blocked_tasks = [r for r in task_rows if (r.get("status") or "").strip() == "blocked_provider_auth"]

    dossier_map = load_map(read_csv(Path(args.dossier_index)), "claim_id")
    ranking_map = load_map(read_csv(Path(args.ranking)), "claim_id")
    queue_map = load_map(read_csv(Path(args.queue)), "claim_id")

    template_text = safe_read_text(Path(args.template))

    packet_root = Path(args.packet_root)
    packet_root.mkdir(parents=True, exist_ok=True)

    manual_votes_dir = Path(args.manual_votes_dir)
    manual_votes_dir.mkdir(parents=True, exist_ok=True)

    quorum_root = Path(args.quorum_root)

    packet_rows: List[Dict[str, str]] = []
    ledger_rows: List[Dict[str, str]] = []

    for task in blocked_tasks:
        claim_id = (task.get("claim_id") or "").strip()
        task_id = (task.get("task_id") or "").strip()
        rank_row = ranking_map.get(claim_id, {})
        queue_row = queue_map.get(claim_id, {})
        dossier_row = dossier_map.get(claim_id, {})

        review_score = parse_float(rank_row.get("review_score", "0"), 0.0)
        ladder_status = (queue_row.get("ladder_status") or "").strip()
        metric_match = (queue_row.get("metric_match") or "").strip()

        dossier_path = Path(dossier_row.get("dossier_path", "")) if dossier_row.get("dossier_path") else None
        dossier_text = safe_read_text(dossier_path) if dossier_path else ""
        dossier_snippet = dossier_text[: args.dossier_snippet_chars]

        claim_dir = packet_root / claim_id
        claim_dir.mkdir(parents=True, exist_ok=True)

        excerpt_path = claim_dir / "dossier_excerpt.md"
        excerpt_path.write_text(
            "\n".join(
                [
                    f"# Dossier Excerpt: {claim_id}",
                    "",
                    f"Generated: {utc_now()}",
                    f"Task: {task_id}",
                    f"Source dossier: {dossier_path}",
                    "",
                    dossier_snippet,
                    "",
                ]
            ),
            encoding="utf-8",
        )

        prompt_path = claim_dir / "manual_vote_prompt.md"
        prompt_text = render_prompt(
            template_text,
            claim_id=claim_id,
            review_score=review_score,
            ladder_status=ladder_status,
            metric_match=metric_match,
            dossier_snippet=dossier_snippet,
        )
        prompt_path.write_text(prompt_text + "\n", encoding="utf-8")

        manual_json_template_path = claim_dir / "manual_vote_template.json"
        write_json(
            manual_json_template_path,
            {
                "claim_id": claim_id,
                "provider": "gemini|deepseek|kimi|claude_web",
                "status_class": "approve_promote|approve_with_caveats|escalate",
                "confidence": 0.0,
                "rationale": [],
                "critical_risks": [],
                "publication_gate_recommendation": "promote|hold|escalate",
                "notes": "",
                "submitted_utc": utc_now(),
                "operator_lane": "Lane_A|Lane_B|Human",
                "source_ref": "chat_url_or_export_or_screenshot_path",
            },
        )

        blocked_reason = extract_blocked_reasons(quorum_root / claim_id)
        preferred = choose_manual_provider(task)

        packet_rows.append(
            {
                "task_id": task_id,
                "claim_id": claim_id,
                "rank": rank_row.get("rank", ""),
                "review_score": f"{review_score:.3f}",
                "metric_match": metric_match,
                "ladder_status": ladder_status,
                "status": task.get("status", ""),
                "external_quorum_complete": task.get("external_quorum_complete", ""),
                "blocked_reason": blocked_reason,
                "preferred_manual_provider": preferred,
                "model_a": task.get("model_a", ""),
                "model_b": task.get("model_b", ""),
                "dossier_path": str(dossier_path) if dossier_path else "",
                "dossier_excerpt_path": str(excerpt_path),
                "manual_prompt_path": str(prompt_path),
                "manual_vote_template_path": str(manual_json_template_path),
                "target_manual_vote_path": str(manual_votes_dir / f"{claim_id}_manual_vote.json"),
            }
        )

        ledger_rows.append(
            {
                "task_id": task_id,
                "claim_id": claim_id,
                "provider": "",
                "operator_lane": "",
                "source_ref": "",
                "vote_json_path": str(manual_votes_dir / f"{claim_id}_manual_vote.json"),
                "raw_response_path": str(manual_votes_dir / f"{claim_id}_raw_response.txt"),
                "submitted_utc": "",
                "ingest_status": "pending",
                "ingest_notes": "",
            }
        )

    write_csv(
        Path(args.packet_csv),
        packet_rows,
        fieldnames=[
            "task_id",
            "claim_id",
            "rank",
            "review_score",
            "metric_match",
            "ladder_status",
            "status",
            "external_quorum_complete",
            "blocked_reason",
            "preferred_manual_provider",
            "model_a",
            "model_b",
            "dossier_path",
            "dossier_excerpt_path",
            "manual_prompt_path",
            "manual_vote_template_path",
            "target_manual_vote_path",
        ],
    )

    write_csv(
        Path(args.submission_ledger),
        ledger_rows,
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

    md_lines: List[str] = []
    md_lines.append("# Manual Quorum Packet (Cycle 003)")
    md_lines.append("")
    md_lines.append(f"Generated: {utc_now()}")
    md_lines.append(f"Blocked claims: {len(packet_rows)}")
    md_lines.append("")
    md_lines.append("## How To Run")
    md_lines.append("1. Open each `manual_prompt_path` and run it in a non-Codex provider web UI (Gemini/DeepSeek/Kimi preferred while Claude is quota-blocked).")
    md_lines.append("2. Save structured JSON output to `target_manual_vote_path`.")
    md_lines.append("3. Save raw model response text to matching `raw_response_path` in the submission ledger.")
    md_lines.append("4. Fill provider/operator/source/submitted_utc columns in the ledger CSV.")
    md_lines.append("5. Return packet to coordinator for ingestion and quorum merge.")
    md_lines.append("")
    md_lines.append("## Packet Index")
    md_lines.append("| Task | Claim | Rank | Review Score | Preferred Manual Provider | Prompt | Target Vote JSON |")
    md_lines.append("|---|---|---:|---:|---|---|---|")
    for r in packet_rows:
        md_lines.append(
            f"| {r['task_id']} | {r['claim_id']} | {r['rank']} | {r['review_score']} | {r['preferred_manual_provider']} | {r['manual_prompt_path']} | {r['target_manual_vote_path']} |"
        )
    md_lines.append("")
    md_lines.append("## Files")
    md_lines.append(f"- Packet CSV: {args.packet_csv}")
    md_lines.append(f"- Submission Ledger: {args.submission_ledger}")
    md_lines.append(f"- Manual votes dir: {args.manual_votes_dir}")

    packet_md_path = Path(args.packet_md)
    packet_md_path.parent.mkdir(parents=True, exist_ok=True)
    packet_md_path.write_text("\n".join(md_lines) + "\n", encoding="utf-8")

    print(f"wrote_packet_csv={args.packet_csv} rows={len(packet_rows)}")
    print(f"wrote_packet_md={args.packet_md}")
    print(f"wrote_submission_ledger={args.submission_ledger} rows={len(ledger_rows)}")
    print(f"packet_root={args.packet_root}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
