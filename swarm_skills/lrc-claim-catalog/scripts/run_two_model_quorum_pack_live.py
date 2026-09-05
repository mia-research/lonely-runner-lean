#!/usr/bin/env python3
"""Run two-model quorum task pack with live model calls (Codex + Claude CLI).

This script writes the same quorum artifacts as the proxy runner, but uses
real provider calls when available. If a provider is unavailable (e.g. auth),
it records a blocked state with explicit reason.
"""

from __future__ import annotations

import argparse
import csv
import json
import os
import re
import subprocess
import tempfile
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

ALLOWED_STATUS = {"approve_promote", "approve_with_caveats", "escalate"}


def utc_now() -> str:
    return datetime.now(timezone.utc).replace(microsecond=0).isoformat().replace("+00:00", "Z")


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description="Run two-model quorum pack in live CLI mode")
    p.add_argument("--task-pack", required=True, help="Quorum task pack CSV")
    p.add_argument("--dossier-index", required=True, help="Dossier index CSV")
    p.add_argument("--output-root", required=True, help="Root reports/quorum output dir")
    p.add_argument("--task-pack-out", required=True, help="Updated task pack CSV")
    p.add_argument("--summary-md", required=True, help="Summary markdown")
    p.add_argument("--summary-csv", required=True, help="Summary CSV")
    p.add_argument("--ranking", default="", help="Optional ranking CSV for prompt context")
    p.add_argument("--queue", default="", help="Optional promotion queue CSV for prompt context")
    p.add_argument("--limit", type=int, default=0, help="Optional max claims to execute")
    p.add_argument("--max-dossier-chars", type=int, default=12000, help="Max dossier chars in prompt")
    p.add_argument("--timeout-sec", type=int, default=180, help="Per-model call timeout seconds")
    p.add_argument(
        "--claude-max-output-tokens",
        type=int,
        default=8192,
        help="Claude response token cap. Set 0 to inherit env; otherwise this value is enforced.",
    )
    p.add_argument(
        "--max-response-chars",
        type=int,
        default=1200,
        help="Prompt guard: ask models to keep JSON response concise.",
    )
    p.add_argument(
        "--fallback-codex-for-unsupported",
        action="store_true",
        help="Use live Codex fallback when lane provider has no CLI integration",
    )
    p.add_argument(
        "--workdir",
        default="/Users/trentpalelei/Documents/Claude Library",
        help="Working directory for codex exec",
    )
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


def write_json(path: Path, obj: Dict[str, object]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2), encoding="utf-8")


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


def parse_json_object(text: str) -> Dict[str, object]:
    txt = (text or "").strip()
    if not txt:
        return {}
    try:
        obj = json.loads(txt)
        if isinstance(obj, dict):
            return obj
    except Exception:
        pass

    match = re.search(r"\{[\s\S]*\}", txt)
    if not match:
        return {}
    try:
        obj = json.loads(match.group(0))
        if isinstance(obj, dict):
            return obj
    except Exception:
        return {}
    return {}


def canonical_provider(provider_name: str) -> str:
    p = (provider_name or "").strip().lower()
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


def provider_from_lane(model_lane: str) -> str:
    lane = (model_lane or "").lower()
    if "claude" in lane:
        return "claude"
    if "chatgpt" in lane or "openai" in lane or "codex" in lane:
        return "codex"
    if "gemini" in lane:
        return "gemini"
    if "deepseek" in lane:
        return "deepseek"
    if "kimi" in lane or "moonshot" in lane:
        return "kimi"
    return "unknown"


def normalize_vote(raw: Dict[str, object], fallback_note: str = "") -> Dict[str, object]:
    status = str(raw.get("status_class", "escalate")).strip().lower()
    if status not in ALLOWED_STATUS:
        status = "escalate"

    try:
        confidence = float(raw.get("confidence", 0.0))
    except Exception:
        confidence = 0.0
    confidence = max(0.0, min(confidence, 1.0))

    rationale_raw = raw.get("rationale", [])
    if isinstance(rationale_raw, list):
        rationale = [str(x) for x in rationale_raw][:8]
    elif isinstance(rationale_raw, str):
        rationale = [rationale_raw[:240]]
    else:
        rationale = []

    risks_raw = raw.get("critical_risks", [])
    if isinstance(risks_raw, list):
        risks = [str(x) for x in risks_raw][:8]
    elif isinstance(risks_raw, str):
        risks = [risks_raw[:240]]
    else:
        risks = []

    gate = str(raw.get("publication_gate_recommendation", "")).strip().lower()
    if gate not in {"promote", "hold", "escalate"}:
        gate = "promote" if status == "approve_promote" else ("hold" if status == "approve_with_caveats" else "escalate")

    notes = str(raw.get("notes", "")).strip()
    if fallback_note:
        notes = (notes + " | " + fallback_note).strip(" |")

    return {
        "status_class": status,
        "confidence": round(confidence, 3),
        "rationale": rationale,
        "critical_risks": risks,
        "publication_gate_recommendation": gate,
        "notes": notes,
    }


def build_prompt(
    claim_id: str,
    task_id: str,
    model_lane: str,
    dossier_text: str,
    review_score: float,
    ladder_status: str,
    metric_match: str,
    max_response_chars: int,
) -> str:
    return (
        "You are an independent mathematical-claim adjudicator for publication gating. "
        "Evaluate validity risk conservatively but do not auto-deny novel ideas.\n\n"
        "Return ONLY a single JSON object. Your response must start with { and contain no text before or after the JSON. Keys:\n"
        "status_class (approve_promote|approve_with_caveats|escalate),\n"
        "confidence (0..1),\n"
        "rationale (array of short strings),\n"
        "critical_risks (array),\n"
        "publication_gate_recommendation (promote|hold|escalate),\n"
        "notes (string).\n\n"
        f"Keep output concise: total response <= {max_response_chars} characters. "
        "Use at most 3 rationale items and 3 critical_risks items.\n\n"
        f"Claim ID: {claim_id}\n"
        f"Task ID: {task_id}\n"
        f"Lane: {model_lane}\n"
        f"review_score: {review_score}\n"
        f"numeric_ladder_status: {ladder_status}\n"
        f"measurement_metric_match: {metric_match}\n\n"
        "Dossier excerpt:\n"
        f"{dossier_text}\n"
    )


def run_codex(prompt: str, timeout_sec: int, workdir: str) -> Tuple[bool, Dict[str, object], str]:
    with tempfile.NamedTemporaryFile(prefix="codex_vote_", suffix=".txt", delete=False) as tf:
        out_path = Path(tf.name)

    cmd = [
        "codex",
        "exec",
        "--skip-git-repo-check",
        "--ephemeral",
        "-C",
        workdir,
        "--output-last-message",
        str(out_path),
        prompt,
    ]
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout_sec)
    except subprocess.TimeoutExpired:
        return False, {}, "codex_timeout"

    final_text = ""
    try:
        final_text = out_path.read_text(encoding="utf-8")
    except Exception:
        final_text = ""

    if proc.returncode != 0:
        stderr = (proc.stderr or "")[-600:]
        return False, {}, f"codex_error_rc{proc.returncode}: {stderr.strip()}"

    obj = parse_json_object(final_text)
    if not obj:
        return False, {}, "codex_non_json_response"
    return True, obj, ""


def resolve_claude_token_cap(cli_cap: int) -> str:
    if cli_cap and cli_cap > 0:
        return str(cli_cap)
    env_cap = (os.environ.get("CLAUDE_CODE_MAX_OUTPUT_TOKENS") or "").strip()
    if env_cap.isdigit() and int(env_cap) > 0:
        return env_cap
    return "8192"


def run_claude(prompt: str, timeout_sec: int, claude_max_output_tokens: int) -> Tuple[bool, Dict[str, object], str]:
    env = {**os.environ, "CLAUDE_CODE_MAX_OUTPUT_TOKENS": resolve_claude_token_cap(claude_max_output_tokens)}
    cmd = ["claude", "-p", "--output-format", "text", prompt]
    try:
        proc = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout_sec, env=env)
    except subprocess.TimeoutExpired:
        return False, {}, "claude_timeout"

    if proc.returncode != 0:
        err = ((proc.stderr or "") + "\n" + (proc.stdout or ""))[-600:]
        return False, {}, f"claude_error_rc{proc.returncode}: {err.strip()}"

    obj = parse_json_object(proc.stdout or "")
    if not obj:
        return False, {}, "claude_non_json_response"
    return True, obj, ""


def run_deepseek(prompt: str, timeout_sec: int) -> Tuple[bool, Dict[str, object], str]:
    """Call local DeepSeek-R1:14b via Ollama for quorum votes.

    Uses the Ollama /api/chat endpoint directly (no subprocess).
    DeepSeek R1 returns a <think> block then the JSON answer — Ollama's
    native 'think' parameter separates them so we only score the content.
    """
    import re as _re

    payload = {
        "model": "deepseek-r1:14b",
        "stream": False,
        "think": False,          # keep output clean for JSON parsing
        "messages": [
            {
                "role": "system",
                "content": (
                    "You are an independent mathematical-claim adjudicator. "
                    "Respond ONLY with a single valid JSON object — no prose, "
                    "no markdown fences, no text before or after the braces."
                ),
            },
            {"role": "user", "content": prompt},
        ],
        "options": {
            "temperature": 0.2,
            "num_predict": 1200,
            "num_ctx": 32768,
        },
        "keep_alive": "15m",
    }

    try:
        import requests as _req
        resp = _req.post(
            "http://localhost:11434/api/chat",
            json=payload,
            timeout=timeout_sec,
        )
        resp.raise_for_status()
    except Exception as exc:
        return False, {}, f"deepseek_connection_error: {exc}"

    data = resp.json()
    content = data.get("message", {}).get("content", "")

    # Strip any accidental <think>...</think> or markdown fences
    content = _re.sub(r"<think>.*?</think>", "", content, flags=_re.DOTALL)
    content = content.strip().strip("```json").strip("```").strip()

    obj = parse_json_object(content)
    if not obj:
        return False, {}, f"deepseek_non_json_response: {content[:200]}"
    return True, obj, ""


def merge_decision(vote_a: str, vote_b: str) -> Tuple[str, str]:
    if vote_a == vote_b:
        if vote_a == "approve_promote":
            return "consensus_promote", "Both live votes approve promotion."
        if vote_a == "approve_with_caveats":
            return "consensus_caveated", "Both live votes approve with caveats."
        return "consensus_escalate", "Both live votes request escalation."
    return "conflict_escalate", "Live votes disagree; escalate adjudication with stronger refuter packet."


def write_merged_md(
    path: Path,
    claim_id: str,
    task_id: str,
    vote_a: Dict[str, object],
    vote_b: Dict[str, object],
    merged_status: str,
    merged_note: str,
    quorum_complete: str,
    dossier_path: str,
) -> None:
    lines: List[str] = []
    lines.append(f"# Quorum Decision: {claim_id}")
    lines.append("")
    lines.append(f"Generated: {utc_now()}")
    lines.append(f"Task: {task_id}")
    lines.append("Mode: live_cli")
    lines.append(f"Dossier: {dossier_path}")
    lines.append("")
    lines.append("## Live Votes")
    lines.append(
        f"- Model A: {vote_a.get('status_class')} (confidence={vote_a.get('confidence')}, provider={vote_a.get('provider')}, success={vote_a.get('model_call_success')})"
    )
    lines.append(
        f"- Model B: {vote_b.get('status_class')} (confidence={vote_b.get('confidence')}, provider={vote_b.get('provider')}, success={vote_b.get('model_call_success')})"
    )
    lines.append("")
    lines.append("## Merged Result")
    lines.append(f"- merged_status: {merged_status}")
    lines.append(f"- note: {merged_note}")
    lines.append(f"- external_quorum_complete: {quorum_complete}")
    lines.append("")
    lines.append("## Traceability")
    lines.append(f"- model_a_blocked_reason: {vote_a.get('blocked_reason', '')}")
    lines.append(f"- model_b_blocked_reason: {vote_b.get('blocked_reason', '')}")

    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    args = parse_args()

    tasks = read_csv(Path(args.task_pack))
    dossier_idx = load_map(read_csv(Path(args.dossier_index)), "claim_id")
    ranking = load_map(read_csv(Path(args.ranking)), "claim_id") if args.ranking else {}
    queue = load_map(read_csv(Path(args.queue)), "claim_id") if args.queue else {}

    out_root = Path(args.output_root)

    updated_tasks: List[Dict[str, str]] = []
    result_rows: List[Dict[str, str]] = []

    executed_count = 0
    for t in tasks:
        status_in = (t.get("status") or "").strip().lower()
        should_run = status_in in {"", "queued", "retry", "executed_proxy", "blocked_provider_auth", "executed_live_same_provider"}
        if not should_run:
            updated_tasks.append(dict(t))
            continue
        if args.limit and executed_count >= args.limit:
            updated_tasks.append(dict(t))
            continue

        claim_id = (t.get("claim_id") or "").strip()
        task_id = (t.get("task_id") or "").strip()
        lane_a = (t.get("model_a") or "").strip()
        lane_b = (t.get("model_b") or "").strip()

        drow = dossier_idx.get(claim_id, {})
        dossier_path = Path(drow.get("dossier_path", "")) if drow.get("dossier_path") else None
        dossier_text = ""
        if dossier_path and dossier_path.exists():
            dossier_text = dossier_path.read_text(encoding="utf-8", errors="replace")
        dossier_text = dossier_text[: args.max_dossier_chars]

        rrow = ranking.get(claim_id, {})
        qrow = queue.get(claim_id, {})
        review_score = parse_float(rrow.get("review_score", "0"), 0.0)
        ladder_status = (qrow.get("ladder_status") or "").strip()
        metric_match = (qrow.get("metric_match") or "").strip()

        prompt_a = build_prompt(
            claim_id,
            task_id,
            lane_a,
            dossier_text,
            review_score,
            ladder_status,
            metric_match,
            args.max_response_chars,
        )
        prompt_b = build_prompt(
            claim_id,
            task_id,
            lane_b,
            dossier_text,
            review_score,
            ladder_status,
            metric_match,
            args.max_response_chars,
        )

        def dispatch(model_lane: str, prompt: str) -> Dict[str, object]:
            p = provider_from_lane(model_lane)

            if p == "codex":
                ok, raw, err = run_codex(prompt, args.timeout_sec, args.workdir)
                provider_name = "codex_live"
                if not ok:
                    return {
                        "provider": provider_name,
                        "model_call_success": False,
                        "blocked_reason": err,
                        **normalize_vote({"status_class": "escalate", "confidence": 0.0, "rationale": ["provider_call_failed"], "notes": err}),
                    }
                return {
                    "provider": provider_name,
                    "model_call_success": True,
                    "blocked_reason": "",
                    **normalize_vote(raw),
                }

            if p == "claude":
                ok, raw, err = run_claude(prompt, args.timeout_sec, args.claude_max_output_tokens)
                provider_name = "claude_live"
                if not ok:
                    return {
                        "provider": provider_name,
                        "model_call_success": False,
                        "blocked_reason": err,
                        **normalize_vote({"status_class": "escalate", "confidence": 0.0, "rationale": ["provider_call_failed"], "notes": err}),
                    }
                return {
                    "provider": provider_name,
                    "model_call_success": True,
                    "blocked_reason": "",
                    **normalize_vote(raw),
                }

            if p == "deepseek":
                ok, raw, err = run_deepseek(prompt, args.timeout_sec)
                provider_name = "deepseek_local"
                if not ok:
                    return {
                        "provider": provider_name,
                        "model_call_success": False,
                        "blocked_reason": err,
                        **normalize_vote({"status_class": "escalate", "confidence": 0.0, "rationale": ["provider_call_failed"], "notes": err}),
                    }
                return {
                    "provider": provider_name,
                    "model_call_success": True,
                    "blocked_reason": "",
                    **normalize_vote(raw),
                }

            if args.fallback_codex_for_unsupported:
                ok, raw, err = run_codex(prompt, args.timeout_sec, args.workdir)
                provider_name = f"codex_fallback_for_{p or 'unknown'}"
                if not ok:
                    return {
                        "provider": provider_name,
                        "model_call_success": False,
                        "blocked_reason": err,
                        **normalize_vote({"status_class": "escalate", "confidence": 0.0, "rationale": ["fallback_provider_call_failed"], "notes": err}),
                    }
                return {
                    "provider": provider_name,
                    "model_call_success": True,
                    "blocked_reason": "",
                    **normalize_vote(raw, fallback_note=f"fallback_used_for_lane_provider={p}"),
                }

            return {
                "provider": p or "unknown",
                "model_call_success": False,
                "blocked_reason": f"provider_not_integrated:{p}",
                **normalize_vote({"status_class": "escalate", "confidence": 0.0, "rationale": ["provider_not_integrated"], "notes": f"provider_not_integrated:{p}"}),
            }

        vote_a = dispatch(lane_a, prompt_a)
        vote_b = dispatch(lane_b, prompt_b)

        merged_status, merged_note = merge_decision(str(vote_a["status_class"]), str(vote_b["status_class"]))

        success_a = bool(vote_a.get("model_call_success"))
        success_b = bool(vote_b.get("model_call_success"))
        provider_a = canonical_provider(str(vote_a.get("provider", "")))
        provider_b = canonical_provider(str(vote_b.get("provider", "")))

        if success_a and success_b and provider_a != provider_b:
            row_status = "executed_live"
            quorum_complete = "yes"
        elif success_a and success_b:
            row_status = "executed_live_same_provider"
            quorum_complete = "partial_same_provider"
        else:
            row_status = "blocked_provider_auth"
            quorum_complete = "no"

        claim_dir = out_root / claim_id
        model_a_path = claim_dir / "model_a_vote.json"
        model_b_path = claim_dir / "model_b_vote.json"
        merged_path = claim_dir / "merged_quorum_decision.md"

        vote_a_obj = {
            "claim_id": claim_id,
            "task_id": task_id,
            "model_lane": lane_a,
            "execution_mode": "live_cli",
            "external_api_called": success_a,
            "generated_utc": utc_now(),
            **vote_a,
        }
        vote_b_obj = {
            "claim_id": claim_id,
            "task_id": task_id,
            "model_lane": lane_b,
            "execution_mode": "live_cli",
            "external_api_called": success_b,
            "generated_utc": utc_now(),
            **vote_b,
        }

        write_json(model_a_path, vote_a_obj)
        write_json(model_b_path, vote_b_obj)
        write_merged_md(
            merged_path,
            claim_id,
            task_id,
            vote_a_obj,
            vote_b_obj,
            merged_status,
            merged_note,
            quorum_complete,
            str(dossier_path) if dossier_path else "",
        )

        row = dict(t)
        row["status"] = row_status
        row["updated_utc"] = utc_now()
        row["execution_mode"] = "live_cli"
        row["external_quorum_complete"] = quorum_complete
        row["merged_status"] = merged_status
        if row_status == "blocked_provider_auth":
            row["execution_notes"] = (
                "live_quorum_blocked: "
                f"model_a_success={success_a}, model_b_success={success_b}, "
                f"model_a_reason={vote_a.get('blocked_reason','')}, model_b_reason={vote_b.get('blocked_reason','')}"
            )
        elif row_status == "executed_live_same_provider":
            row["execution_notes"] = "live_votes_completed_same_provider_only; cross-provider quorum still pending"
        else:
            row["execution_notes"] = merged_note
        row["output_artifacts"] = f"{model_a_path}|{model_b_path}|{merged_path}"
        updated_tasks.append(row)

        result_rows.append(
            {
                "task_id": task_id,
                "claim_id": claim_id,
                "status": row_status,
                "merged_status": merged_status,
                "external_quorum_complete": quorum_complete,
                "model_a_provider": provider_a,
                "model_b_provider": provider_b,
                "output_dir": str(claim_dir),
                "updated_utc": utc_now(),
            }
        )
        executed_count += 1

    write_csv(Path(args.task_pack_out), updated_tasks)
    write_csv(
        Path(args.summary_csv),
        result_rows,
        fieldnames=[
            "task_id",
            "claim_id",
            "status",
            "merged_status",
            "external_quorum_complete",
            "model_a_provider",
            "model_b_provider",
            "output_dir",
            "updated_utc",
        ],
    )

    status_counts = Counter(r["status"] for r in result_rows)
    merged_counts = Counter(r["merged_status"] for r in result_rows)

    lines: List[str] = []
    lines.append("# Two-Model Quorum Pack Execution (Live CLI)")
    lines.append("")
    lines.append(f"Generated: {utc_now()}")
    lines.append(f"Tasks executed: {len(result_rows)}")
    lines.append("Execution mode: live_cli")
    lines.append("")
    lines.append("## Status Counts")
    for k, v in sorted(status_counts.items()):
        lines.append(f"- {k}: {v}")
    lines.append("")
    lines.append("## Merged Status Counts")
    for k, v in sorted(merged_counts.items()):
        lines.append(f"- {k}: {v}")
    lines.append("")
    lines.append("## Task Results")
    lines.append("| Task | Claim | Status | Merged Status | External Quorum Complete | A Provider | B Provider |")
    lines.append("|---|---|---|---|---|---|---|")
    for r in result_rows:
        lines.append(
            f"| {r['task_id']} | {r['claim_id']} | {r['status']} | {r['merged_status']} | {r['external_quorum_complete']} | {r['model_a_provider']} | {r['model_b_provider']} |"
        )
    lines.append("")
    lines.append("## Gate Note")
    lines.append("- `external_quorum_complete=yes` is required for strict cross-provider publication gate.")

    md_path = Path(args.summary_md)
    md_path.parent.mkdir(parents=True, exist_ok=True)
    md_path.write_text("\n".join(lines) + "\n", encoding="utf-8")

    print(f"wrote_task_pack={args.task_pack_out}")
    print(f"wrote_summary_md={args.summary_md}")
    print(f"wrote_summary_csv={args.summary_csv} rows={len(result_rows)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
