#!/usr/bin/env python3
"""
proof_checker.py — Adversarial proof-section reviewer for the Math Ex / LRC pipeline.

Uses the local DeepSeek R1 14b model via Ollama native API with chain-of-thought
reasoning enabled by default.  Given a theorem statement or proof section (markdown),
it runs one or more of four checks and aggregates them into a single verdict.

Usage (CLI):
    python3 tools/proof_checker.py "<proof_text>" [--task TASK] [--no-thinking] [--json]

    # Pipe a section directly from the paper:
    python3 tools/proof_checker.py "$(sed -n '514,642p' lrc_n11_ap_paper_v22.md)" --task full --json

Tasks:
    cases   Check exhaustiveness and non-overlap of all proof cases.
    arith   Verify every numerical inequality (flag suspicious or unchecked ones).
    deps    Verify cited lemma/theorem names appear in a self-consistent dependency chain.
    full    Run cases + arith + deps sequentially and aggregate into one verdict.

Output (plain text or --json):
    VERDICT: [SOUND | CONCERNS | UNSOUND]
    CONCERNS: <bullet list, or NONE>
    LINE_REFS: <quoted passages that triggered concerns, or NONE>

JSON keys (--json):
    verdict, concerns, line_refs, task, model, thinking_trace (if thinking enabled)
"""

import argparse
import json
import os
import sys
from typing import Optional
import requests

# ── Config ──────────────────────────────────────────────────────────────────────
OLLAMA_URL   = "http://localhost:11434/api/chat"
MODEL        = "deepseek-r1:14b"
DEFAULT_MAX_TOKENS     = 2048
DEFAULT_NUM_CTX        = int(os.environ.get("PROOF_CHECKER_NUM_CTX",    "131072"))
DEFAULT_KEEP_ALIVE     = os.environ.get("PROOF_CHECKER_KEEP_ALIVE",     "15m")
DEFAULT_TIMEOUT_SECONDS = int(os.environ.get("PROOF_CHECKER_TIMEOUT",   "480"))

# ── System prompts ───────────────────────────────────────────────────────────────
_PREAMBLE = """\
You are an adversarial mathematical proof reviewer specialising in combinatorics and
number theory (Lonely Runner Conjecture, arithmetic-progression witnesses, modular
arithmetic).  Your job is to find genuine logical gaps, not style issues.

Important calibration:
- A "false negative" error is when you flag something that is actually proved elsewhere.
  Before flagging, check whether the proof appeals to a cited external lemma/file.
- Only report CONCERNS that represent genuine mathematical gaps or errors.
- Do NOT flag formatting, notation preference, or prose style.

"""

SYSTEM_PROMPTS = {
    "cases": _PREAMBLE + """\
TASK: Case-coverage audit.
Check whether the proof cases are:
1. EXHAUSTIVE — together they cover the entire parameter space (no gap).
2. NON-OVERLAPPING — no two cases handle identical regions (or overlap is harmless).
3. CORRECTLY CONCLUDED — each case actually reaches the claimed conclusion.

Output exactly:
VERDICT: [SOUND | CONCERNS | UNSOUND]
CONCERNS: <bullet list of genuine issues, or NONE>
LINE_REFS: <quoted short passages that triggered concerns, or NONE>
""",

    "arith": _PREAMBLE + """\
TASK: Arithmetic inequality audit.
For every numerical inequality or bound in the text:
1. Verify it is correct using exact arithmetic where possible (fractions, not decimals).
2. Flag any inequality stated without justification that looks suspicious.
3. Pay special attention to inequalities of the form X - Y > 0 or X/Y < 1.
   Example of a known error: (9/11)^8 - 16/69 was falsely claimed > 0; it equals ≈ -0.031 < 0.

Output exactly:
VERDICT: [SOUND | CONCERNS | UNSOUND]
CONCERNS: <bullet list with the specific inequality and its correct value, or NONE>
LINE_REFS: <quoted short passages that triggered concerns, or NONE>
""",

    "deps": _PREAMBLE + """\
TASK: Dependency chain audit.
Check that:
1. Every cited lemma, theorem, proposition, or external file name is either:
   (a) proved earlier in the same text, or
   (b) explicitly noted as proved in an external canonical file.
2. No circular dependencies exist (A cites B, B cites A).
3. The status claimed ("proved", "unconditional", "complete") is consistent with
   the stated dependencies.

Output exactly:
VERDICT: [SOUND | CONCERNS | UNSOUND]
CONCERNS: <bullet list of missing or circular citations, or NONE>
LINE_REFS: <quoted short passages that triggered concerns, or NONE>
""",
}

TASK_PRESETS = {
    "cases": {"max_tokens": 2048, "thinking_min_tokens": 3072, "num_ctx": 65536},
    "arith": {"max_tokens": 2048, "thinking_min_tokens": 4096, "num_ctx": 65536},
    "deps":  {"max_tokens": 1536, "thinking_min_tokens": 2048, "num_ctx": 65536},
}


# ── Core call ────────────────────────────────────────────────────────────────────

def _resolve_options(
    task: str,
    thinking: bool,
    max_tokens: Optional[int],
    num_ctx: Optional[int],
) -> tuple[int, int]:
    preset = TASK_PRESETS.get(task, {})
    explicit_max = max_tokens is not None
    resolved_max = max_tokens if explicit_max else preset.get("max_tokens", DEFAULT_MAX_TOKENS)
    resolved_ctx = num_ctx if num_ctx is not None else preset.get("num_ctx", DEFAULT_NUM_CTX)
    if thinking and not explicit_max:
        resolved_max = max(resolved_max, preset.get("thinking_min_tokens", DEFAULT_MAX_TOKENS))
    return resolved_max, resolved_ctx


def _call_model(
    prompt: str,
    task: str,
    thinking: bool,
    max_tokens: Optional[int],
    num_ctx: Optional[int],
    keep_alive: str,
    timeout_seconds: int,
    _allow_thinking_fallback: bool = True,
) -> dict:
    """Single call to DeepSeek R1 via Ollama for a given task."""
    temperature = 0.6 if thinking else 0.2
    max_tokens, num_ctx = _resolve_options(task, thinking, max_tokens, num_ctx)

    payload = {
        "model":      MODEL,
        "stream":     False,
        "think":      thinking,
        "keep_alive": keep_alive,
        "messages": [
            {"role": "system", "content": SYSTEM_PROMPTS[task]},
            {"role": "user",   "content": prompt},
        ],
        "options": {
            "temperature": temperature,
            "num_predict": max_tokens,
            "num_ctx":     num_ctx,
        },
    }

    try:
        resp = requests.post(OLLAMA_URL, json=payload, timeout=timeout_seconds)
        resp.raise_for_status()
    except requests.exceptions.ConnectionError:
        return {"error": "Cannot connect to Ollama at localhost:11434. Is it running?",
                "verdict": None, "content": "", "task": task}
    except requests.exceptions.Timeout:
        return {"error": f"Request timed out after {timeout_seconds}s.",
                "verdict": None, "content": "", "task": task}

    data = resp.json()
    msg  = data.get("message", {})
    content       = msg.get("content", "")
    thinking_text = msg.get("thinking", None)
    done_reason   = data.get("done_reason")

    # Fallback: thinking mode can exhaust token budget with no final content
    if thinking and not content.strip() and thinking_text and _allow_thinking_fallback:
        fallback = _call_model(
            prompt=prompt, task=task, thinking=False,
            max_tokens=max(max_tokens, 512), num_ctx=num_ctx,
            keep_alive=keep_alive, timeout_seconds=timeout_seconds,
            _allow_thinking_fallback=False,
        )
        fallback["thinking_trace"]       = thinking_text
        fallback["fallback_used"]        = True
        fallback["original_done_reason"] = done_reason
        return fallback

    # Parse structured fields
    verdict = concerns = line_refs = None
    for line in content.splitlines():
        s = line.strip()
        if s.startswith("VERDICT:"):
            verdict = s.split(":", 1)[-1].strip()
        elif s.startswith("CONCERNS:"):
            concerns = s.split(":", 1)[-1].strip()
        elif s.startswith("LINE_REFS:"):
            line_refs = s.split(":", 1)[-1].strip()

    result = {
        "verdict":   verdict,
        "concerns":  concerns,
        "line_refs": line_refs,
        "content":   content,
        "task":      task,
        "model":     data.get("model", MODEL),
        "done_reason": done_reason,
    }
    if thinking and thinking_text:
        result["thinking_trace"] = thinking_text
    return result


# ── Full (multi-task) runner ──────────────────────────────────────────────────────

def _aggregate(results: list[dict]) -> dict:
    """Combine multiple sub-task results into a single aggregated verdict."""
    all_concerns = []
    all_line_refs = []
    worst = "SOUND"
    for r in results:
        v = (r.get("verdict") or "").upper()
        if v == "UNSOUND":
            worst = "UNSOUND"
        elif v == "CONCERNS" and worst != "UNSOUND":
            worst = "CONCERNS"
        c = r.get("concerns")
        if c and c.upper() != "NONE":
            all_concerns.append(f"[{r['task'].upper()}] {c}")
        lr = r.get("line_refs")
        if lr and lr.upper() != "NONE":
            all_line_refs.append(f"[{r['task'].upper()}] {lr}")

    return {
        "verdict":   worst,
        "concerns":  "\n".join(all_concerns) if all_concerns else "NONE",
        "line_refs": "\n".join(all_line_refs) if all_line_refs else "NONE",
        "sub_tasks": results,
        "task":      "full",
        "model":     MODEL,
    }


def check_proof(
    proof_text: str,
    task: str = "full",
    thinking: bool = True,
    max_tokens: Optional[int] = None,
    num_ctx: Optional[int] = None,
    keep_alive: str = DEFAULT_KEEP_ALIVE,
    timeout_seconds: int = DEFAULT_TIMEOUT_SECONDS,
) -> dict:
    """
    Main entry point.

    task='full' runs cases + arith + deps and aggregates.
    Other tasks run a single check.
    """
    if task == "full":
        results = []
        for sub in ("cases", "arith", "deps"):
            r = _call_model(
                prompt=proof_text, task=sub, thinking=thinking,
                max_tokens=max_tokens, num_ctx=num_ctx,
                keep_alive=keep_alive, timeout_seconds=timeout_seconds,
            )
            results.append(r)
            if "error" in r:
                # Abort on connectivity errors
                return {"error": r["error"], "verdict": None, "task": "full"}
        return _aggregate(results)
    else:
        return _call_model(
            prompt=proof_text, task=task, thinking=thinking,
            max_tokens=max_tokens, num_ctx=num_ctx,
            keep_alive=keep_alive, timeout_seconds=timeout_seconds,
        )


# ── CLI ──────────────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(
        description="Adversarial proof-section reviewer backed by DeepSeek R1 (via Ollama)."
    )
    parser.add_argument("prompt",
        nargs="?", default=None,
        help="Proof text (omit to read from stdin)")
    parser.add_argument("--task", "-t",
        choices=["cases", "arith", "deps", "full"],
        default="full",
        help="Check to run: cases | arith | deps | full (default: full)")
    parser.add_argument("--no-thinking",
        action="store_true",
        help="Disable chain-of-thought (thinking is ON by default)")
    parser.add_argument("--max-tokens", "-m",
        type=int, default=None,
        help="Override max output tokens")
    parser.add_argument("--num-ctx",
        type=int, default=None,
        help=f"Override context window (default: {DEFAULT_NUM_CTX})")
    parser.add_argument("--keep-alive",
        default=DEFAULT_KEEP_ALIVE,
        help=f"Ollama model keep-alive (default: {DEFAULT_KEEP_ALIVE})")
    parser.add_argument("--timeout",
        type=int, default=DEFAULT_TIMEOUT_SECONDS,
        help=f"HTTP timeout in seconds (default: {DEFAULT_TIMEOUT_SECONDS})")
    parser.add_argument("--json", "-j",
        action="store_true",
        help="Output full JSON result")

    args = parser.parse_args()
    thinking = not args.no_thinking

    if args.prompt is None:
        if sys.stdin.isatty():
            print("Enter proof text (Ctrl+D to finish):", file=sys.stderr)
        proof_text = sys.stdin.read().strip()
    else:
        proof_text = args.prompt

    if not proof_text:
        print("Error: no proof text provided.", file=sys.stderr)
        sys.exit(1)

    result = check_proof(
        proof_text=proof_text,
        task=args.task,
        thinking=thinking,
        max_tokens=args.max_tokens,
        num_ctx=args.num_ctx,
        keep_alive=args.keep_alive,
        timeout_seconds=args.timeout,
    )

    if "error" in result:
        print(f"ERROR: {result['error']}", file=sys.stderr)
        sys.exit(1)

    if args.json:
        # Omit thinking traces from JSON to keep output readable
        def _strip(d):
            if isinstance(d, dict):
                return {k: _strip(v) for k, v in d.items() if k != "thinking_trace"}
            if isinstance(d, list):
                return [_strip(x) for x in d]
            return d
        out = _strip(result)
        # But do show thinking traces on stderr if they exist
        if thinking:
            for sub in result.get("sub_tasks", [result]):
                tr = sub.get("thinking_trace", "")
                if tr:
                    print(f"── THINKING [{sub.get('task','').upper()}] ────────────────────────────────────────────────────", file=sys.stderr)
                    print(tr, file=sys.stderr)
        print(json.dumps(out, indent=2))
    else:
        if thinking:
            for sub in result.get("sub_tasks", [result]):
                tr = sub.get("thinking_trace", "")
                if tr:
                    print(f"── THINKING [{sub.get('task','').upper()}] ────────────────────────────────────────────────────", file=sys.stderr)
                    print(tr, file=sys.stderr)
        print(f"VERDICT:   {result.get('verdict', 'N/A')}")
        print(f"CONCERNS:  {result.get('concerns', 'NONE')}")
        print(f"LINE_REFS: {result.get('line_refs', 'NONE')}")


if __name__ == "__main__":
    main()
