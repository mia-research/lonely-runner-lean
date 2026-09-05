#!/usr/bin/env python3
"""
gemma4_subagent.py — Local Gemma 4 subagent for the Math Ex / LRC pipeline.

Uses the Ollama native /api/chat endpoint. Gemma 4 has built-in chain-of-thought
reasoning; pass --thinking to enable extended reasoning mode.

Usage (CLI):
    python3 tools/gemma4_subagent.py "your prompt" [--task TASK] [--thinking] [--json]

Tasks:
    prescreening   Fast first-pass: is this claim internally consistent?
    verify         Detailed verification with threshold checks.
    math           Symbolic/formula check — use --thinking for full CoT.
    draft          Prose drafting: quorum prompts, addenda, summaries.
    dedup          Check if two claims are substantively identical.

Examples:
    python3 tools/gemma4_subagent.py "phi(5)=4, fi=1/(n*delta) to 5e-13" --task math
    python3 tools/gemma4_subagent.py "$(cat reports/formalization/CLAIM-LRC-000062/formal_claim.md)" --task verify
    python3 tools/gemma4_subagent.py "CLAIM-A: ... CLAIM-B: ..." --task dedup --json

Pipeline role:
    Use Gemma 4 for MEDIUM tasks: draft review, second opinion on Qwen output,
    moderate symbolic math, moderately ambiguous dedup.
    Use Qwen for FAST/CHEAP tasks: prescreening, routine drafts, simple dedup.
    Use DeepSeek for HARD tasks: multi-step proofs, adversarial review, hard dedup.

Prerequisites:
    Ollama >= 0.6.x must be installed and running.
    Run: ollama pull gemma4:12b  (or gemma4:2b / gemma4:27b for smaller/larger)
"""

import argparse
import json
import os
import sys
from typing import Optional
import requests

# ── Config ──────────────────────────────────────────────────────────────────────
OLLAMA_URL  = "http://localhost:11434/api/chat"
MODEL       = "gemma4"
DEFAULT_MAX_TOKENS      = 1024
DEFAULT_NUM_CTX         = int(os.environ.get("GEMMA4_SUBAGENT_NUM_CTX",    "32768"))
DEFAULT_KEEP_ALIVE      = os.environ.get("GEMMA4_SUBAGENT_KEEP_ALIVE",     "15m")
DEFAULT_TIMEOUT_SECONDS = int(os.environ.get("GEMMA4_SUBAGENT_TIMEOUT",    "240"))

STABLE_THRESHOLD    = 1e-9
SENSITIVE_THRESHOLD = 1e-6

# ── System prompts ───────────────────────────────────────────────────────────────
SYSTEM_PROMPTS = {
    "prescreening": """\
You are a fast mathematical claim pre-screener for the LRC adjudication pipeline.
Flag obvious inconsistencies, undefined terms, or threshold violations. Be brief.
Output exactly:
VERDICT: [PASS | FLAG | ESCALATE]
REASON: <one sentence>
""",

    "verify": f"""\
You are a mathematical verification assistant for the LRC claim pipeline.
Think carefully before responding. Check for:
1. Internal consistency of assumptions and conclusions.
2. Correct use of metric definitions: phi(n), isolation count, fi, delta.
3. Threshold compliance — stable bound: {STABLE_THRESHOLD}, sensitive: {SENSITIVE_THRESHOLD}.
4. Any arithmetic or formula errors.

Output format:
VERDICT: [CONSISTENT | INCONSISTENT | NEEDS_ESCALATION]
ISSUES: <bullet list, or NONE>
THRESHOLD_FLAGS: <list values exceeding bounds, or NONE>
CONFIDENCE: [HIGH | MEDIUM | LOW]
""",

    "math": """\
You are a symbolic mathematics assistant specialising in number theory and combinatorics.
Think step by step through each derivation. Be precise about quantifiers.
Flag any step relying on an unproven assumption.
Use: phi(n) for Euler's totient, gcd, lcm, Z/nZ.
Show all intermediate steps — do not skip algebra.
""",

    "draft": """\
You are a technical writing assistant for mathematical research.
Produce clean, structured prose suitable for a formalization package.
Tone: preprint-style — precise, concise, no padding.
""",

    "dedup": """\
You are a claim deduplication assistant.
Given CLAIM-A and CLAIM-B, think carefully about mathematical equivalence before deciding.
Determine if they are:
  IDENTICAL   — same math content, different wording
  OVERLAPPING — one is a special case or subset of the other
  DISTINCT    — genuinely different claims
Output:
RELATION: [IDENTICAL | OVERLAPPING | DISTINCT]
EXPLANATION: <2-3 sentences>
RECOMMENDATION: [MERGE | KEEP_BOTH | ESCALATE]
""",
}

TASK_PRESETS = {
    "prescreening": {
        "max_tokens": 200,
        "num_ctx": 16384,
    },
    "verify": {
        "max_tokens": 1280,
        "thinking_min_tokens": 1536,
        "num_ctx": 32768,
    },
    "math": {
        "max_tokens": 1536,
        "thinking_min_tokens": 2048,
        "num_ctx": 49152,
    },
    "dedup": {
        "max_tokens": 768,
        "thinking_min_tokens": 1024,
        "num_ctx": 32768,
    },
}


def resolve_task_options(
    task: str,
    thinking: bool,
    max_tokens: Optional[int],
    num_ctx: Optional[int],
) -> tuple[int, int]:
    """Apply task presets unless the caller explicitly overrides them."""
    preset = TASK_PRESETS.get(task, {})
    explicit_max_tokens = max_tokens is not None

    resolved_max_tokens = (
        max_tokens if max_tokens is not None
        else preset.get("max_tokens", DEFAULT_MAX_TOKENS)
    )
    resolved_num_ctx = (
        num_ctx if num_ctx is not None
        else preset.get("num_ctx", DEFAULT_NUM_CTX)
    )

    if thinking and not explicit_max_tokens:
        resolved_max_tokens = max(
            resolved_max_tokens,
            preset.get("thinking_min_tokens", DEFAULT_MAX_TOKENS),
        )

    return resolved_max_tokens, resolved_num_ctx


# ── Core call ────────────────────────────────────────────────────────────────────

def call_gemma4(
    prompt: str,
    task: str = "verify",
    thinking: bool = False,
    max_tokens: Optional[int] = None,
    temperature: float = None,
    model: str = MODEL,
    num_ctx: Optional[int] = None,
    keep_alive: str = DEFAULT_KEEP_ALIVE,
    timeout_seconds: int = DEFAULT_TIMEOUT_SECONDS,
    _allow_thinking_fallback: bool = True,
) -> dict:
    """
    Call local Gemma 4 via Ollama native API.

    Returns:
        {
          "verdict":        str | None,
          "content":        str,
          "thinking_trace": str | None,   # populated when thinking=True
          "task":           str,
          "model":          str,
        }
    """
    if temperature is None:
        temperature = 0.7 if thinking else 0.2

    max_tokens, num_ctx = resolve_task_options(task, thinking, max_tokens, num_ctx)

    payload = {
        "model":      model,
        "stream":     False,
        "think":      thinking,          # Ollama native param for CoT
        "keep_alive": keep_alive,
        "messages": [
            {"role": "system", "content": SYSTEM_PROMPTS.get(task, SYSTEM_PROMPTS["verify"])},
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
                "verdict": None, "content": "", "task": task, "model": model}
    except requests.exceptions.Timeout:
        return {"error": f"Request timed out after {timeout_seconds}s.",
                "verdict": None, "content": "", "task": task, "model": model}
    except requests.exceptions.HTTPError as e:
        if e.response is not None and e.response.status_code == 404:
            return {"error": f"Model '{model}' not found in Ollama. Run: ollama pull {model}",
                    "verdict": None, "content": "", "task": task, "model": model}
        return {"error": f"HTTP error from Ollama: {e}",
                "verdict": None, "content": "", "task": task, "model": model}

    data = resp.json()
    msg  = data.get("message", {})

    content       = msg.get("content", "")
    thinking_text = msg.get("thinking", None)
    done_reason   = data.get("done_reason")

    # Thinking mode can exhaust the output budget on the trace and return no final answer.
    # Fall back to a non-thinking pass so the caller still gets a usable result.
    if (
        thinking
        and not content.strip()
        and thinking_text
        and _allow_thinking_fallback
    ):
        fallback = call_gemma4(
            prompt=prompt,
            task=task,
            thinking=False,
            max_tokens=max(max_tokens, 512),
            temperature=0.2,
            model=model,
            num_ctx=num_ctx,
            keep_alive=keep_alive,
            timeout_seconds=timeout_seconds,
            _allow_thinking_fallback=False,
        )
        fallback["thinking"]             = True
        fallback["thinking_trace"]       = thinking_text
        fallback["fallback_used"]        = True
        fallback["fallback_reason"]      = (
            "thinking mode returned no final content; reran once with think=false"
        )
        fallback["original_done_reason"] = done_reason
        fallback["num_ctx"]              = num_ctx
        fallback["keep_alive"]           = keep_alive
        return fallback

    # Parse VERDICT line if present
    verdict = None
    for line in content.splitlines():
        stripped = line.strip()
        if stripped.startswith("VERDICT:"):
            verdict = stripped.split(":", 1)[-1].strip()
            break

    result = {
        "verdict":     verdict,
        "content":     content,
        "task":        task,
        "model":       data.get("model", model),
        "thinking":    thinking,
        "done_reason": done_reason,
        "max_tokens":  max_tokens,
        "num_ctx":     num_ctx,
        "keep_alive":  keep_alive,
    }
    if thinking and thinking_text:
        result["thinking_trace"] = thinking_text

    return result


# ── LRC pipeline helpers ─────────────────────────────────────────────────────────

def prescreen_claim(claim_text: str) -> dict:
    """Fast pre-screen — use before quorum to catch obvious issues."""
    return call_gemma4(claim_text, task="prescreening", max_tokens=200)


def verify_claim(claim_text: str, deep: bool = False) -> dict:
    """Verification. deep=True enables chain-of-thought."""
    return call_gemma4(claim_text, task="verify", thinking=deep)


def check_dedup(claim_a: str, claim_b: str, deep: bool = False) -> dict:
    """Check if two claims are duplicates."""
    prompt = f"CLAIM-A:\n{claim_a}\n\nCLAIM-B:\n{claim_b}"
    return call_gemma4(prompt, task="dedup", thinking=deep)


def solve_math(problem: str, deep: bool = False) -> dict:
    """Symbolic math. deep=True enables chain-of-thought."""
    return call_gemma4(problem, task="math", thinking=deep)


def draft_addendum(instructions: str) -> dict:
    """Draft a quorum_prompt_addendum.md from high-level instructions."""
    return call_gemma4(instructions, task="draft")


# ── CLI ──────────────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(
        description="Local Gemma 4 subagent for the LRC pipeline (via Ollama)."
    )
    parser.add_argument("prompt",
        nargs="?", default=None,
        help="Prompt text (omit to read from stdin)")
    parser.add_argument("--task", "-t",
        choices=list(SYSTEM_PROMPTS.keys()),
        default="verify",
        help="Task type (default: verify)")
    parser.add_argument("--thinking", "-T",
        action="store_true",
        help="Enable chain-of-thought reasoning (slower, more thorough)")
    parser.add_argument("--max-tokens", "-m",
        type=int, default=None,
        help="Override max output tokens (task presets apply when omitted)")
    parser.add_argument("--model",
        default=MODEL,
        help=f"Override Ollama model (default: {MODEL})")
    parser.add_argument("--num-ctx",
        type=int, default=None,
        help=f"Override context window (task presets apply; base default: {DEFAULT_NUM_CTX})")
    parser.add_argument("--keep-alive",
        default=DEFAULT_KEEP_ALIVE,
        help=f"How long Ollama should keep the model warm (default: {DEFAULT_KEEP_ALIVE})")
    parser.add_argument("--timeout",
        type=int, default=DEFAULT_TIMEOUT_SECONDS,
        help=f"HTTP timeout in seconds (default: {DEFAULT_TIMEOUT_SECONDS})")
    parser.add_argument("--json", "-j",
        action="store_true",
        help="Output full JSON result")

    args = parser.parse_args()

    if args.prompt is None:
        if sys.stdin.isatty():
            print("Enter prompt (Ctrl+D to finish):", file=sys.stderr)
        prompt = sys.stdin.read().strip()
    else:
        prompt = args.prompt

    if not prompt:
        print("Error: no prompt provided.", file=sys.stderr)
        sys.exit(1)

    result = call_gemma4(
        prompt=prompt,
        task=args.task,
        thinking=args.thinking,
        max_tokens=args.max_tokens,
        model=args.model,
        num_ctx=args.num_ctx,
        keep_alive=args.keep_alive,
        timeout_seconds=args.timeout,
    )

    if "error" in result:
        print(f"ERROR: {result['error']}", file=sys.stderr)
        sys.exit(1)

    if args.json:
        print(json.dumps(result, indent=2))
    else:
        if args.thinking and result.get("thinking_trace"):
            print("── THINKING ────────────────────────────────────────────────────", file=sys.stderr)
            print(result["thinking_trace"], file=sys.stderr)
            print("── ANSWER ──────────────────────────────────────────────────────", file=sys.stderr)
        print(result["content"])


if __name__ == "__main__":
    main()
