#!/usr/bin/env python3
"""
local_llm.py — ZCode's unified internal API over the local Ollama server.

Lives in .zcode/ (ZCode's own directory). It does NOT modify or import the
existing tools/{qwen,gemma4,deepseek}_subagent.py wrappers — those remain
standalone and untouched. This module is a parallel façade over the same
Ollama server (localhost:11434), exposing one consistent interface to all
three installed chat models.

Usage (CLI):
    python3 .zcode/local_llm.py "your prompt" \\
        [--model qwen|gemma4|deepseek] [--task prescreening|verify|math|draft|dedup] \\
        [--thinking] [--json] [--health]

Usage (import):
    # from the repo root
    import sys; sys.path.insert(0, ".zcode")
    from local_llm import ask, verify, prescreen, dedup, math, draft, health

    r = ask("phi(5)=?", model="qwen", task="math")
    print(r["content"], r["verdict"])

Model routing (advisory — never a verdict, per proof-not-test):
    qwen      (qwen3.5:4b)     FAST/CHEAP: prescreening, drafts, simple dedup
    gemma4    (gemma4:26b)     MEDIUM: review, second opinion, moderate math
    deepseek  (deepseek-r1:14b) HARD: multi-step proofs, adversarial review, hard dedup

Notes:
    - Native Ollama /api/chat only (more reliable than OpenAI-compat for `think`).
    - Per-model tuning (token budgets, context windows, timeouts, prompt overlays)
      lives in `MODELS` as DATA, not code.
    - The `local-qwen-ollama-subagent` skill is the workflow doc; this module is
      the importable API behind it.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
from typing import Optional
import requests

# ── Config ──────────────────────────────────────────────────────────────────────
OLLAMA_URL = os.environ.get("OLLAMA_URL", "http://localhost:11434/api/chat")
OLLAMA_TAGS_URL = OLLAMA_URL.replace("/api/chat", "/api/tags")

STABLE_THRESHOLD = 1e-9
SENSITIVE_THRESHOLD = 1e-6

# Base (terse) system prompts. gemma4/deepseek add task-specific reasoning
# prefixes via PROMPT_OVERLAYS below.
BASE_SYSTEM_PROMPTS = {
    "prescreening": """\
You are a fast mathematical claim pre-screener for the LRC adjudication pipeline.
Flag obvious inconsistencies, undefined terms, or threshold violations. Be brief.
Output exactly:
VERDICT: [PASS | FLAG | ESCALATE]
REASON: <one sentence>
""",

    "verify": f"""\
You are a mathematical verification assistant for the LRC claim pipeline.
Check for:
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
Show derivations step by step. Be precise about quantifiers.
Flag any step relying on an unproven assumption.
Use: phi(n) for Euler's totient, gcd, lcm, Z/nZ.
""",

    "draft": """\
You are a technical writing assistant for mathematical research.
Produce clean, structured prose suitable for a formalization package.
Tone: preprint-style — precise, concise, no padding.
""",

    "dedup": """\
You are a claim deduplication assistant.
Given CLAIM-A and CLAIM-B, determine if they are:
  IDENTICAL   — same math content, different wording
  OVERLAPPING — one is a special case or subset of the other
  DISTINCT    — genuinely different claims
Output:
RELATION: [IDENTICAL | OVERLAPPING | DISTINCT]
EXPLANATION: <2-3 sentences>
RECOMMENDATION: [MERGE | KEEP_BOTH | ESCALATE]
""",
}

# Per-model task prompt overlays. Only the tasks that differ from base are
# listed; everything else falls back to BASE_SYSTEM_PROMPTS[task].
PROMPT_OVERLAYS = {
    "gemma4": {
        "verify": BASE_SYSTEM_PROMPTS["verify"].replace(
            "You are a mathematical verification assistant for the LRC claim pipeline.\n",
            "You are a mathematical verification assistant for the LRC claim pipeline.\n"
            "Think carefully before responding. ",
        ),
        "math": BASE_SYSTEM_PROMPTS["math"] + "Show all intermediate steps — do not skip algebra.\n",
        "dedup": BASE_SYSTEM_PROMPTS["dedup"].replace(
            "Given CLAIM-A and CLAIM-B, determine if they are:",
            "Given CLAIM-A and CLAIM-B, think carefully about mathematical equivalence before deciding.\n"
            "Determine if they are:",
        ),
    },
    "deepseek": {
        "verify": BASE_SYSTEM_PROMPTS["verify"].replace(
            "You are a mathematical verification assistant for the LRC claim pipeline.\n",
            "You are a mathematical verification assistant for the LRC claim pipeline.\n"
            "Think carefully before responding. ",
        ),
        "math": BASE_SYSTEM_PROMPTS["math"].replace(
            "Show derivations step by step.",
            "Think step by step through each derivation.",
        ) + "Show all intermediate steps — do not skip algebra.\n",
        "dedup": BASE_SYSTEM_PROMPTS["dedup"].replace(
            "Given CLAIM-A and CLAIM-B, determine if they are:",
            "Given CLAIM-A and CLAIM-B, think carefully about mathematical equivalence before deciding.\n"
            "Determine if they are:",
        ),
    },
}

# ── Model registry ──────────────────────────────────────────────────────────────
# Per-model tuning as DATA. Tags match what's actually installed in the local
# Ollama (verified 2026-07-23): qwen3.5:4b, gemma4:26b, deepseek-r1:14b.
MODELS: dict[str, dict] = {
    "qwen": {
        "tag": "qwen3.5:4b",
        "max_tokens": 1024,
        "num_ctx": 32768,
        "timeout": 180,
        "default_deep": False,
        "handle_404": False,
        "presets": {
            "verify": {"max_tokens": 1280, "thinking_min_tokens": 1536, "num_ctx": 49152},
            "math":  {"max_tokens": 1536, "thinking_min_tokens": 2048, "num_ctx": 65536},
        },
    },
    "gemma4": {
        "tag": "gemma4:26b",
        "max_tokens": 1024,
        "num_ctx": 32768,
        "timeout": 240,
        "default_deep": False,
        "handle_404": True,
        "presets": {
            "prescreening": {"max_tokens": 200,  "num_ctx": 16384},
            "verify":       {"max_tokens": 1280, "thinking_min_tokens": 1536, "num_ctx": 32768},
            "math":         {"max_tokens": 1536, "thinking_min_tokens": 2048, "num_ctx": 49152},
            "dedup":        {"max_tokens": 768,  "thinking_min_tokens": 1024, "num_ctx": 32768},
        },
    },
    "deepseek": {
        "tag": "deepseek-r1:14b",
        "max_tokens": 1536,
        "num_ctx": 65536,
        "timeout": 360,
        "default_deep": True,   # deepseek helpers historically defaulted to CoT
        "handle_404": True,
        "presets": {
            "prescreening": {"max_tokens": 200,  "num_ctx": 32768},
            "verify":       {"max_tokens": 1536, "thinking_min_tokens": 2048, "num_ctx": 65536},
            "math":         {"max_tokens": 2048, "thinking_min_tokens": 4096, "num_ctx": 131072},
            "dedup":        {"max_tokens": 768,  "thinking_min_tokens": 1536, "num_ctx": 49152},
        },
    },
}

# Alias map: accept legacy tags / common spellings and resolve to a registry key.
_TAG_ALIASES = {
    "qwen": "qwen", "qwen3.5": "qwen", "qwen3.5:4b": "qwen",
    "gemma": "gemma4", "gemma4": "gemma4", "gemma4:26b": "gemma4",
    "deepseek": "deepseek", "deepseek-r1": "deepseek", "deepseek-r1:14b": "deepseek",
    "r1": "deepseek",
}

DEFAULT_MODEL = "qwen"
DEFAULT_KEEP_ALIVE = "15m"


# ── Resolution helpers ──────────────────────────────────────────────────────────

def _resolve_model(model: str) -> str:
    """Map a model key or legacy tag to a registry key. Raises ValueError if unknown."""
    key = _TAG_ALIASES.get(model)
    if key is None:
        for k, cfg in MODELS.items():
            if cfg["tag"] == model:
                return k
        raise ValueError(
            f"Unknown model {model!r}. Known: {sorted(MODELS)} "
            f"or tags {[c['tag'] for c in MODELS.values()]}"
        )
    return key


def _resolve_task_options(
    model_key: str,
    task: str,
    thinking: bool,
    max_tokens: Optional[int],
    num_ctx: Optional[int],
) -> tuple[int, int]:
    """Apply per-model task presets unless the caller explicitly overrides."""
    cfg = MODELS[model_key]
    preset = cfg["presets"].get(task, {})
    explicit_max_tokens = max_tokens is not None

    resolved_max_tokens = (
        max_tokens if max_tokens is not None
        else preset.get("max_tokens", cfg["max_tokens"])
    )
    resolved_num_ctx = (
        num_ctx if num_ctx is not None
        else preset.get("num_ctx", cfg["num_ctx"])
    )

    if thinking and not explicit_max_tokens:
        resolved_max_tokens = max(
            resolved_max_tokens,
            preset.get("thinking_min_tokens", cfg["max_tokens"]),
        )
    return resolved_max_tokens, resolved_num_ctx


def _system_prompt(model_key: str, task: str) -> str:
    base = BASE_SYSTEM_PROMPTS.get(task, BASE_SYSTEM_PROMPTS["verify"])
    overlay = PROMPT_OVERLAYS.get(model_key, {})
    return overlay.get(task, base)


# ── Core call ───────────────────────────────────────────────────────────────────

def ask(
    prompt: str,
    model: str = DEFAULT_MODEL,
    task: str = "verify",
    thinking: bool = False,
    max_tokens: Optional[int] = None,
    temperature: Optional[float] = None,
    num_ctx: Optional[int] = None,
    keep_alive: Optional[str] = None,
    timeout: Optional[int] = None,
    _allow_thinking_fallback: bool = True,
) -> dict:
    """
    Call a local model via Ollama native /api/chat.

    Args:
        prompt:      user prompt text.
        model:       registry key (qwen|gemma4|deepseek) or legacy tag.
        task:        one of prescreening|verify|math|draft|dedup.
        thinking:    enable chain-of-thought (Ollama native `think` param).
        max_tokens:  override num_predict (task presets apply when omitted).
        temperature: default 0.2 (0.7 when thinking).
        num_ctx:     override context window (task presets apply when omitted).
        keep_alive:  how long Ollama keeps the model warm (default 15m).
        timeout:     HTTP timeout in seconds (per-model default when omitted).

    Returns:
        {
          "verdict":        str | None,   # parsed from a `VERDICT:` line if present
          "content":        str,
          "thinking_trace": str | None,   # only when thinking=True
          "task":           str,
          "model":          str,          # Ollama-reported tag
          "thinking":       bool,
          "done_reason":    str | None,
          "max_tokens":     int,
          "num_ctx":        int,
          "keep_alive":     str,
          "fallback_used":  bool,         # True if CoT ate the budget and we reran
        }
        On transport failure: {"error": ..., "verdict": None, "content": "", ...}
    """
    if temperature is None:
        temperature = 0.7 if thinking else 0.2
    if keep_alive is None:
        keep_alive = DEFAULT_KEEP_ALIVE

    model_key = _resolve_model(model)
    cfg = MODELS[model_key]
    tag = cfg["tag"]
    if timeout is None:
        timeout = cfg["timeout"]

    max_tokens, num_ctx = _resolve_task_options(model_key, task, thinking, max_tokens, num_ctx)

    payload = {
        "model": tag,
        "stream": False,
        "think": thinking,
        "keep_alive": keep_alive,
        "messages": [
            {"role": "system", "content": _system_prompt(model_key, task)},
            {"role": "user", "content": prompt},
        ],
        "options": {
            "temperature": temperature,
            "num_predict": max_tokens,
            "num_ctx": num_ctx,
        },
    }

    try:
        resp = requests.post(OLLAMA_URL, json=payload, timeout=timeout)
        resp.raise_for_status()
    except requests.exceptions.ConnectionError:
        return _err("Cannot connect to Ollama at " + OLLAMA_URL + ". Is it running?", task, tag)
    except requests.exceptions.Timeout:
        return _err(f"Request timed out after {timeout}s.", task, tag)
    except requests.exceptions.HTTPError as e:
        if e.response is not None and e.response.status_code == 404 and cfg["handle_404"]:
            return _err(f"Model '{tag}' not found in Ollama. Run: ollama pull {tag}", task, tag)
        return _err(f"HTTP error from Ollama: {e}", task, tag)

    data = resp.json()
    msg = data.get("message", {})

    content = msg.get("content", "")
    thinking_text = msg.get("thinking", None)
    done_reason = data.get("done_reason")

    # Thinking mode can exhaust the output budget on the trace and return no
    # final answer. Fall back to a non-thinking pass so the caller still gets
    # a usable result.
    if thinking and not content.strip() and thinking_text and _allow_thinking_fallback:
        fallback = ask(
            prompt=prompt,
            model=model_key,
            task=task,
            thinking=False,
            max_tokens=max(max_tokens, 512),
            temperature=0.2,
            num_ctx=num_ctx,
            keep_alive=keep_alive,
            timeout=timeout,
            _allow_thinking_fallback=False,
        )
        fallback["thinking"] = True
        fallback["thinking_trace"] = thinking_text
        fallback["fallback_used"] = True
        fallback["fallback_reason"] = (
            "thinking mode returned no final content; reran once with think=false"
        )
        fallback["original_done_reason"] = done_reason
        fallback["num_ctx"] = num_ctx
        fallback["keep_alive"] = keep_alive
        return fallback

    verdict = _parse_verdict(content)

    result = {
        "verdict": verdict,
        "content": content,
        "task": task,
        "model": data.get("model", tag),
        "thinking": thinking,
        "done_reason": done_reason,
        "max_tokens": max_tokens,
        "num_ctx": num_ctx,
        "keep_alive": keep_alive,
        "fallback_used": False,
    }
    if thinking and thinking_text:
        result["thinking_trace"] = thinking_text
    return result


def _err(message: str, task: str, tag: str) -> dict:
    return {"error": message, "verdict": None, "content": "", "task": task, "model": tag}


def _parse_verdict(content: str) -> Optional[str]:
    for line in content.splitlines():
        stripped = line.strip()
        if stripped.startswith("VERDICT:"):
            return stripped.split(":", 1)[-1].strip()
    return None


# ── Task convenience wrappers ───────────────────────────────────────────────────
# Each preserves the per-model historical default: deepseek defaults to
# thinking=True for verify/dedup/math; qwen and gemma4 default to thinking=False.
# Callers can always pass thinking= explicitly.

def prescreen(text: str, model: str = DEFAULT_MODEL) -> dict:
    """Fast pre-screen — use before quorum to catch obvious issues."""
    return ask(text, model=model, task="prescreening", max_tokens=200)


def verify(text: str, model: str = DEFAULT_MODEL, deep: Optional[bool] = None) -> dict:
    """Full verification. `deep` defaults to the model's historical default."""
    if deep is None:
        deep = MODELS[_resolve_model(model)]["default_deep"]
    return ask(text, model=model, task="verify", thinking=deep)


def dedup(claim_a: str, claim_b: str, model: str = DEFAULT_MODEL, deep: Optional[bool] = None) -> dict:
    """Check whether two claims are duplicates."""
    if deep is None:
        deep = MODELS[_resolve_model(model)]["default_deep"]
    prompt = f"CLAIM-A:\n{claim_a}\n\nCLAIM-B:\n{claim_b}"
    return ask(prompt, model=model, task="dedup", thinking=deep)


def math(problem: str, model: str = DEFAULT_MODEL, deep: Optional[bool] = None) -> dict:
    """Symbolic / formula check."""
    if deep is None:
        deep = MODELS[_resolve_model(model)]["default_deep"]
    return ask(problem, model=model, task="math", thinking=deep)


def draft(instructions: str, model: str = DEFAULT_MODEL) -> dict:
    """Preprint-style prose drafting."""
    return ask(instructions, model=model, task="draft")


# ── Ops helpers ─────────────────────────────────────────────────────────────────

def list_models() -> list[str]:
    """Registry keys this module knows how to route to."""
    return sorted(MODELS)


def health() -> dict:
    """
    Ping Ollama and report which configured models are currently loaded.

    Returns:
        {
          "ollama_reachable": bool,
          "loaded_tags":      [str, ...],   # every model Ollama currently has
          "configured":       {key: {"tag": str, "loaded": bool, "presets": [...]}},
        }
    """
    out = {"ollama_reachable": False, "loaded_tags": [], "configured": {}}
    try:
        r = requests.get(OLLAMA_TAGS_URL, timeout=10)
        r.raise_for_status()
        out["ollama_reachable"] = True
        out["loaded_tags"] = [m["name"] for m in r.json().get("models", [])]
    except Exception as e:
        out["error"] = f"Cannot reach Ollama at {OLLAMA_TAGS_URL}: {e}"
        return out

    loaded = set(out["loaded_tags"])
    for key, cfg in MODELS.items():
        out["configured"][key] = {
            "tag": cfg["tag"],
            "loaded": cfg["tag"] in loaded or key in loaded,
            "presets": sorted(cfg["presets"]),
        }
    return out


# ── CLI ─────────────────────────────────────────────────────────────────────────

def _build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="local_llm.py",
        description="ZCode unified internal API over the local Ollama server.",
    )
    p.add_argument("prompt", nargs="?", default=None,
                   help="Prompt text (omit to read from stdin)")
    p.add_argument("--model", "-M", default=DEFAULT_MODEL,
                   choices=sorted(MODELS),
                   help=f"Model key (default: {DEFAULT_MODEL}). "
                        f"Routing: qwen=fast/cheap, gemma4=medium, deepseek=hard.")
    p.add_argument("--task", "-t",
                   choices=list(BASE_SYSTEM_PROMPTS),
                   default="verify",
                   help="Task type (default: verify)")
    p.add_argument("--thinking", "-T", action="store_true",
                   help="Enable chain-of-thought (slower, more thorough)")
    p.add_argument("--max-tokens", "-m", type=int, default=None,
                   help="Override max output tokens (task presets apply when omitted)")
    p.add_argument("--num-ctx", type=int, default=None,
                   help="Override context window (task presets apply when omitted)")
    p.add_argument("--keep-alive", default=DEFAULT_KEEP_ALIVE,
                   help=f"How long Ollama should keep the model warm (default: {DEFAULT_KEEP_ALIVE})")
    p.add_argument("--timeout", type=int, default=None,
                   help="HTTP timeout in seconds (per-model default when omitted)")
    p.add_argument("--json", "-j", action="store_true",
                   help="Output full JSON result")
    p.add_argument("--health", action="store_true",
                   help="Print Ollama/model health and exit")
    return p


def main() -> None:
    args = _build_parser().parse_args()

    if args.health:
        print(json.dumps(health(), indent=2))
        return

    if args.prompt is None:
        if sys.stdin.isatty():
            print("Enter prompt (Ctrl+D to finish):", file=sys.stderr)
        prompt = sys.stdin.read().strip()
    else:
        prompt = args.prompt

    if not prompt:
        print("Error: no prompt provided.", file=sys.stderr)
        sys.exit(1)

    result = ask(
        prompt=prompt,
        model=args.model,
        task=args.task,
        thinking=args.thinking,
        max_tokens=args.max_tokens,
        num_ctx=args.num_ctx,
        keep_alive=args.keep_alive,
        timeout=args.timeout,
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
