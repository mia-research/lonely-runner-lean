#!/usr/bin/env python3
"""
codex_subagent.py — OpenAI Codex CLI subagent for the Math Ex / LRC pipeline.

Mirrors qwen_subagent.py interface. Delegates CODE tasks to Codex so Claude
handles only judgment, escalation, and novel proof steps.

Usage (CLI):
    python3 tools/codex_subagent.py "your prompt" [--task TASK] [--json]

Tasks:
    harness    Generate a Python validation harness from a claim spec.
    analyze    Analyze CSV / numerical data for anomalies and statistics.
    refactor   Refactor or fix an existing Python script.
    review     Code review: find bugs, off-by-ones, edge cases.

Examples:
    python3 tools/codex_subagent.py "$(cat reports/harness/spec.md)" --task harness
    python3 tools/codex_subagent.py "$(head -50 lrc_efficiency_runtime_validation.csv)" --task analyze
    python3 tools/codex_subagent.py "$(cat tools/qwen_subagent.py)" --task review
"""

import argparse
import json
import os
import subprocess
import sys
import tempfile
from typing import Optional

# ── Config ───────────────────────────────────────────────────────────────────
DEFAULT_SANDBOX        = os.environ.get("CODEX_SANDBOX", "read-only")
DEFAULT_TIMEOUT        = int(os.environ.get("CODEX_TIMEOUT", "120"))
CODEX_API_KEY          = os.environ.get("OPENAI_API_KEY", "")

# ── System prompt prefixes per task ──────────────────────────────────────────
TASK_PROMPTS = {
    "harness": """\
You are a Python test-harness engineer for a mathematical research pipeline.
Given a claim specification, write a complete, self-contained Python 3 script
that validates the claim numerically. Include:
  - All imports at the top
  - A main() function
  - Clear pass/fail output with specific values
  - Threshold checks at 1e-9 (stable) and 1e-6 (sensitive)
Output only the Python script, no explanation.

CLAIM SPEC:
""",

    "analyze": """\
You are a data analysis engineer. Given CSV or tabular data, produce:
  SUMMARY: row/column counts, data types
  ANOMALIES: rows that violate expected patterns or thresholds (1e-9 stable, 1e-6 sensitive)
  STATISTICS: min, max, mean, std for numeric columns
  FLAGS: any values that need investigation
Be concise. Use bullet points.

DATA:
""",

    "refactor": """\
You are a Python refactoring engineer. Given a Python script:
  - Fix any bugs or logic errors
  - Improve clarity without changing behaviour
  - Remove dead code
  - Keep the same function signatures
Output only the corrected Python script, no explanation.

SCRIPT:
""",

    "review": """\
You are a Python code reviewer for a scientific pipeline.
Given a Python script, report:
  BUGS: logic errors, off-by-one errors, exception handling gaps
  EDGE_CASES: inputs that would cause silent failures
  IMPROVEMENTS: up to 3 concrete suggestions
  VERDICT: [PASS | NEEDS_FIX | CRITICAL]
Be concise and specific. Reference line numbers.

SCRIPT:
""",
}

# ── Core call ─────────────────────────────────────────────────────────────────

def call_codex(
    prompt: str,
    task: str = "review",
    sandbox: str = DEFAULT_SANDBOX,
    timeout: int = DEFAULT_TIMEOUT,
) -> dict:
    """
    Call Codex CLI non-interactively via `codex exec`.

    Returns:
        {
          "verdict":  str | None,
          "content":  str,
          "task":     str,
          "error":    str | None,
        }
    """
    if not CODEX_API_KEY:
        return {
            "error":   "OPENAI_API_KEY is not set. Add it to ~/.zshrc and restart terminal.",
            "verdict": None,
            "content": "",
            "task":    task,
        }

    task_prefix = TASK_PROMPTS.get(task, TASK_PROMPTS["review"])
    full_prompt = task_prefix + prompt

    # Write final output to a temp file — cleaner than parsing stdout stream
    with tempfile.NamedTemporaryFile(mode="w", suffix=".txt", delete=False) as tf:
        out_path = tf.name

    cmd = [
        "codex", "exec",
        "--sandbox", sandbox,
        "--ephemeral",
        "--skip-git-repo-check",
        "-o", out_path,
        full_prompt,
    ]

    try:
        result = subprocess.run(
            cmd,
            capture_output=True,
            text=True,
            timeout=timeout,
            env={**os.environ, "OPENAI_API_KEY": CODEX_API_KEY},
        )
    except FileNotFoundError:
        return {
            "error":   "codex not found. Run: npm install -g @openai/codex",
            "verdict": None,
            "content": "",
            "task":    task,
        }
    except subprocess.TimeoutExpired:
        return {
            "error":   f"Codex timed out after {timeout}s.",
            "verdict": None,
            "content": "",
            "task":    task,
        }

    # Read the output file
    try:
        with open(out_path) as f:
            content = f.read().strip()
    except FileNotFoundError:
        content = result.stdout.strip()  # fallback to stdout if -o failed
    finally:
        try:
            os.unlink(out_path)
        except OSError:
            pass

    if result.returncode != 0 and not content:
        return {
            "error":   f"codex exited {result.returncode}: {result.stderr.strip()[:300]}",
            "verdict": None,
            "content": "",
            "task":    task,
        }

    # Parse VERDICT line if present
    verdict = None
    for line in content.splitlines():
        stripped = line.strip()
        if stripped.startswith("VERDICT:"):
            verdict = stripped.split(":", 1)[-1].strip()
            break

    return {
        "verdict": verdict,
        "content": content,
        "task":    task,
        "error":   None,
    }


# ── LRC pipeline helpers ──────────────────────────────────────────────────────

def generate_harness(spec_text: str) -> dict:
    """Generate a Python validation harness from a claim spec."""
    return call_codex(spec_text, task="harness")


def analyze_data(csv_text: str) -> dict:
    """Analyze CSV/tabular data for anomalies."""
    return call_codex(csv_text, task="analyze")


def refactor_script(script_text: str) -> dict:
    """Refactor or fix a Python script."""
    return call_codex(script_text, task="refactor", sandbox="workspace-write")


def review_script(script_text: str) -> dict:
    """Code review a Python script."""
    return call_codex(script_text, task="review")


# ── CLI ───────────────────────────────────────────────────────────────────────

def main():
    parser = argparse.ArgumentParser(
        description="Codex CLI subagent for the LRC pipeline."
    )
    parser.add_argument("prompt",
        nargs="?", default=None,
        help="Prompt text (omit to read from stdin)")
    parser.add_argument("--task", "-t",
        choices=list(TASK_PROMPTS.keys()),
        default="review",
        help="Task type (default: review)")
    parser.add_argument("--sandbox", "-s",
        default=DEFAULT_SANDBOX,
        help=f"Codex sandbox level (default: {DEFAULT_SANDBOX})")
    parser.add_argument("--timeout",
        type=int, default=DEFAULT_TIMEOUT,
        help=f"Timeout in seconds (default: {DEFAULT_TIMEOUT})")
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

    result = call_codex(
        prompt=prompt,
        task=args.task,
        sandbox=args.sandbox,
        timeout=args.timeout,
    )

    if result.get("error"):
        print(f"ERROR: {result['error']}", file=sys.stderr)
        sys.exit(1)

    if args.json:
        print(json.dumps(result, indent=2))
    else:
        print(result["content"])


if __name__ == "__main__":
    main()
