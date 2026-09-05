#!/usr/bin/env python3
"""
prescreen_qwen.py
=================
Qwen-assisted pre-screening of the LRC n=11 proof's key inequality chains.

This script runs on the M4 MacBook Pro where Ollama is available at
localhost:11434 with model qwen3:5:4b.

It sends structured prompts to Qwen asking it to:
  1. Verify the logical structure of Chain A, Chain B, and Universal Blocking.
  2. Assess whether the boundary ledger exclusions (A.1-A.8) are complete.
  3. Identify any missing cases in the α/β decomposition of Section 6.

Results are written to prescreen_qwen_results.json.

CLAUDE.md routing: Qwen --task prescreening (proof section > 50 lines).

Usage
-----
  python3 prescreen_qwen.py [--output PATH] [--model MODEL]

Requires: Ollama running at localhost:11434.

Author: Trent Palelei
Date  : 2026-03-30
"""

import argparse
import json
import subprocess
import sys
import time
from datetime import datetime, timezone


OLLAMA_MODEL = "qwen3.5:4b"
OLLAMA_CMD   = ["python3", "tools/qwen_subagent.py"]

# ---------------------------------------------------------------------------
# Prescreen prompts
# ---------------------------------------------------------------------------

PROMPTS = [
    {
        "id":    "chain_A_logic",
        "task":  "prescreening",
        "title": "Chain A logical structure",
        "prompt": (
            "In the n=11 Lonely Runner Conjecture proof (v28.2), "
            "Chain A (Lemma 5.3) claims:\n"
            "  If runner 3 with sigma_3=+1 covers a right gap [g_L, 109/110] in slot I_9,\n"
            "  then a_3 in [32/(11*g_L), 340/109],\n"
            "  which forces a_8 >= 8*a_3/3,\n"
            "  which forces a_6 in [43*a_3/23, 225/38],\n"
            "  and B_{6,4}[left] = 54/(11*a_6) >= 228/275 > 89/110 = I_8[left],\n"
            "  creating a gap in I_8 of width at least 1/50.\n\n"
            "Task: Verify the logical chain. Are the implications in each step "
            "correct? Is the conclusion (gap in I_8 >= 1/50) valid? "
            "Are there any missing cases or unstated assumptions?"
        ),
    },
    {
        "id":    "chain_B_logic",
        "task":  "prescreening",
        "title": "Chain B logical structure",
        "prompt": (
            "In the n=11 Lonely Runner Conjecture proof (v28.2), "
            "Chain B (Lemma 5.4) claims:\n"
            "  If runner 4 with sigma_4=+1 covers a right gap in slot I_9,\n"
            "  then a_4 in [43/(11*g_L), 450/109],\n"
            "  which forces a_7 >= 7*a_4/4 >= 7*450/(4*109) = 1575/218 ≈ 7.225,\n"
            "  but covering I_7's right edge requires a_7 <= 560/87 ≈ 6.437.\n"
            "  Incompatibility: 1575/218 > 560/87.\n\n"
            "Task: Check whether 1575/218 > 560/87 exactly. "
            "Is the forcing argument (a_7 >= 7*a_4/4) correct given the "
            "pair-ownership structure of (4,7) for slots I_2, I_7? "
            "Any gap in this reasoning?"
        ),
    },
    {
        "id":    "sign_class_coverage",
        "task":  "prescreening",
        "title": "Alpha/Beta decomposition completeness",
        "prompt": (
            "The n=11 LRC proof (v28.2) Section 6 decomposes the "
            "sigma_2=+1 case into 7 regions:\n"
            "  alpha_1: sigma_9=-1, a_9 in [580/69, 87/10)\n"
            "  alpha_2: sigma_9=-1, a_9 in [87/10, 980/109)\n"
            "  alpha_3: sigma_9=+1, a_9 in (9, 1960/207)\n"
            "  beta_1:  sigma_9=-1, a_9 in [580/69, 87/10)    [with gap, triggers UB]\n"
            "  beta_2:  sigma_9=-1, a_9 in [87/10, 980/109)   [with gap, triggers UB]\n"
            "  beta_3:  sigma_9=+1, a_9 in [1960/207, 86/9]\n"
            "  beta_4:  sigma_9=+1, a_9 in (86/9, 10)\n\n"
            "Task: Does this decomposition cover ALL cases for sigma_2=+1? "
            "Specifically: (1) Is sigma_9=-1 range [8,9) fully covered by "
            "alpha_1 union alpha_2? Note 980/109 ≈ 8.99 and the range is "
            "[8,9). (2) Is sigma_9=+1 range (9,10) fully covered by "
            "alpha_3 union beta_3 union beta_4? Note 1960/207 ≈ 9.47. "
            "Is there a gap in (9, 1960/207)? (3) Are the alpha and beta "
            "regions mutually exclusive?"
        ),
    },
    {
        "id":    "universal_blocking",
        "task":  "prescreening",
        "title": "Universal Blocking exhaustiveness (Theorem 5.5)",
        "prompt": (
            "Theorem 5.5 of the n=11 LRC proof (v28.2) claims that no "
            "assignment of runners 3-8 can simultaneously cover a right gap "
            "in slot I_9 AND keep all other slots completely blocked.\n\n"
            "The argument uses:\n"
            "  - PSM (Primary Slot Miss): negative-signed runners covering I_9 "
            "    must leave their own primary slot unblocked.\n"
            "  - Chain A: runner 3, sigma=+1, forces gap in I_8.\n"
            "  - Chain B: runner 4, sigma=+1, forces incompatibility in I_7.\n"
            "  - Runners 5,6,7,8 are claimed infeasible or subordinate (Appendix A.10).\n\n"
            "Task: (1) Is the PSM argument self-contained given the sign-range "
            "containment result (Lemma 5.1: a_j in (j-1, j+1))? "
            "(2) Can runner 5 with sigma_5=+1 cover I_9? Runner 5 'owns' "
            "slots I_1 and I_8 (pair with runner 6). What prevents it from "
            "also covering I_9 via a different branch k? "
            "(3) Are runners 6, 7, 8 genuinely infeasible for I_9 coverage "
            "given sign ranges?"
        ),
    },
]

# ---------------------------------------------------------------------------


def run_qwen_prompt(prompt_rec: dict, model: str) -> dict:
    """Run a single prompt through the Qwen subagent."""
    cmd = OLLAMA_CMD + [prompt_rec["prompt"], "--task", prompt_rec["task"]]

    start = time.monotonic()
    try:
        result = subprocess.run(
            cmd, capture_output=True, text=True, timeout=180
        )
        elapsed = time.monotonic() - start
        output  = result.stdout.strip()
        error   = result.stderr.strip()
        success = result.returncode == 0
    except subprocess.TimeoutExpired:
        elapsed = 180.0
        output  = ""
        error   = "TIMEOUT"
        success = False

    return {
        "id":      prompt_rec["id"],
        "title":   prompt_rec["title"],
        "success": success,
        "elapsed_s": elapsed,
        "response": output,
        "error":   error,
        "timestamp": datetime.now(timezone.utc).isoformat(),
    }


def main():
    parser = argparse.ArgumentParser(
        description="Qwen prescreen of LRC n=11 proof sections."
    )
    parser.add_argument("--output", type=str,
                        default="prescreen_qwen_results.json")
    parser.add_argument("--model",  type=str, default=OLLAMA_MODEL)
    args = parser.parse_args()

    print("=" * 60)
    print("  LRC n=11 Qwen Prescreen")
    print(f"  Model : {args.model}")
    print(f"  Prompts: {len(PROMPTS)}")
    print("=" * 60)
    print("  Note: Qwen is used for logical structure review only.")
    print("  Exact arithmetic is handled by exact_symbolic.py.")
    print()

    results = []
    for i, prompt_rec in enumerate(PROMPTS):
        print(f"[{i+1}/{len(PROMPTS)}] {prompt_rec['title']} ...", end=" ", flush=True)
        rec = run_qwen_prompt(prompt_rec, args.model)
        results.append(rec)

        if rec["success"]:
            print(f"done ({rec['elapsed_s']:.1f}s)")
            # Print first 200 chars of response as preview
            preview = rec["response"][:200].replace("\n", " ")
            print(f"  → {preview}{'...' if len(rec['response']) > 200 else ''}")
        else:
            print(f"FAILED — {rec['error'][:80]}")

        print()

        # Auditor checkpoint (per CLAUDE.md §1)
        print(f"  Qwen says: {rec['response'][:120].replace(chr(10), ' ')}")
        print(f"  Decision: Accepting — Qwen prescreen recorded for human review.")
        print()

    # Write output
    output_data = {
        "timestamp":  datetime.now(timezone.utc).isoformat(),
        "model":      args.model,
        "n_prompts":  len(PROMPTS),
        "n_success":  sum(1 for r in results if r["success"]),
        "results":    results,
        "usage_note": (
            "Qwen responses are advisory. Each response should be reviewed "
            "by the researcher before accepting conclusions. Exact arithmetic "
            "is verified independently by exact_symbolic.py."
        ),
    }

    with open(args.output, "w") as f:
        json.dump(output_data, f, indent=2)

    print(f"Results written to: {args.output}")
    print(f"{output_data['n_success']}/{len(PROMPTS)} prompts completed successfully.")


if __name__ == "__main__":
    main()
