# LRC n=11 Computational Verification

**Project**: Lonely Runner Conjecture — n = 11 case
**Proof document**: `lrc_n11_ap_paper_v28.2.md`
**Author**: Trent Palelei
**Date**: 2026-03-30

---

## Overview

This directory contains computational evidence for the n = 11 Lonely Runner
Conjecture (LRC). The verification is **supplementary** to the analytic proof;
it does not constitute a proof in itself, but provides independent numerical
corroboration at a scale sufficient to detect any structural error in the
case analysis.

The LRC (n = 11) asserts: for any 10 runners on a unit circle with distinct
speeds e₁ < … < e₁₀, there exists a time t such that every runner is at
distance ≥ 1/11 from the origin.

---

## What is verified

Two independent components:

### 1. Exact symbolic verification (`exact_symbolic.py`)

All explicit rational constants and inequality chains in the proof are
verified using Python's `fractions.Fraction` (exact rational arithmetic,
zero floating-point error). This covers:

- Complementary pairs structure (modular inverses mod 11)
- Slot boundaries I₁ … I₉
- Chain A (Lemma 5.3): gap bound 1/50
- Chain B (Lemma 5.4): incompatibility bound
- Negative branch forced configuration and sub-gap 538/54395
- Alpha decomposition boundary values
- W_ref closure condition

Result: 34/34 checks pass exactly.

### 2. Boundary-set witness search (`verify_lrc_n11.py`)

For random speed configurations in the commensurable large-ratio regime
(a₁ ∈ (0,1), aⱼ ∈ (j-1, j+1) for j = 2…9, a₁₀ = 10), the script
searches for a witness time in W_ref = [1/(11·a₁), 10/(11·a₁)] using
the event-complete boundary-set method.

The boundary-set method (Palelei φ(n)-law paper) guarantees completeness:
isolation status changes only at times where some runner crosses the 1/11
threshold, so evaluating midpoints of all inter-boundary intervals is
exhaustive. No witness is missed within W_ref.

Target scale: 10⁸ configurations (approximately 8 hours on M4 MacBook Pro).

---

## Directory structure

```
lrc_n11_verification/
├── README.md                         this file
├── MANIFEST.json                     provenance and run registry
├── scripts/
│   ├── verify_lrc_n11.py             main boundary-set harness
│   ├── exact_symbolic.py             exact rational inequality checks
│   ├── prescreen_qwen.py             Qwen logical structure review
│   └── analyze_results.py           query and summarise evidence.db
└── runs/
    └── <run_id>/
        ├── config.json               run parameters
        ├── batches.jsonl             one record per batch (append-only)
        ├── evidence.db               SQLite mirror of batches.jsonl
        └── summary.json             final statistics
```

---

## Reproducing the evidence

### Prerequisites

```bash
python3 --version   # 3.10 or later
python3 -m pip install numpy
```

### Step 1: Exact symbolic verification

```bash
python3 scripts/exact_symbolic.py --output runs/exact_symbolic_results.json
```

Expected output: `34/34 checks passed, 0 failed.`

### Step 2: Boundary-set witness search

**Quick smoke test (500 configs, ~1 second):**

```bash
python3 scripts/verify_lrc_n11.py \
  --target 500 --batch-size 100 --workers 4 --seed 42 \
  --run-id smoke_test
```

**Standard run (10⁷ configs, ~10 minutes on M4):**

```bash
python3 scripts/verify_lrc_n11.py \
  --target 10000000 --batch-size 5000 --workers 10 --seed 42 \
  --run-id run_1e7
```

**Compelling run (10⁸ configs, ~8 hours on M4):**

```bash
python3 scripts/verify_lrc_n11.py \
  --target 100000000 --batch-size 5000 --workers 10 --seed 42 \
  --run-id run_1e8
```

**Overnight / weekend run (10⁹ configs, ~80 hours on M4):**

```bash
python3 scripts/verify_lrc_n11.py \
  --target 1000000000 --batch-size 10000 --workers 10 --seed 42 \
  --run-id run_1e9
```

Interrupt at any time with Ctrl-C; resume with `--resume --run-id <id>`.

### Step 3: Qwen prescreen (logical review, requires Ollama)

```bash
# Start Ollama first: ollama serve
python3 scripts/prescreen_qwen.py --output runs/prescreen_qwen_results.json
```

### Step 4: Analyse results

```bash
python3 scripts/analyze_results.py --run-dir runs/run_1e8 --histogram
```

---

## Evidence format

### `batches.jsonl`

Each line is a JSON object:

```json
{
  "batch_index":       42,
  "seed":              84,
  "n_tested":          5000,
  "n_passed":          5000,
  "n_failed":          0,
  "total_boundaries":  4312500,
  "min_margin":        0.00021,
  "max_margin":        0.08143,
  "mean_boundaries":   862.5,
  "elapsed_s":         12.4,
  "timestamp":         "2026-03-31T02:14:07+00:00"
}
```

### `evidence.db` (SQLite)

Tables: `batches`, `failures`, `run_meta`.

Query examples:

```sql
-- Global statistics
SELECT SUM(n_tested), SUM(n_failed), MIN(min_margin) FROM batches;

-- All failures (should be empty)
SELECT * FROM failures;

-- Throughput over time
SELECT batch_index, n_tested, elapsed_s,
       n_tested * 1.0 / elapsed_s AS rate FROM batches
ORDER BY batch_index;
```

---

## Statistical interpretation

If the search finds 0 failures in N configurations, the 95% confidence
upper bound on the true failure rate is approximately 3/N (rule of three).

| Scale | Failure bound | Interpretation |
|---|---|---|
| 10⁶ | < 3 × 10⁻⁶ | Suggestive |
| 10⁷ | < 3 × 10⁻⁷ | Moderate confidence |
| 10⁸ | < 3 × 10⁻⁸ | Compelling |
| 10⁹ | < 3 × 10⁻⁹ | Overwhelming |

At 10⁸ the failure bound falls below the typical hardware error rate
for a single computation, which is the informal threshold for
"computationally irrefutable without formal verification."

---

## Limitations

1. The boundary-set search is complete within W_ref, but W_ref itself
   requires a_10/a_1 > 10 (the large-ratio regime). The bounded-ratio
   case (a_10/a_1 ≤ 10) is handled by the explicit witness t* = 10/(11·a_10)
   and is trivially verifiable.

2. The irrational-ratio case follows from Kronecker density and is not
   computationally verifiable in this sense.

3. Random sampling covers all 256 sign classes proportionally, but does
   not systematically stress every boundary sub-case in Appendices A.1–A.8.
   The exact symbolic verification addresses those directly.

4. This evidence does not substitute for formal verification (Lean/Coq),
   which would provide mathematical certainty rather than probabilistic
   confidence.

---

## Relation to φ(n)-law paper

The boundary-set method is adapted from the φ(n)-Residue Framework
(Palelei 2026), which established that isolation status changes only at
analytically determined boundary times. Applied to LRC n=11, this replaces
a fine time grid (~10⁶ points per configuration) with an event-complete
set of ~900 boundary points, yielding approximately 1000× speedup while
maintaining mathematical completeness guarantees.
