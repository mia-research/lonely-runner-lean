# WPZ — Opus 4.8 coordination & synthesis  (FINAL STEP)

**Farm to:** Opus 4.8 subagent (`model: opus`). This is the judgment-heavy step —
adjudicating heterogeneous results against the methodology and writing the bounded
verdict — which is why it is the coordinator, not a compute worker.

## Inputs
- `../RESULTS/WP1..WP8*.json`  (WP1 n·Q, WP2 joint classifier, WP3 small-N exact,
  WP4 null n-dist, WP5 GLV, WP6 candidate-sweep distinguishers, WP7 per-family
  battery, WP8 exotic two-stage)
- the WP briefs in this folder (for what each test *claimed* to do)
- `../btc_puzzle_research_plan_v2.md` — the §3 idea→WP coverage map. **Your first
  job: confirm every source idea has an executed test. Any idea with no test, or
  any WP result that argues an idea away instead of running it, is a DEFECT — list
  it for re-run, do not accept the dismissal.** (v1 of the plan dismissed whole
  buckets on priors; v2 exists to prevent that. Hold the results to the same bar.)
- prior records: `../btc_puzzle_findings_v2.md`, and memory topics
  `btc_puzzle_hunt_method`, `btc_puzzle_nk_decomposition`, `btc_puzzle_gect_debunked`.

## Adjudication checklist (apply to EVERY WP result)
1. **Did the positive control fire?** If `positive_control.detected` is false, the
   null is **discarded as underpowered**, not reported as a negative. (v2 §0.2)
2. **Attack-valid vs structure-probe.** Any signal from a WP with
   `attack_valid=false` (WP4, WP5) is a *diagnostic/prior*, never "the public key
   leaks X." Enforce the wording.
3. **Circularity.** Confirm no reported signal rides on a feature that used
   `d,n,k,D` (the F1 / `XY mod n²` trap). Reject if so.
4. **Right null.** Selection claims must be vs the matched-multiset null (WP4),
   not single-scale uniform. Map-property claims vs baseline + planted-control.
5. **Conditional phrasing.** Rewrite any absolute ("impossible", "ruled out") into
   a bounded negative (features + n + floor). (`feedback_conditional_negatives`)

## Deliverable → `../btc_puzzle_findings_v3.md`  (VERSIONED — do not overwrite v2)
Structure it like v2 (§0 methodology stays; do not re-derive it):
- **§1 What moved at 100k power** — the one-line outcome of each WP.
- **§2 Newly bounded (with conditions + control status)** — e.g. the map-property
  ceiling (WP2) at n=100k, the WP1 large-N score verdict, WP3 exact ledger.
- **§3 Surviving signals / leans** — anything ≥2σ that passed all 5 checks:
  most likely the WP4 marginal-n prior and/or WP1 small-N exact separation.
  State each as a *posterior shift on n*, with its ceiling.
- **§4 Highest-value next action** — one recommendation. Candidates: extend WP1
  to larger N with a real DL-distance oracle; the sub-second PRNG-seed vector
  (v2 §3.1, off the 100k substrate); or more real solved keys to power the
  selection tests. Pick one and say why.

Then hand back to the main session a 6–10 line summary: per-WP verdict + the §4
recommendation. Flag any WP whose result file failed an adjudication check so the
main session can re-run it.
