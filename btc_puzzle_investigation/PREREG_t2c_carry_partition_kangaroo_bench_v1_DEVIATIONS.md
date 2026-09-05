# DEVIATIONS — PREREG_t2c_carry_partition_kangaroo_bench_v1.md

Freeze protocol: post-freeze changes disclosed here. OBJECT, the two-arm+oracle design, the single-bit
ceiling, the anti-circularity ruling, the firing-control logic, and the pre-commitment table are
UNCHANGED. One instrument change (D1) and one scale change (D2).

## D1 — [instrument] solver = BSGS, not a stochastic kangaroo

**Frozen (§1–§5).** The interval-DLP solver is a two-herd distinguished-point interval **kangaroo**
(`interval_dlp_bench`-style), with §5 power built around kangaroo op-count CV ≈ 0.5–0.7.

**Deviation (D1).** The runner uses **BSGS** (baby-step-giant-step) confined to an interval/run, counting
EC point-additions, as the interval-DLP solver for all three arms (BASELINE / VARIANT / ORACLE).
Rationale — this is a strict improvement for *this* benchmark, not a shortcut:
- BSGS op-count for a width-`w` interval is **deterministic** `≈ 2⌈√w⌉` (no jump-tuning, no variance, no
  solve-failure/censoring). So the ratio `R_k = variant_ops / baseline_ops` isolates the partition's
  interval-restriction effect **exactly**, removing the §3 tuning-confound and the §5 CV-noise the
  kangaroo spec spent effort controlling.
- The firing control (§4) becomes **exact**: ORACLE confined to the run containing `d` costs `2√w_run`,
  ratio `√(w_run/|I|)` deterministically — no noise floor needed to see it fire.
- The physics the verdict rests on — op-count ∝ `√(searched width)`, and `Σ_runs √w_run ≥ √(Σ w_run)`
  (concavity) making a fragmented-class search COST MORE than one interval — is **identical** for BSGS
  and kangaroo. So the exponent-vs-constant verdict (§2 shape 1/2/3) is instrument-independent.
- The single-bit ceiling (§0) and the anti-circularity ruling (§2R) are unchanged (the VARIANT still
  consumes only the public partition, never `ε(d_target)`).

Consequence: §5's `T=1000`-for-CV-noise is relaxed to `T≈200` `d`-draws (BASELINE and ORACLE op-counts
are deterministic per `d`; the VARIANT's per-`d` op-count is deterministic given the fixed
class/run search order — the only per-`d` variation is *which* run holds `d`, so a few hundred draws
resolve the median exactly). All other §6 schedule elements (curve selection rule, k-selection rule,
frozen seeds) stand.

## D2 — [scale] model-curve size band lowered for tractability

**Frozen (§6).** `n` in bands ~2³⁰, 2³⁵, 2⁴⁰.

**Deviation (D2).** First pass uses smaller j=0 prime-order model curves (`n` ~ 2¹⁸–2²⁶) so that
`select_j0_prime_order` (which computes order by an `O(q)` point count) and the per-`d` BSGS (`O(√w)`)
are both fast, while the GLV lattice basis (~`√n`) is still large enough that the genuinely-2-D carry
skew is non-trivial for `k` in the mid-range (skew needs the 2-D regime `k ≳ ½log₂n`, present here).
Zero secp power either way; a larger-`n` pass is an untested refinement (§9 unprojected clause), not a
scope claim. The k-selection RULE (`k_strong=argmax|P_k−½|`, etc.) is unchanged and applied to each
curve's own exact `P_k`.

Recorded 2026-08-26, before any trial.

## D3 — [self-audit] v1 stacked the deck two ways; v2 (`t2c_carry_composition_bench_v2.py`) fixes both

A user-prompted adversarial self-review of the v1 runner (`t2c_carry_partition_kangaroo_bench_v1.py`)
found the v1 result was a REAL null but **stacked toward a more dramatic/mis-scoped null** than honest:

**Stack 1 — inflated magnitude (the negative-bias failure mode, my own).** v1's VARIANT did a full
scalar-mult `[lo_r]G` setup **per run** (per-run BSGS), so at fragmented k (100s of runs) the reported
op-count was dominated by per-run setup, not search — producing a fake "14–21× liability." The honest
variant is ONE BSGS over `I` with the giant steps REORDERED by the public carry prior; for a UNIFORM `d`
reordering cannot change the expected steps-to-find. **v2 measures R1D ≈ 1.0** (0.92–1.06 across two
curves, all k) — simple no-help, no liability. The 21× was an artifact.

**Stack 2 — wrong object (scope substitution).** v1 tested carry-partition on the **1-D interval** DLP
and cited `RESULT_curve_island_lambda_folding` (2⁵⁸× worse) for the endomorphism half by proxy — it never
built the actual **2-D GLV composition** (`P=[a]G+[b]φ(G)` with the carry `ε` as a constraint on the
contiguous `(a,b)` sign-region, where — unlike the 1-D interval — it does NOT fragment). **v2 builds and
directly measures it:** the 2-D meet-in-the-middle op-count vs the 1-D interval baseline, instrument-
consistent (both counted as baby-steps + giant-steps-to-find). Result: **2D/1D ≥ ~1, up to ~20×** —
the 2-D composition is *worse* than the plain interval for interval keys (box ~`n` ≫ interval `2^k`),
reaching parity only at `k→log₂n`; the carry ORACLE gives no benefit over the full 2-D (2Dor ≈ 2Dfull).

**Metric fix (avoiding a re-stack).** v2 counts the STANDARD BSGS group-op cost — (baby steps) + (giant
steps examined until solution), 1 unit each — identically for the 1-D and 2-D solvers, so no per-cell-mul
vs incremental-add mismatch tilts the ratio (an early v2 draft had 2-D looking artificially cheap from
exactly that mismatch; caught and removed).

**Net:** the verdict (no computational advantage) is unchanged and theorem-backed (one carry bit ⇒
constant factor; interval bound ⇒ 2-D worse than 1-D), but it now rests on **fair, measured** numbers on
the **actual composition object**, not a stacked strawman. The canonical result is
`RESULT_t2c_carry_partition_kangaroo_bench_v1.md` (v2 numbers). Recorded 2026-08-26, post-run.
