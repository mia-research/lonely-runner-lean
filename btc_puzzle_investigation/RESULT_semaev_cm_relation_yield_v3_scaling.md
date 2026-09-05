# RESULT — R1 CM relation-yield, SCALING extension: T1(j0) grows ~linearly in |V| over {4,5,6} (m=4 infeasible)

**Grade: `[EMPIRICAL — EXPLORATORY extension; |V|=6 is BEYOND the pre-registered Scaling set {4,5}, so it
is characterization, not a new pre-committed verdict. Reuses the frozen v3 instrument + wide schedule
(SHA 53d05e4b…, identical curves). m=3; p∈[523,8011].]`** No ECDLP/extraction/security claim.

Extends `RESULT_semaev_cm_relation_yield_v3_wide.md`. The pre-registered A1 ("H1 fires ∧ Scaling grows",
on |V|∈{4,5}) already held; this adds the 3rd point to test **trend vs 2-point line**, and records the
**m=4 axis as infeasible in this harness**.

**Schedule SHA-256:** `53d05e4b84f10c1ff82bceaaf120ea84a45154ef1c809bc57a518b2a9e3beb8f` (matches the wide
run — same 24 log-spaced primes, same curves; |V|=6 is on the identical objects). **Log:**
`semaev_cm_relation_yield_v3_v6.log`. **Date:** 2026-08-07.

---

## 1. The Scaling curve (T1 = matched-#E log-quo advantage, mean over 24 primes)

| |V| | **T1(j0)** | perm_p | pos | step | T1(j1728) | R2(mu3) |
|---|---|---|---|---|---|---|
| 4 | 0.1874 | 0.0000 | 22/24 | — | 0.0138 (null) | 0.253 |
| 5 | 0.3384 | 0.0000 | 22/24 | +0.151 | 0.0290 (null) | 0.263 |
| **6** | **0.5088** | **0.0000** | **23/24** | **+0.170** | 0.0593 (p=0.045) | 0.219 (p=0.020) |

**T1(j0) is approximately linear in |V|** over {4,5,6}: increments +0.151, +0.170 (slightly
accelerating). It does **not** saturate and is **not** a 2-point artifact. Controls at |V|=6: **C4**
non-CM/non-CM in-band (mean −0.034, p=0.834); **C2** #E-match median gap 0.011 ≪ cap 0.043; **C1** plant
fires (quo=18). T1(j0) holds at the top of the range (|V|=6: p=4423→1.22, p=8011→1.27).

## 2. What the linear trend means — precisely, and fenced

- `T1 = log Q_j0 − log Q_nonCM(matched)`. A **linear** `T1` in `|V|` means the **ratio**
  `Q_j0 / Q_nonCM` grows **~exponentially in `|V|`** over [4,6] — i.e. the CM decomposition-count
  advantage is **NOT a bounded constant** at model scale; it **increases with factor-base size** in the
  tested window. This is the "more-than-constant route" the prereg named as the candidate-lever signature,
  and the 3rd point supports it (was 2-point in the wide run).
- **This is where extrapolation must stop, and does.** `|V|∈{4,5,6}` is *tiny*; a real index-calculus
  factor base is `|V| ~ p^{c}` (thousands+). **A 3-point trend at `|V|=4–6` gives NO license to project to
  large `|V|`** — the linear regime can bend or saturate once `|V|` is no longer ≪ the number of
  small-order structures, and that is **untestable here** (|V|≥7 needs larger `p` for decomposable targets
  and more compute). The trend is a real feature of the tested window, not a demonstrated asymptotic.

## 3. m=4 (the other Scaling axis) — INFEASIBLE in this harness

The pre-registered `m=4` secondary ("where `Dmax` resolves") **does not resolve**: even *building* the S₅
summation polynomial for a single cell exceeded **120 s** (`probe_m4`, p=523), before any solve — so a
24-prime × K run is intractable (consistent with the 08-05 note: S₆ intractable, S₅ heavy). **Recorded as
a scoped infeasibility.** The Scaling conclusion therefore rests on the `|V|` axis **only**; whether the
advantage also grows with `m` (points per relation) is **untested**.

## 4. Scope and what is NOT claimed (unchanged fences)

- **Model scale, no transfer.** `|V| ≤ 6`, `p ≤ 8011`, `m = 3`. Nothing reaches `2²⁵⁶` or a real
  factor-base size. **No ECDLP/secp/security consequence.**
- **The trend is within-window.** "Grows ~linearly / ratio ~exponential in |V|" is a statement about
  `|V|∈[4,6]`, not an asymptotic. Extrapolation to attack-scale `|V|` is explicitly **not** made.
- **j1728 and H2 remain weak/borderline** (j1728 T1=0.059 p=0.045; R2=0.22 p=0.02) — the robust, growing
  effect is **j0/μ₆ only** (secp's family). Not re-asserted as a "secp weakness."
- **The consequential question is still untouched:** does a growing decompositions-per-target advantage
  actually **lower relation-collection cost** (fewer targets for a full relation set), net of the
  curve-dependent total (`conservation_check.py`)? Not measured — and it is the thing that would decide
  "structural curiosity" vs "lever."

## 5. CLOSURE LEDGER (per DESIGN_suppression_counter_v1)
- **"T1(j0) growth is a trend, not a 2-point line / not saturating"** | refutation-run: this |V|=6 run —
  3rd point 0.509, `perm_p=0`, step +0.170 (≈ the +0.151 prior step), controls in-band → the saturation
  hypothesis is refuted **by the added point**, not asserted. Backed.
- **"the trend does NOT license a scale claim"** | this is a *scope fence*, not a closure: the trend is
  real in-window; the asymptotic is untested (|V|≥7 out of reach here). Stated as owed, not as "bounded."
- No avenue closed; j0 is a strengthened open candidate, j1728/H2 remain scoped nulls.

## 6. Next probes (named)
1. **|V|=7, 8** at the largest feasible `p` (needs `p` large enough for |V|-decomposable targets; per-cell
   ~seconds-to-minutes) — does the linear trend continue or bend? The direct asymptotic probe within reach.
2. **Mechanism of the j0 yield excess** (own prereg): why the j=0 `S₄` system has more `F_p`-rational
   decompositions per target on a random base; is it a counting identity? Connects to `Σ_t quo`
   curve-dependence.
3. **Yield → relation-collection-cost** translation — the consequential test (§4).
4. `m=4` only if a lighter S₅ construction (precomputed/streamed resultants) makes it tractable.
