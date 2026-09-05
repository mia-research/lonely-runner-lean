# RESULT — R1 CM relation-yield, WIDE-RANGE confirmation: the j0 effect PERSISTS across the decade; j1728 + H2 were low-p artifacts

**Grade: `[EMPIRICAL — §8 A1 (candidate) for j0, CONFIRMED across p∈[523,8011]; pre-registered v3,
experiment-designer gate-CLEARED; matched-#E null; firing controls live; m=3; |V|∈{4,5}]`.**
No ECDLP/extraction/security claim (§0 banner governs). This is the wider-range rerun of
`RESULT_semaev_cm_relation_yield_v3.md` — same frozen spec, deviation **D1 fixed** (primes now
log-spaced across [500,8000] instead of the first-24 cluster [523,823]).

**Spec:** `PREREG_semaev_cm_relation_yield_v3.md` (gate cleared). **Instrument:**
`semaev_cm_relation_yield_v3.py --wide` (reuses frozen `semaev_elimination_v1.py`). **Schedule SHA-256
(frozen before first quo):** `53d05e4b84f10c1ff82bceaaf120ea84a45154ef1c809bc57a518b2a9e3beb8f`.
**Log:** `semaev_cm_relation_yield_v3_wide.log`. **Primes:** 24 log-spaced, [523 … 8011]. **Date:** 2026-08-07.

---

## 1. The confirmation test — narrow vs wide (the decisive comparison)

| arm | narrow [523,823] V=4 / V=5 | **WIDE [523,8011] V=4 / V=5** | outcome |
|---|---|---|---|
| **T1(j0)** matched-#E | +0.207 / +0.409, p=0.0000 (21,22/24) | **+0.187 / +0.338, p=0.0000 (22,22/24)** | **PERSISTS** |
| **T1(j1728)** | +0.135 / +0.228, p=0.0037/0.0021 | **+0.014 / +0.029, p=0.167 / 0.111** | **FADES → NULL** |
| **R2 (H2, x-closure)** | +0.658 / +0.617, p=0.0000/0.0004 | **+0.253 / +0.263, p=0.0081 / 0.0325** | **WEAKENS; V=5 sub-α** |
| **Scaling(j0)** ΔT1(V4→V5) | +0.202 | **+0.151** (≥0.10 threshold) | **still GROWS** |
| **C4** nonCM vs nonCM (control) | ≈0, p=0.30/0.22 | **≈0, p=0.862 / 0.927** | behaves |
| C2 #E-match median rel-gap | 0.013 (cap 0.077) | **0.011 (cap 0.043)** | PASS |
| C1 plant | quo=18 (fires) | quo=18 (fires) | PASS |

`T1(j0)` holds at the top of the range (per-prime V=5): p=2437 → 0.93, p=4423 → 0.82, p=8011 → 0.85 —
not a low-`p` edge effect.

## 2. §8 verdict, read off the table

- **j0 → A1 (CANDIDATE), CONFIRMED across the decade.** H1 fires (T1 = 0.187, 0.338; `perm_p = 0`;
  22/24 positive at both `|V|`; ≥ the 0.092 floor) **AND Scaling grows** (+0.151 ≥ 0.10). The narrow-range
  candidate survived the exact test built to kill it. Magnitude at |V|=5: `exp(0.338) ≈ 1.40×` more
  decompositions per target than the #E-matched non-CM curve.
- **j1728 → NULL (backed).** In the wide run T1(j1728) = 0.014 / 0.029, `perm_p = 0.167 / 0.111`,
  **below the 0.092 floor** at power (48 pairs, C4 in-band). The narrow-run firing did **not** survive the
  wider `#E` range → it was a low-`p` artifact. *(Scoped null, run-backed — see the ledger, §5.)*
- **H2 (x-closure) → WEAKENED, borderline.** R2 dropped from ~1.9× (log 0.66) to ~1.29× (log 0.25);
  fires at V=4 (`p=0.008`) but not V=5 (`p=0.033 > 0.01`), 7/24 positive (was 18/24). The narrow-run
  magnitude was inflated by low `p`; the x-closure effect on single-target `quo` is small and range-fragile.
  *(The moving-target argument predicted R2≈1; the wide run leaves a weak, borderline deviation — closer to
  the prediction than the narrow run suggested.)*

**Net:** the surviving, robust, scale-spanning effect is **T1(j0) — the j=0/μ₆ family (secp's own class)
carries more Semaev relation yield per target than a group-order-matched non-CM curve, and it grows with
the factor-base size.** j1728 (μ₄) and the x-closure channel were narrow-range and did not hold.

## 3. What this sharpens vs the prior record

- The 08-05 result (Finding 2) refuted **secp-specificity** on the raw-`quo` statistic at `p=211` alone
  (secp ≈ j1728). The wide, `#E`-matched, 24-prime test is more powerful and **separates j0 from j1728**:
  j0 persists, j1728 does not. This does **not** re-assert a "secp-specific weakness" — it says the robust
  relation-yield structure is on the **μ₆ family** (j=0), of which secp is a member, at model scale.
  Whether j0 is genuinely special or j1728 merely fell below power (its narrow effect was already weaker,
  0.135 vs 0.207) is **not decided** here.

## 4. Scope and what is NOT claimed (honest)

- **Model scale, no transfer.** `p ≤ 8011`. Nothing reaches `2²⁵⁶`. `exp(0.34) ≈ 1.4×` is a **constant
  factor** on decompositions-per-target; overcoming the subexponential index-calculus barrier is **not**
  demonstrated or claimed. `[No ECDLP/secp/security consequence.]`
- **Growth rests on 2 `|V|` points** (4→5); `m=4` (the S₅ axis) was not run. "Grows" is a slope, not a
  trend — the next probe.
- **Mechanism unexplained.** Why the j=0 summation system yields more `F_p`-rational decompositions per
  target on a random base is open (candidate: the j-specific structure of `S₄`; connects to `Σ_t quo`
  curve-dependence, `conservation_check.py`). Owed before any lever reading.
- **The consequential question is untouched:** does more yield-per-target actually **reduce
  relation-collection cost** (fewer targets for a full relation set), or is it offset by the
  curve-dependent total? Not measured.

## 5. CLOSURE LEDGER  *(modeling the DESIGN_suppression_counter_v1 discipline)*
- **"j1728 H1 does not survive the wider range"** | refutation-run: the wide run itself — 48 matched
  pairs, `perm_p = 0.11/0.17`, floor 0.092, C4 control in-band (p≈0.9) → a **powered** null, not an
  assertion. Backed.
- **"H2 x-closure is weak/borderline across the decade"** | refutation-run: wide run, R2 `perm_p =
  0.008 (V4) / 0.033 (V5)`, floor `|log R2|≥0.174` → fires narrowly then drops sub-α; a bounded magnitude
  with its power, not "no effect." Backed.
- **No avenue is closed** — j1728/H2 are scoped model-range nulls; j0 remains an open candidate.

## 6. Next probes (named)
1. **Extend Scaling** — `|V|∈{4,5,6}` and `m=4` (S₅, time-boxed): is the j0 growth a trend or a 2-point
   line? The only route from "constant factor" to a lever.
2. **Mechanism of the j0 yield excess** (own prereg): j-specific `S₄` structure / `F_p`-rational
   decomposition count; is it μ₆-specific or a power artifact vs j1728?
3. **Yield → relation-collection-cost translation** — the consequential test.
4. (lower priority) larger `p` toward `10⁵` if the growth holds — still model scale, but a longer lever arm.
