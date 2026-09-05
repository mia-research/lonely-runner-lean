# PREREG v5 — Semaev CM Lever: Cost-Side, Mechanism, Extrapolation ("what can the lever do")

**File:** `PREREG_semaev_cm_lever_capability_v5.md`  **Date:** 2026-08-15
**Depends on:** `RESULT_semaev_cm_relation_yield_v4.md` (A1 — H1 fires at all 5 |V|-levels, Scaling GROWS).
**Status: PRE-RUN.** No confirmatory statistic computed. **Gate: experiment-designer pass OWED before run.**

---

## §0 SCOPE BANNER (governs every number)

Enumerable model curves `E : y²=x³+Ax+B` over small `F_p` (`p ≡ 1 mod 3`).
`p = 2²⁵⁶−2³²−977` is **not** enumerable; **nothing here transfers.**
No secp break; no ECDLP/extraction/security claim. The object is **CM (μ₄,μ₆) vs non-CM (μ₂)**.
The v4 lever characterization (`exp(T1) ≈ 0.35·|V|^{0.9}` at model scale) is a **model-scale
reading only**; no extrapolation beyond the tested range is claimed by any verdict below.

---

## §1 OBJECT (reuses the FROZEN instrument `semaev_elimination_v1.py`, unchanged)

Same instrument as v3/v4. Three arms, each with its own run script; the instrument file is
byte-identical to the v3/v4 runs (verified by SHA before the run).

**Arm A (cost side).** Per cell, in addition to `quo`, log the instrument's already-computed
degree diagnostics:
- `d_ff` — first degree D with a genuine degree fall (`fall > 0` in `macaulay_stats`);
- `d_solv` — minimal truncation D at which `quo(D)` equals the stable final quotient
  (the linear-algebra solving degree as observed by the truncated-Macaulay route);
- `d_gb` — degree of the reduced Gröbner basis.
These require **zero instrument changes** (already returned by `measure_system`; v3/v4 computed
but did not log them).

**Arm B (mechanism).** Exact surface counts + normalization:
- `N_T = #{(x1,x2,x3) ∈ F_p³ : S₄(x1,x2,x3,x_T) = 0}` computed **exactly** by vectorized
  brute force (int64 modular arithmetic, exact for p < 2³¹) at Arm-B's own small-p schedule;
- normalized excess `E = quo·p³ / (|V|³·N_T)` per cell;
- symbolic verification of candidate structure (B-S1/B-S2 below) in Sage over `QQ(ω)` — exact.

**Arm C (extrapolation).** Extend the T1(|V|) curve to |V|=9 (and conditionally |V|=10) at
reduced K on a frozen prime sub-schedule.

---

## §2 FORCED / ANCHOR FACTS — from v4, ZERO new evidence

- **A1** — `#E` drives `quo` as `≈1+(|V|^m/m!)/#E`. Controlled by matching (§3).
- **A2** — automorphism order κ acts on TARGET ORBIT / factor-base SIZE, NOT on single-target
  `quo` on a random base (classical route). H2's x-closure effect is separate and bounded (v4: A6).
- **A3** — `deg(Sx)` curve-independent [PROVED].
- **A4 (from v4 RESULT)** — H1 fires at all |V| ∈ {4..8}; Scaling GROWS with log shape:
  `T1(j0) ≈ 0.90·ln|V| − 1.04`. Read as `exp(T1) ≈ 0.35·|V|^{0.9}` **at model scale**.
  This power-law reading cannot persist (quo bounded by ≈ `|V|³·N_T/p³`); where it bends is
  the Arm-C question.
- **A5 (instrument semantics)** — `d_ff`, `d_solv`, `d_gb` are exact integer degree diagnostics
  computed inside `measure_system` via the degree-sweep `macaulay_stats`; `d_solv` is the
  minimal D with `quo(D)` = stable quotient.
- **A6 (from POSITIVE_FINDINGS_MASTER Part VIII, M9)** — solving degree and first-fall degree
  are **curve-blind** `[VERIFIED, p≤307, m≤4, |V|=3]` on *identical* V/target systems across
  secp / non-CM / j=1728. Arm A therefore tests a **scope extension of a verified fact**, in a
  regime M9 did not cover: per-curve systems (each curve's own decomposable targets),
  `|V|∈{4,5,6}`, `p∈[523,823]`. M9 predicts A-H1 null (A1c). A firing (A1a/A1b) would
  contradict a verified fact at its tested scale and be reported as such — a major finding,
  not a silent contradiction.

---

## §3 HYPOTHESES & STATISTICS (frozen; directions pre-committed where benchmarked)

| id | hypothesis / statistic (verdict-bearing) | null |
|---|---|---|
| **A-H1 (PRIMARY — cost)** | Paired `Δd = d_solv(CM) − d_solv(nonCM matched)` per prime, per \|V\| ∈ {4,5,6}, per CM level. Mean paired difference, **two-sided** (direction unbenchmarked). Fires if p < 0.01. | within-pair sign flip, 2×10⁴ draws, integer-rank p |
| **A-H2 (secondary)** | Same for `d_ff` and `d_gb`. Two-sided. Reported per \|V\|. | same |
| **A-H3 (secondary — economics)** | Per cell: `Σquo` (total decompositions found over K targets) and `elapsed`. Paired log-ratio `log[(Σquo/elapsed)_CM / (Σquo/elapsed)_nonCM]`. One-sided (CM higher — benchmarked by v4 yield). | within-pair sign flip |
| **B-S1 (symbolic — no measurement)** | Verify or refute: for A=0, `S₃(ωx1,ωx2,ωx3) = ω·S₃(x1,x2,x3)` with ω a formal cube root of unity. Exact computation in `QQ(ω)`. Output PROVED / REFUTED. | n/a |
| **B-S2 (symbolic — no measurement)** | Same for the equivariance exponent k of `S₄`: `S₄(ωx1,..,ωx4) = ω^k·S₄(x1..x4)`. PROVED / REFUTED + k. | n/a |
| **B-H1 (PRIMARY, Arm B)** | At Arm-B primes (\|V\| ∈ {4,5,6}): paired `T1_excess = mean(log E_CM − log E_nonCM)`, `E = quo·p³/(\|V\|³·N_T)`. Two-sided. Fires if p < 0.01. | within-pair sign flip |
| **B-H2 (interpretive split, pre-committed)** | If `T1_excess` ≈ `T1` (CIs overlap; same sign) → mechanism is **distributional** (surface's F_p-points cluster on the sampled torus; character-sum class). If `T1_excess` ≈ 0 while T1 > 0 → **count-driven** (residual #E or surface-count effect) — this would weaken the #E-independence reading and trigger investigation. | n/a (routing rule) |
| **C-H1 (PRIMARY, Arm C)** | H1 (yield) at \|V\|=9 (and \|V\|=10 if run): same one-sided sign-flip as v4. | as v4 |
| **C-Scaling (PRIMARY, Arm C)** | T1(\|V\|) on pooled points {4..8 (n=24), 9 (n=16), 10 (n=12, conditional)}. Model set **frozen here**: `M_flat`, `M_linear` (a·\|V\|+b), `M_log` (a·ln\|V\|+b), **`M_log2`: a·ln\|V\| + b·(ln\|V\|)² + c** (curvature/saturation test; 3 params). Weighted LS, **dual weighting pre-committed**: primary = weights ∝ per-level n; sensitivity = weights ∝ 1/Var(T1) per level (per-level variance logged). Both fits reported. **Calibration rule FIXED PROSPECTIVELY (D4 lesson from v4):** primary verdict = raw AICc (Δ≥6 thresholds below); bootstrap stability (10⁴ per-prime resamples) is reported alongside, and **if bootstrap support for the winning verdict is < 50% (growth decisive in <50% of resamples), the verdict is issued WITH a `[LOW-BOOTSTRAP-SUPPORT]` flag rather than silently**. Verdicts: **GROWS-LOG** (M_log best by Δ≥6 over flat AND M_log2 not better than M_log by Δ≥4); **GROWS-CURVED** (M_log2 beats M_log by Δ≥4 with b<0 — concave, saturation onset); **GROWS-LINEAR** (M_linear best by Δ≥6 over flat); **FLAT** / **INCONCLUSIVE** as v4. | residual bootstrap as v4 (10⁴ draws, per-level per-prime resampling) |
| **C-stop (frozen stopping rule)** | The \|V\|=10 arm runs **iff** `T1(9) − T1(8) ≥ 0.05` (log-rate continues or close). Otherwise Arm C stops at \|V\|=9. | n/a |

**Verdicts (conjunctions; no post-hoc subset).**

| # | Condition | Conclusion |
|---|---|---|
| **A1a** | A-H1 fires with mean Δd < 0 (CM **lower** solving degree) | **Cost lever confirmed** — yield and algebra-cost levers compound. Report mean degree shift and the implied matrix-size ratio. |
| **A1b** | A-H1 fires with mean Δd > 0 (CM **higher**) | **Cost anti-lever** — yield gain partially offset by algebra cost. Report the net economics (A-H3 arbitrates). |
| **A1c** | A-H1 null | Yield lever does not touch solving degree at tested scale (levers independent). |
| **A2** | A-H3 fires (CM higher relations/second) | Net campaign economics favor CM. Report ratio. |
| **B1** | B-H1 fires ∧ T1_excess ≈ T1 | **Distributional mechanism** — clustering of the decomposition surface's F_p-points on the sampled torus (character-sum class). Anchored by B-S1/B-S2 if PROVED. |
| **B2** | T1 > 0 ∧ T1_excess ≈ 0 | **Count-driven** — challenges #E-independence reading; investigation owed. |
| **C1** | C-H1 fires ∧ C-Scaling GROWS-LOG | Power-law reading extends to \|V\|=9(,10) without curvature. |
| **C2** | C-H1 fires ∧ GROWS-CURVED | **Saturation onset detected** — report the curvature sign and fitted bend scale. This is the extrapolation boundary. |
| **C3** | C-H1 fires ∧ INCONCLUSIVE | Range extension without shape resolution. |
| **D** | any control fails | that arm uninformative; no verdict. |

**Catch-all:** outcomes not matching (e.g., B-S1 REFUTED with B1 firing; C-stop triggering with
GROWS-CURVED) are reported with full statistics, no named verdict, future prereg owed.

---

## §4 CONTROLS (all must fire/hold; no verdict if any fails)

- **C1 — firing plant** (same as v4): planted decomposable system, quo >> baseline.
- **C2 — #E-match adequacy:** median relative gap ≤ 2/√p per arm per |V|.
- **C3 — |V| equality** across classes (code assert).
- **C4 — nonCM vs nonCM null** (same single-adjacent-pair implementation as v4; two-sided sign-flip).
- **C5 — group-law construction:** every decomposable target has quo ≥ 1 (dim 0).
- **C6 (Arm A)** — v4 consistency: `|T1_A(|V|) − T1_v4(|V|)| ≤ 2σ` at |V| ∈ {4,5,6}
  (σ = per-prime SD/√24; K=15 uses the first 15 targets of the same frozen stream —
  subset, not exact reproduction, hence the 2σ band).
- **C7 (Arm B, NEW) — N_T cross-validation:** at ≥2 Arm-B primes, recompute N_T by an
  independent method (group-count identity `N_T = (#E² + corrections)/2` with corrections
  enumerated exactly, OR a second brute-force implementation with different loop order).
  Must agree exactly (integer equality).
- **C8 (Arm A/C, NEW) — d_solv sanity:** `0 < d_solv ≤ Dmax` for all cells; report the
  d_solv distribution (distinct values, tie structure) before testing.

---

## §5 EXACTNESS

- **Exact int / GF(p):** all curve arithmetic, `quo`, `N_T` (int64 modular arithmetic,
  exact for p < 2³¹ — documented), `d_ff`/`d_solv`/`d_gb`, permutation counts.
- **Sanctioned analytic-only float:** `log E`, `T1_excess`, model-fit coefficients, AICc —
  enter only as monotone statistics ranked against permutation/bootstrap nulls.
- **Symbolic:** B-S1/B-S2 over `QQ(ω)` in Sage — exact ring arithmetic, no floats.

---

## §6 SCOPE & SCHEDULE (frozen pre-run, SHA-256'd before first quo)

- **Arm A:** the v4 24-prime schedule (p ≡ 1 mod 3, [523,823], seed=1000+p curve construction),
  |V| ∈ {4,5,6}, **K=15** (first 15 of the frozen target stream), j0 + j1728 + 5 nonCM.
  Logging: per cell `quo`-vector, `d_ff`, `d_solv`, `d_gb`, elapsed, Σquo.
- **Arm B:** **12 primes p ≡ 1 mod 3, p ∈ [211, 401]** (deterministic: first 12 from 200),
  |V| ∈ {4,5,6}, **K=10**, same class construction (fresh schedule, own SHA).
  Per (curve, target): `quo` (instrument) and `N_T` (brute force, vectorized, exact).
- **Arm C:** |V|=9, **K=10**, **first 16 primes** of the v4 frozen 24-prime schedule (frozen
  order — first 16, no selection). Conditional |V|=10: **K=8, first 12 primes** (same rule),
  runs iff C-stop condition met.
- **Cost estimates** (from v4 observed per-target times, ~2.5×/|V|-step):
  Arm A ≈ 2.6 h; Arm B cells ≈ 25 min + N_T brute force ≈ 40 min (p ≤ 401: p³ ≤ 6.5×10⁷
  per target, vectorized); Arm C night-1 (|V|=9) ≈ 11 h; conditional |V|=10 ≈ 17 h.
- `_SCHEDULE_v5_A.json`, `_SCHEDULE_v5_B.json` — SHA-256'd before the first quo of each arm.

---

## §7 POWER (pinned as numbers)

- **A-H1:** d_solv is integer-valued with few distinct values; 24 pairs × 3 |V|-levels × 2 CM
  levels = 144 paired comparisons (pooled per level: 24). Detects a median degree shift of
  ≥ 1 on ≥ 70% of pairs at p < 0.01. Ties are informative (no shift), not dropped.
- **A-H3:** detects relations/second ratio ≥ 1.15× at power ≈ 0.8 (24 pairs, anticipated
  log-ratio SD ≈ 0.3 — from v4 cell-time scatter).
- **B-H1:** 12 pairs per |V|. Detects |T1_excess| ≥ 0.15 at power ≈ 0.7 (anticipated SD ≈ 0.15
  after normalization — uncertain, reported with the achieved power).
- **C:** level-mean SE at |V|=9 ≈ 0.14 (n=16, K=10, per-prime SD ≈ 0.5). The increment test
  T1(9)−T1(8) vs the log-fit prediction (+0.12) is **directional, not sharp** — pre-registered
  as such. The AICc curvature test on 6–7 heteroscedastic points will most likely resolve
  GROWS-LOG vs GROWS-CURVED only if curvature is strong (|b·(ln|V|)²| contribution ≥ 0.1
  across the range); otherwise INCONCLUSIVE-shape is an expected honest outcome.

---

## §8 PRE-COMMITTED OUTCOME TABLE

No dismissal vocabulary; every row a positive result.

| # | Outcome | Reported as |
|---|---|---|
| **A1a/A1b/A1c** | cost-lever confirmed / anti-lever / independent | Characterization of the cost side. A1a: compounding levers. A1b: net-economics arbitration via A-H3. A1c: levers orthogonal at tested scale. |
| **A2** | economics | Campaign-level speedup factor (model scale). |
| **B1/B2** | distributional / count-driven | Mechanism localization. B1 names the character-sum clustering class (with B-S1/B-S2 anchor if PROVED). B2 triggers a #E-independence investigation. |
| **B-S1/B-S2** | PROVED / REFUTED | Symbolic lemma or refutation, recorded either way. |
| **C1/C2/C3** | GROWS-LOG / GROWS-CURVED / INCONCLUSIVE | Extrapolation boundary characterization. C2 reports the fitted bend scale. |
| **D** | control failure | uninformative; no verdict. |

**Unprojected-covariate clause.** Any null must NOT be read "no structure": report per-level
statistics, the degree-diagnostic distributions, the N_T values, and untested extensions
(m=4, larger p, other CM orders, Gröbner-ordering dependence of d_solv) as next candidates.

**Output type:** characterization of lever capability at model scale with power + §0 scope.
Never ECDLP/extraction/security.

---

## §9 CHANGE LOG v4→v5

1. **Three arms added** (cost-side, mechanism, extrapolation) — v4 characterized the yield
   lever; v5 tests what it does and why.
2. **Degree diagnostics (`d_ff`, `d_solv`, `d_gb`) promoted to verdict-bearing** (A-H1) —
   previously computed but unlogged.
3. **N_T normalization introduced** (Arm B) with exact brute-force counts + C7 cross-validation.
4. **Symbolic arm added** (B-S1/B-S2) — candidate μ₃ quasi-homogeneity, exact.
5. **M_log2 curvature model pre-committed** (Arm C) — added BEFORE seeing |V|>8 data.
6. **C-stop conditional rule frozen** (|V|=10 arm iff T1(9)−T1(8) ≥ 0.05).
7. **Arm B gets its own small-p schedule** (brute-force N_T affordability), fresh SHA.
8. **D4/D5 lessons applied prospectively:** Arm C's calibration rule (raw AICc primary,
   bootstrap as flagged stability report) and dual weighting (n and 1/Var) are frozen
   BEFORE any |V|>8 data exist. Arm C also logs per-prime values so 1/Var weights are
   computable post-hoc without rerunning.
9. **A6 forced fact added (M9 curve-blindness)** — Arm A reframed as a scope extension of
   MASTER Part VIII M9 to per-curve systems at larger |V|/p; expected outcome per M9: null.

---

## §10 DEVIATIONS

- **D6 — C4 omitted at registration, added during gate.** C4 (nonCM-vs-nonCM null) was declared in §4 but had no implementation in either script and no deviation entry in this section (“D2 disclosure carried” was a dangling reference from v4). Gate audit (2026-08-21) caught this as BLOCKING. Fixed by porting the v4 single-adjacent-pair code into the Arm A script before any full run. §4 C4 line updated to remove the dangling reference.

## §11 Files this run will produce

- `semaev_cm_lever_capability_v5.py` (Arm A; `--armC9`, `--armC10` flags for Arm C)
- `semaev_mechanism_nt_v5.py` (Arm B)
- `semaev_symbolic_quasi_v5.py` (B-S1/B-S2, seconds)
- `_SCHEDULE_v5_A.json`, `_SCHEDULE_v5_B.json` (+ SHA-256 files)
- `semaev_cm_lever_capability_v5.log`, `semaev_mechanism_nt_v5.log`
- `RESULT_semaev_cm_lever_capability_v5.md`
