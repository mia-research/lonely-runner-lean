# PRE-REGISTRATION — P0, the anti-coherent plant: what alternative class does the cross-prime decision rule have power against? (v1)

**Date 2026-07-30. Frozen before any statistic in §3 was evaluated.**
**Origin:** `ANALYSIS_destructive_interference_frame_v1.md` §5, probe P0 (user-selected).
**Class:** INSTRUMENT CALIBRATION on synthetic plants. **Not** a leakage test. **Not** a re-analysis
of real data. **No real-data verdict can be produced by this spec** (§7).

---

## 0. The object, named — and the proxy it must not be confused with

**OBJECT:** the **cross-prime decision rule** actually used to declare the twist-orbit nulls:

> `D_min : reject iff min_{i=1..12} p_i < α/12`  (α=0.05 ⇒ threshold **0.004167**)

as applied in `RESULT_twist_orbit_spectrum_v1.md` (reported `min p = 0.029`, "≫ Bonferroni 0.004")
and `RESULT_twist_orbit_magnitude_v1.md` (reported `min p = 0.050 @ 2647`).

**PROXY THAT MUST NOT BE SUBSTITUTED (the §2b failure mode):** the *per-prime* test's power.
The record's existing power statements — *"PLANT-POS fires 4–6×"*, *"PLANT 4.9–10.9×"* — are
measurements of the **per-prime** statistic `T` against the **per-prime** null p95
(`twist_orbit_spectrum_run_v1.py:209`, `twist_orbit_magnitude_run_v1.py:84`). **They say nothing
about `D_min`.** A per-prime plant that fires 5× in one prime and a plant that is invisible in every
prime individually but present in all twelve are different alternatives, and only the first has ever
been calibrated. Reporting per-prime power as if it scoped `D_min` is the proxy error. This spec
measures `D_min` itself.

**Pre-committed claim under test (the thing that could be wrong):** that the twist-orbit nulls'
stated power ("scoped-real, not a power fail") extends to distributed alternatives.

---

## 1. Why this is P0 and not P1

`D_min` is a **max-combiner**. Max-combiners are near-optimal against an alternative concentrated in
one cell and are known to lose power against an alternative spread across all cells. That is a
textbook fact, so the *direction* of the result is not in doubt; **the magnitude is**, and the
magnitude is what determines whether the existing nulls need re-scoping. This probe therefore
produces a **number**, not a discovery, and it cannot produce a false positive about the curve (§7).

---

## 2. Frozen inputs

- **Stratum:** the frozen `stratum_S` in `twist_orbit_spectrum_FREEZE_v2.json` (12 primes,
  `p ≡ 7 mod 12`, `n` prime, `p > 547`). Read, not re-chosen.
- **Pipeline:** `twist_orbit_spectrum_run_v1.py` unmodified — `Vfull`, `class_values`, `rebuild_W`,
  `Tstat`, `permutation_pvalue`. The plant is injected at the **same point** the existing
  `PLANT_POS` uses (the class-value vector `rho`), so the comparison is like-for-like.
- **Seed:** `20260730`. Fixed now. One seed. No seed-shopping (`kfold_gate` guard 1).
- **α:** 0.05. Bonferroni threshold `α/12 = 0.004167`. Both frozen.

## 3. Design

### 3.1 Two-stage, to keep the cost honest

**Stage 1 (empirical, 3 primes — the smallest, middle, largest of `stratum_S`).**
Measure the map `δ ↦ distribution of the per-prime p-value` under an additive plant

> `rho_planted = rho_base + δ · scale · exp(iπ s / L)`,  `s = 0..L-1`,
> `scale = sqrt(mean(|rho|²))` — the same tone and the same empirical scale as the existing
> `PLANT_POS` (`twist_orbit_spectrum_run_v1.py:204-206`), with `δ` replacing the implicit `1`.

`rho_base` = **a permutation draw of the real `rho`** (ground truth: no signal), so the `δ=0` row is
an FPR check with known truth. Per `(prime, δ)`: `n_rep = 200` base draws; per draw the p-value is
computed with the pipeline's own `permutation_pvalue` at `R = 1000` (⇒ resolution `1/1001`, finer
than the 0.004167 threshold). `δ ∈ {0, 0.05, 0.1, 0.2, 0.35, 0.5, 0.75, 1.0}`, frozen.

**Stage 2 (combiner comparison, on p-values only — negligible cost).**
Draw 12 iid p-values from the Stage-1 empirical distribution at amplitude `δ` and evaluate:
- `D_min` (**the rule under test**): reject iff `min p_i < 0.004167`
- `D_fisher`: `−2Σ log p_i` vs `χ²_24`, α=0.05
- `D_stouffer`: `Σ Φ⁻¹(1−p_i)/√12` vs `z_{0.95}`
`n_rep = 20000` combiner replicates per `(δ, arm)`.

### 3.2 Arms (the coherence structure of the plant)

| arm | plant | what it models |
|---|---|---|
| **A1 CONCENTRATED** | amplitude `δ` in **1** prime, 0 in the other 11 | the alternative the existing PLANT calibrates |
| **A2 DISTRIBUTED** | amplitude `δ` in **all 12** primes | a sub-noise signal present family-wide |
| **A3 SIGN-SCRAMBLED** | amplitude `δ` in all 12, tone conjugated (`s → −s`) on a subset selected by `p mod 4`, by `p mod 3`, and (third variant) at random | the D4 mechanism: an unaccounted arithmetic phase |

**A3 is the literal anti-coherent plant.** Note in advance: because `T = |·|²`, `D_min` is *invariant*
to a global conjugation per prime, so **A3 and A2 must give identical `D_min` power**. That is a
**pre-committed instrument check, not a finding** — if the run reports them different, the harness is
wrong. A3's information content is against `D_stouffer` (a signed combiner), where a scrambled sign
*must* destroy power and an aligned one must not.

### 3.3 Exchangeability assumption, stated and checked
Stage 2 assumes the `δ ↦ p` map is common across the 12 primes; Stage 1 measures it at 3.
**Check C-EXCH:** the three primes' `δ*` (§4) must agree within ±25%. If they do not, Stage 2 is
reported as **not licensed** and the spec is amended — not patched post hoc.

---

## 4. Pre-committed primary readout

**`δ*(rule, arm)` = the smallest frozen `δ` at which detection rate ≥ 0.80.**

**HEADLINE NUMBER:** `Ratio = δ*(D_min, A2) / δ*(D_fisher, A2)`.

Pre-committed interpretation, fixed now:
- **`Ratio ≤ 1.3`** ⇒ the max-combiner is not materially lossy here. The twist-orbit nulls' scope
  **extends** to distributed alternatives, and the interference worry is **bounded, with a number**.
  This *strengthens* the existing nulls. `[the outcome that closes P1]`
- **`Ratio ≥ 2.0`** ⇒ `D_min` is materially blind to distributed alternatives. Every twist-orbit null
  is then scoped to **concentrated** alternatives only, this scope must be written into the RESULT
  files, and **P1 (coherent re-pool) is promoted from optional to owed.**
- **`1.3 < Ratio < 2.0`** ⇒ report the number, no scope change, no promotion. **Pre-committed
  abstention** — and per `feedback_prereg_abstention_is_the_finding_2026_07_19`, abstaining here
  closes nothing and licenses no follow-up statistic on this frozen run.

## 5. Controls that must fire (run aborts if any fails)

- **C-FPR:** at `δ=0`, detection rate of `D_min` ∈ [0.02, 0.09] and of `D_fisher` ∈ [0.03, 0.07].
  A miscalibrated null invalidates every row.
- **C-A1:** `δ*(D_min, A1) < δ*(D_fisher, A1)` — the max-combiner must **win** on the concentrated
  arm. If it does not, the harness is wrong, not the literature.
- **C-CONJ:** `δ*(D_min, A3) == δ*(D_min, A2)` exactly (§3.2). Harness check.
- **C-REBUILD:** the pipeline's own `rebuild_err` and `C_ODD`/`C_PARSEVAL` checks pass on every
  prime used, unmodified.
- **C-MONO:** detection rate is non-decreasing in `δ` for every (rule, arm). Non-monotonicity is the
  `T_dev` failure (`AUDIT_prereg_incomplete_shortscalar_SELFAUDIT_v1.md`) and voids the readout.

## 6. Falsification / what would make this probe wrong

- C-FPR out of band, or C-A1 reversed ⇒ the harness is defective; **no number is reported.**
- C-EXCH fails ⇒ Stage 2 unlicensed; Stage 1 reported alone as three per-prime curves.
- If `δ*` is not reached at `δ = 1.0` for a (rule, arm) cell, that cell is reported as
  **`δ* > 1.0`** — never extrapolated.

## 7. Scope — what this run can and cannot say

**CAN:** state the alternative class `D_min` has power against, as a number, and thereby scope the
existing twist-orbit nulls.
**CANNOT:** say anything about whether the curve has structure. No real-data statistic is
re-evaluated; the real `rho` enters only as a *permuted* base (no signal by construction) and as the
empirical scale. **A positive finding about secp256k1 is not among this spec's possible outputs.**
This is the whole reason P0 is first: the false-positive budget the user allowed is **not** spent here.

## 8. Deviations
Any departure from §2–§5 is logged in `PREREG_anticoherent_plant_powerscope_v1_DEVIATIONS.md`
before the affected number is reported.
