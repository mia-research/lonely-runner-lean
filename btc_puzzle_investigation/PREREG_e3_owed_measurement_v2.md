# PREREG v2 (FROZEN) — E3 (A-1d) owed measurement: structural-null reframe + FWER + OOS + curve-class

**Date frozen 2026-08-18.** Supersedes the DRAFT `PREREG_e3_owed_measurement_v1.md` (retained). v2 applies
all four `experiment-designer` HOLD findings (audit recorded verbatim in §7). Integer-exact throughout
(`int`/`gmpy2.powmod`; no float in the signal path). Discharges `ROADMAP_REDIRECT_v3.md` **Brick A** /
`POSITIVE_FINDINGS_MASTER_v12.md` **§E.3**. No security/keyspace/extractability claim is made or reachable.

---

## 0. Object under test (fixed; reproduced exactly 2026-08-18, not assumed)

**E3 = field-difference cubic-character energy** of the real 82 solved-puzzle pubkey x-coords on secp256k1.
For each unordered pair `i<j` of the 82 x-coords: `z=(x_i−x_j) mod P`; cube class `c=χ₃(z)∈{0,1,2}` via
`z^((P−1)/3) mod P ∈ {1,β,β²}`; QR bit `q∈{0,1}` via `z^((P−1)/2)`; 6-cell histogram `H[3q+c]`.
**Family via `stats3`** (reused verbatim from `c2_grouplaw_diffset_curve_v1.py`, integer-only):
`E2=(n_q0−n_q1)²`, `E3=A3²−A3·B3+B3²` (`A3=n_c0−n_c2,B3=n_c1−n_c2`; ≡ `a²+b²+c²−ab−bc−ca`), `E6` (sextic).

**Reproduced (integrity gate, must re-assert at run):** `E3(real,secp)=13125`, `(a,b,c)=(1082,1057,1182)`,
`a+b+c=3321`, `E3≡0 mod 3`. **Real family:** `E2=1225, E3=13125, E6=847` (confirmed
`e3_repro_prep_v1.py`). E3 = ¼|1ᵀC1|², the all-ones/marginal projection (`RESULT_spectral_decomp_v1.md`).

## 0.5 Frame (in-bounds by null-replacement, not narrowing)

Prior E3 nulls were the known-MT19937 pool → the estimand was "do the real integers differ from a known
generator?" = a **generator** test, out of bounds (`CORRECTION_e3_cmvanishing_interaction_reading_v1.md`;
`feedback_no_prng_generation_side`). v2 replaces the null with a **generator-free STRUCTURAL null** (§1) —
the fix §E.3 demands ("matched null sharing the signal's forced symmetries") — so the estimand becomes
"does the real 82-key SET's number-theoretic cubic-difference structure on secp deviate from pseudorandom
curve points?", IN bounds per the 2026-08-18 boundary. This *widens* what the test sees.

**Mission/brick compliance (reviewed vs `btc CLAUDE.md` Statement of intent + roadmap §0).** Counter-prior:
E3=13125 is the standout owed positive (A-1d ★★); this surfaces-and-tests it, does not pre-deflate (no
outcome is forecast in this spec; every arm carries a decision rule, not a prediction). Burden-on-closure:
each dissolve/non-significant branch (§4) must emit object+observable+power+scope AND a named next probe —
never a bare "door shut." Brick: standalone (scripts+frozen nulls, §6), reusable (structural-null
percentile, `p_FWER`, `q_MT`, the field-fixed CM-required fact), direction-true (carries null/control/OOS/
grade).

---

## 1. Structural null (shared forced symmetries — gate-confirmed matched)

**Structural null = uniform random valid secp curve points.** Draw `x∈[0,P)` uniform; accept iff `x³+7` is a
QR mod P (`(x³+7)^((P−1)/2)=1`), i.e. `x` is a genuine `E(F_P)` point x-coord. `N_null=20000` draws of 82,
frozen seed **`20260818`**. **Shares** (gate-confirmed): the valid-x population, the j=0/μ₆ cubic bias on
x-differences, `C(82,2)=3321` pairs, forced `a+b+c=3321` & `E3≡0 mod3`, MP floor `≈2√82`. **Does not share:
only** the real d-multiset (the tested contrast). Generator provenance retired. (This is the
`RESULT_diffset_cubic_secondcontrol_v1.md` Control-2 population, here the pre-registered primary null.)

## 2. Arms (all pre-committed; decisions fixed before data)

### A1 — reproduction + structural null (secp). PRIMARY MAGNITUDE. [FIX: decidable boundary + symmetric p]
- Recompute `E3(real,secp)`; **assert** `==13125`, `(1082,1057,1182)`, `a+b+c=3321`, `E3≡0 mod3` (abort on
  mismatch — path bug).
- **Pinned decision boundary (α=0.05 two-sided), as integer order statistics of the sorted null:**
  `L_struct = null_E3_sorted[floor(0.025·N_null)]`, `U_struct = null_E3_sorted[floor(0.975·N_null)]`.
  **Decision: REJECT-HIGH iff `E3(real) > U_struct`** (matches the original frozen-region method that gave
  `[84,11997]`).
- **Symmetric two-sided rank p** (FIX — `+1` on BOTH counts):
  `p_struct = min(1, 2·min( (ge+1)/(N+1), (le+1)/(N+1) ))`, `ge=#{null≥E3}, le=#{null≤E3}`, `N=N_null`.
- **Pre-committed:** `E3(real) > U_struct` ⇒ set-level deviation vs pseudorandom curve points is present;
  carry to A2. `E3(real) ≤ U_struct` ⇒ **DISSOLVED** — the anomaly lived only vs a generator pool; bound
  E3's generator-channel magnitude (power A4, scope = marginal cubic energy) + next probe = group-law E3.

### A2 — family-wise MC-correction over {E2,E3,E6}. [FIX: tie convention + symmetric +1]
Exact Westfall–Young max-statistic (min-p) FWER on the SAME structural null.
- Per-statistic two-sided p of value `v` against sorted null of that statistic, **tie convention `≥`/`≤`
  inclusive, applied identically to the real value and to every null draw's own value**:
  `p_s(v)=min(1, 2·min((#{null_s≥v}+1)/(N+1), (#{null_s≤v}+1)/(N+1)))`.
- For each null draw `i`: `minp_i = min(p_E2(E2_i), p_E3(E3_i), p_E6(E6_i))` (plug-in against the full null
  incl. self — bias O(1/N), negligible at N=20000, **disclosed**).
- Observed: `minp_real` and `p_E3_obs=p_E3(13125)`.
- **`p_FWER(E3) = (#{i: minp_i ≤ p_E3_obs} + 1)/(N+1)`** (FIX: symmetric `+1`).
- Also report conservative **Bonferroni ×7** for the heterogeneous 2026-07-26 session family {μ₆-marg,
  χ₂-marg, 12-cell, KW, point-biserial, S_diff, E3} (KW/point-biserial reference d/bits → Bonferroni-bounded,
  not max-stat members) — disclosed as a bound, not the primary.
- **Pre-committed (neither branch prejudged):** `p_FWER ≤ 0.05` ⇒ E3 survives look-elsewhere ⇒ characterize.
  `p_FWER > 0.05` ⇒ family-wise non-significant ⇒ **bounded magnitude with power+scope** (the character-family
  look-elsewhere bound, reusable), NOT a signal and NOT a cubic-channel closure (E3 is one marginal
  projection); next probe = the orthogonal-mode suppression (6.5th pctile, `spectral §Diagnostics`).

### A3 — OOS on the constructed known-generator set. PRIMARY = rank within band-matched MT sets. [FIX: fully partitioned]
The constructed known-MT19937 pool is the full-power known-generator set (`feedback_test_on_both_sets`); the
band-matched MT sets are a **matched control sharing the real bit-band structure**. Draw `M_oos=1000`
independent 82-sets from `constructed_keys_1to160_100k.csv`, each matched one-per-real-bit-band (bits list in
§0-real); take the constructed `X` (hex) directly (no EC mul); compute each set's `E3`. Frozen seed
**`20260818`**.
- **Primary statistic:** `q_MT = #{MT-set E3 ≥ E3(real)=13125} / M_oos` — real's rank among band-matched MT
  sets. **Secondary diagnostic:** median MT-set E3-percentile vs the A1 structural null (explains WHY).
- **Pre-committed (fully partitioned):**
  - `q_MT ≤ 0.05` ⇒ real E3 is high even among band-matched known-MT sets ⇒ the excess needs the specific
    real d-values, NOT the bit-band/pipeline (consistent with band-arms E3=0.503) ⇒ **set-specific**
    (layered with A1/A5 for generator-vs-curve; A3 alone does not separate those).
  - `0.05 < q_MT ≤ 0.50` ⇒ real elevated but within the band-matched MT spread ⇒ **partial**; report the
    `(1−q_MT)` quantile as the bounded residual + next probe (triples `C(82,3)` / band-localized).
  - `q_MT > 0.50` ⇒ real is typical of / below band-matched MT sets ⇒ the E3 excess (vs uniform structural
    null) is a shared bit-band/pipeline property, NOT real-specific ⇒ bound to the pipeline channel + next
    probe (a statistic separating set from pipeline).

### A4 — firing control (instrument power). MUST FIRE. [gate: SOUND — unchanged]
E3 = f(cube-class marginals), so a β²-count-excess plant is exactly matched. On a structural-null 82-set's
counts `(a,b,c)`, plant `(a−⌊Δ/2⌋, b−⌈Δ/2⌉, c+Δ)` (sum fixed 3321); sweep `Δ` over `{0, 25, 50, 75, 100,
150}` (real is `+75` above the class mean). Power = P(reject-high vs A1's `U_struct`) over 500 planted draws
per Δ, frozen seed **`12345`**.
- **Gate:** power monotone in Δ; `Δ=0` false-positive rate `≈0.025` (one-sided upper, calibration);
  power `≥0.9` by `Δ=150`. Else instrument under-powered ⇒ A1/A2 uninformative, record + STOP.

### A5 — curve-class discriminator (FORM-LEVEL). CONDITIONAL + re-gated. [FIX: redesigned]
**Run only if A1 REJECTs-HIGH** (investigation>sharpening: don't chase curve-class specificity for a
dissolved core). **Re-audited by `experiment-designer` before running** (substantive redesign).
- **Field-fixed CM-required fact (already established, reused):** secp (j=0/μ₆/CM) fires; **E′**
  (`y²=x³+x+1` over secp's P, j≠0, non-CM) fails-to-reject (67.1st, `RESULT_diffset_cubic_cmvanishing_v1.md`).
  Both over the SAME prime P ⇒ same χ₃ field character ⇒ no field confound. This is the legitimate form-level
  content: **the E3 excess requires secp's CM/j=0 map**, banner-admissible with its own proof obligation.
- **μ₄-vs-μ₆ discriminator — OBSTRUCTED over F_P (recorded as a structural scope fact).** secp's `P≡3 mod4`
  (verified) ⇒ j=1728 `y²=x³+Ax` is **supersingular** over F_P (trace 0, order P+1), `√−1∉F_P` ⇒ the μ₄
  automorphism is **not F_P-rational**, and `P` is **not** a sum of two squares (no Cornacchia). So the clean
  μ₄/ℤ[i]/ordinary-CM object does not exist over secp's own field; a "null on j=1728 over F_P" would be
  **supersingularity**, not "μ₄ orthogonal-lattice ⇒ trivial cubic carry." **The μ₄ test is unavailable
  field-fixed.**
- **Optional μ₄ check (field-CONFOUNDED, graded weakly):** if pursued, run over a prime `p′≡1 mod4 ∧ p′≡1
  mod3` (so ℤ[i] ordinary AND χ₃ nontrivial), testing the `RESULT_cm_ring_universality_v1.md` prediction
  (μ₄ → trivial cubic carry vs μ₆ → nontrivial). Grade `[EMPIRICAL — form-level, FIELD-CONFOUNDED]`; the
  cross-prime χ₃ change is a NAMED confound; NOT banner-admissible toward secp. **P-256 dropped** (different
  prime = same field confound; E′ already serves the non-CM role field-fixed).

## 3. Power ceiling & scope (before data)
- **N=82 is the entire sample; cannot grow.** #135 unsolved; no solved-key statistic transfers except via a
  generation model (out of bounds). Raw `p≈0.033` cannot become strong under null redraws.
- **Max attainable:** a characterized, family-wise-corrected weak anomaly **at secp scale** (E3 is at the
  real prime + real keys — NOT scale-blocked), OR a bounded magnitude with power+scope, OR a dissolution.
  **Never** a keyspace reduction or extractability. E3 is a marginal rank-1 statistic on 3321 differences,
  blind to orientation-odd / joint-triple / band-localized subspaces.
- **Grades:** A1/A2 `[VERIFIED/EMPIRICAL @ secp]` percentile + `p_FWER` w/ power+scope, or `[DISSOLVED-ON-
  TEST]`. A3 `q_MT` bound. A5 field-fixed CM-required fact `[EMPIRICAL — form-level]`; the μ₄ arm (if run)
  `[EMPIRICAL — form-level, FIELD-CONFOUNDED]`. No grade elsewhere moves on this run.

## 4. Falsification summary (every branch is a brick; none a door shut)
1. A1 `E3≤U_struct` → generator-channel bound + next probe (group-law E3). DISSOLVED-positive.
2. A2 `p_FWER>0.05` → character-family look-elsewhere bound + next probe (orthogonal-mode suppression).
3. A3 `q_MT>0.50` → pipeline/bit-band bound + next probe (set-vs-pipeline separator).
4. A1 REJECT + A2 `p_FWER≤0.05` + A3 `q_MT≤0.05` → set-specific cubic structure at secp, family-wise sig →
   characterize β²-excess (which pairs/bands); + A5 field-fixed CM-required fact. Sharper law, NOT a break.
5. A4 under-powered → uninformative, STOP (instrument brick owed).

## 5. Mortar checklist
- [ ] exact integer signal path; `check_no_float.sh` passes on the new script
- [ ] structural (generator-free) null sharing forced symmetries — not the MT pool, not a forced control
- [ ] A4 firing control registers plants with monotone power; Δ=0 FPR ≈ nominal
- [ ] A3 OOS (band-matched MT) computed before naming any zero
- [ ] forced quantities (`a+b+c`, `E3≡0 mod3`) are bug-checks, not evidence
- [x] `experiment-designer` audit recorded (§7); v2 fixes all four HOLD items; A5 re-gated before running
- [ ] every output graded with power+scope; magnitudes vs form-level kept on separate ledgers

## 6. Artifacts (to be produced)
`e3_owed_measurement_v1.py` (A1–A4, self-contained integer path); frozen nulls
`e3_struct_null_{E2,E3,E6}_v1.npy`; `e3_owed_measurement_v1.log`; (A5, conditional) separate script + re-gate.

## 7. experiment-designer audit (verbatim disposition)
HOLD, four items; core engine (object, exactness, structural-null forced-symmetry match, feature/target
disjointness, A4) ruled SOUND. Dispositions:
1. **A5 misspecified over F_P (decisive)** → REDESIGNED (this §A5): μ₄ obstruction recorded as a scope fact;
   E′ (field-fixed non-CM) is the CM-required discriminator; optional μ₄ arm moved to `p′≡1 mod4` with the
   field confound NAMED; P-256 dropped; "banner-admissible" removed from the μ₄ arm; A5 conditional + re-gated.
2. **A1 `U_struct` undefined** → FIXED: pinned as `null_E3_sorted[floor(0.975·N)]`; decision REJECT-HIGH iff
   `E3(real)>U_struct`.
3. **A3 60–90 band unassigned** → FIXED: reframed to `q_MT` with a full 3-way partition.
4. **A1/A2 `+1` anti-conservative + tie convention** → FIXED: symmetric `+1` both counts; `≥`/`≤` inclusive
   ties applied identically to real and null.

*Predecessors: `_v1` (draft), `RESULT_diffset_cubic_v1/_secondcontrol/_cmvanishing`, `CORRECTION_e3_cmvanishing_interaction_reading_v1`, `RESULT_spectral_decomp_v1`, `RESULT_chi2_diffset_FALSE_POSITIVE_v1`, `RESULT_cm_ring_universality_v1`. Debt: MASTER_v12 §E.3.*
