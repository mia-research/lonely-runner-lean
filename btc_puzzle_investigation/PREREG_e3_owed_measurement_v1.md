# PREREG — E3 (A-1d) owed measurement: structural-null reframe + FWER + OOS + curve-class discriminator

**Date drafted 2026-08-18. Status: DRAFT — frozen only after `experiment-designer` sign-off.**
Discharges `ROADMAP_REDIRECT_v3.md` **Brick A** and `POSITIVE_FINDINGS_MASTER_v12.md` **§E.3**
("E3 (A-1d) owes a MEASUREMENT"). Object under test is **fixed and named before any new data is drawn**.
Integer-exact throughout (`int`/`gmpy2`, no float in the signal path). No security/keyspace/extractability
claim is made or reachable by this design; see §Power ceiling.

---

## 0. The object under test (fixed, reproduced, not re-derived)

**E3 = field-difference cubic-character energy** of the real 82 solved-puzzle pubkey x-coordinates on
secp256k1. For x-set `{x_1,…,x_82}` (n=82, `C(82,2)=3321` unordered pairs):
- for each pair `i<j`, `z=(x_i−x_j) mod P`; cube class `c(z)=χ₃(z)∈{0,1,2}` via `z^((P−1)/3) mod P ∈ {1,β,β²}`;
- counts `(a,b,c)` over the three classes; **`E3 = a²+b²+c²−ab−bc−ca`** (= class-count variance = ¼|1ᵀC1|²,
  the all-ones projection of the pairwise cubic matrix, per `RESULT_spectral_decomp_v1.md`).

**Known value (to be reproduced exactly, not assumed):** `E3(real,secp)=13125`, counts `(1082,1057,1182)`,
`a+b+c=3321`, `E3≡0 mod 3`. Source `RESULT_diffset_cubic_v1.md`.

**Statistic family (for FWER).** The three multiplicative-character energies of the SAME field-difference
set, computed from one 6-cell histogram `H[3q+c]` (`q`=QR-bit, `c`=cube-class) via `stats3` of
`c2_grouplaw_diffset_curve_v1.py` (reused verbatim for reproducibility):
`E2=(n_q0−n_q1)²`, `E3` (above), `E6` (sextic). These are the natural look-elsewhere family for "cubic
energy of the difference set" (could equally have read quadratic or sextic energy of the identical set).

---

## 0.5 Mission & brick compliance (reviewed against `btc CLAUDE.md` Statement of intent + roadmap §0)

- **Counter-prior honored.** E3=13125 is the *standout owed positive* (MASTER A-1d ★★). This design
  **surfaces and tests** it; it does not pre-deflate it. The one-way suppression tell — predicting a null
  in the spec — was removed (A2/§4 carry decision rules, not outcome forecasts). No branch is prejudged.
- **In-bounds by construction, not by narrowing.** The generator angle is excluded by *replacing the null*
  (structural, generator-free) — the estimand becomes number-theoretic key-set structure, which the
  2026-08-18 boundary places IN. This widens what the test can see; it is not a scope-cut.
- **Burden on the closure.** Each DISSOLVED / non-significant branch (§4) is required to emit object +
  observable-class + power + scope AND a named next probe — the same bar as a positive. A bare "dead/
  generic/artifact" verdict is disallowed here.
- **Brick, not hole-in-one.** Standalone (scripts + frozen nulls, named in §Artifacts-to-come); reusable
  (structural-null percentile, `p_FWER`, the curve-class form-table); direction-true (carries null/control/
  OOS/grade). The most reusable arm is **A5** — a form-level law (which curve classes carry the cubic set
  structure) that is banner-admissible toward secp with its own proof obligation, and that tests the
  `RESULT_cm_ring_universality_v1` μ₄/μ₆ prediction.

## 1. The frame this measurement fixes (why the prior nulls do not settle it)

Prior E3 nulls were drawn from `constructed_keys_1to160_100k.csv`, a **known-MT19937 pool**. Against a
generator pool the estimand is *"do the real integers differ from a known generator's output?"* — a
**generator** test (`CORRECTION_e3_cmvanishing_interaction_reading_v1.md`, 2026-07-31: *"if the matched
null is drawn from a generator pool, the test is a generator test, whatever the instrument"*), which is
out of bounds (`btc CLAUDE.md` Scope; `feedback_no_prng_generation_side`). **This measurement replaces the
null with a generator-free STRUCTURAL null** — the exact fix `§E.3` demands ("a matched
Farey/fundamental-domain null **sharing the signal's forced symmetries**"). Against a structural null the
estimand becomes *"does the real 82-key SET's number-theoretic cubic-difference structure on secp deviate
from pseudorandom curve points?"* — **in bounds** per the 2026-08-18 PRNG-boundary decision
(number-theoretic structure of the key IN; generator OUT).

**Structural null = uniform random valid secp curve points.** Draw points `P` uniformly on `E(F_P)`
(`Curve.rand_point`), take `x(P)`. Under ECDLP-pseudorandomness `x([d]G)` for the real d's is compared to
`x(P)` for uniform random `P`: same population (x-coords of curve points), differing only in whether the
82 points are the puzzle images or uniform. This is the `RESULT_diffset_cubic_secondcontrol_v1.md`
Control-2 population (generator-agnostic; there E3(real) sat at 98.1st pctile), here promoted to the
**pre-registered primary null** and enlarged.

**Forced symmetries the structural null SHARES with the signal** (so it is matched, not a foreign
control): (i) x-coords of genuine secp `E(F_P)` points → carries the curve's own j=0/μ₆-induced cubic
bias on x-differences; (ii) exactly `C(82,2)=3321` pairs; (iii) the forced `a+b+c=3321`, `E3≡0 mod 3`;
(iv) Marchenko–Pastur spectral floor `≈2√82` (`RESULT_spectral_decomp_v1.md`). It does **not** share the
real d-values — the sole tested contrast. The forced-symmetry, generator-provenance concern is thereby
retired.

---

## 2. Arms (all pre-committed; each names its decision BEFORE data)

Nulls use a frozen seed; `N_null=20000` structural draws (2.4× the prior 10000). All exact integer.

### A1 — reproduction + structural null (secp). PRIMARY MAGNITUDE.
- Recompute `E3(real,secp)`; **assert** `==13125`, counts `(1082,1057,1182)`, `a+b+c=3321`, `E3≡0 mod 3`
  (integrity gate; a mismatch aborts the run — path bug).
- Percentile & two-sided rank p of `E3(real)` in the `N_null` structural null.
- **Pre-committed decision.** `p_struct = 2·min(#{null≥E3},#{null≤E3}+1)/(N_null+1)`.
  - `E3(real) ≤ U_struct` (fails to clear the structural upper region) ⇒ **the anomaly did not survive the
    generator-free null** ⇒ it was generator-pool-specific ⇒ `[DISSOLVED-ON-TEST]`, bound reported.
  - `E3(real) > U_struct` ⇒ the set-level deviation is real vs pseudorandom curve points; carry to A2.

### A2 — family-wise MC-correction (the core §E.3.1 debt).
Exact **max-statistic permutation FWER** over `{E2,E3,E6}` on the SAME structural null:
- For each null draw compute `(E2,E3,E6)`; convert each to its within-family upper-tail rank; take the
  per-draw **max** rank across the three statistics.
- `p_FWER(E3) = #{null draws whose max-rank ≥ E3(real)'s rank} / N_null` — the honest family-adjusted p.
- Also report the conservative **Bonferroni ×7** bound for the full heterogeneous 2026-07-26 session
  family {μ₆-marg, χ₂-marg, 12-cell, KW, point-biserial, S_diff, E3}, noting which are structural-null
  computable (KW/point-biserial reference d/bits, so they are Bonferroni-bounded, not max-stat members).
- **Pre-committed reading (neither branch prejudged; the run decides).** `p_FWER ≤ 0.05` ⇒ E3 survives
  look-elsewhere on the character family ⇒ escalate to characterization. `p_FWER > 0.05` ⇒ family-wise
  non-significant on the character family ⇒ reported as a **bounded magnitude with power+scope** (the
  character-family look-elsewhere bound is itself a reusable fact), **not** a signal and **not** a closure
  of the cubic channel (E3 is one marginal projection — see §3 scope).

### A3 — OOS on the constructed known-generator set (§E.3.4 + `feedback_test_on_both_sets`).
The constructed known-MT19937 pool is the **full-power known-generator set**; the statistic must be run on
it too. Draw `M_oos=500` independent 82-subsets from `constructed_keys_1to160_100k.csv` matched to the real
keys' bit-bands; map each `d` to `x([d]G)` on secp; compute each set's `E3`, and its percentile vs the A1
structural null.
- **Pre-committed reading.** median known-MT `E3`-percentile:
  - `≤ ~60th` (a null draw) ⇒ known-generator sets are unremarkable ⇒ the real-82's high percentile is
    **specific to the real set**, not generic to the select-bitlen→curve pipeline. (Consistent with the
    band-arms `E3=0.503`.) SUPPORTS the finding as set-specific.
  - `≥ 90th` ⇒ the pipeline itself biases E3 high ⇒ the real anomaly is a **pipeline artifact** ⇒
    `[DISSOLVED-ON-TEST]`.

### A4 — firing control (instrument power). MUST FIRE.
Plant a cubic β²-count excess of strength `ε` into structural-null x-sets (bias a fraction `ε` of pairs
toward class β² — an all-ones/marginal-count plant matched to E3's actual rank-1 sensitivity, NOT a block
plant, since `RESULT_spectral_decomp_v1.md` showed E3 is the marginal projection). Sweep
`ε∈{0,0.02,0.05,0.10}`; report reject-high power at each.
- **Gate.** Power must be monotone in `ε` and reach `≥0.9` by `ε=0.10`, else the instrument is
  under-powered and A1's null/positive is uninformative (record and stop). A `ε=0` false-positive rate must
  sit at the nominal `≈0.05`.

### A5 — curve-class discriminator (FORM-LEVEL, banner-admissible). EXTENSION.
`E3(real 82)` mapped onto three curve classes, **each vs its OWN structural null** (uniform points on THAT
curve, so the curve-alone bias cancels within the arm — the interaction design of the correction §1):
| curve | class | role |
|---|---|---|
| secp | j=0, CM by ℤ[ω], μ₆ | the signal curve |
| P-256 | j≠0, non-CM | roadmap's named control curve; expect null (cf. E′ non-CM fail-to-reject) |
| j=1728 (`y²=x³+Ax` over secp's P, near-prime order via Cornacchia `P=a²+b²`) | CM by ℤ[i], μ₄ | **the discriminator** |

- **Pre-committed reading (a claim about the SYMMETRY CLASS, scale-invariant → admissible toward secp with
  its own proof obligation).**
  - fires on j=0 only (null on non-CM P-256/E′ AND null on μ₄ j=1728) ⇒ effect is **specifically cubic/μ₆**,
    matching `RESULT_cm_ring_universality_v1.md` (j=0 is the UNIQUE CM order with a nontrivial cubic carry
    gate; μ₄ is orthogonal-lattice ⇒ trivial). Strongest form-level brick.
  - fires on BOTH CM curves (j=0 and μ₄ j=1728) ⇒ "CM at all", not cubic-specific.
  - fires on non-CM P-256 as well ⇒ contradicts the E′ fail-to-reject (sanity failure) ⇒ re-audit instrument.
- **Confound named** (`CORRECTION` §4): choose j=1728 A giving near-prime order to remove the density
  confound E′ carried (`n′≈2¹⁸⁰` vs `2²⁵⁶`).

---

## 3. Power ceiling & scope (stated BEFORE data, so nothing is over-sold)

- **N=82 is the entire available sample and cannot grow.** #135 is unsolved; no statistic on solved keys
  transfers to it except through a generation model (out of bounds). The raw `p≈0.033` **cannot become
  strong** under any number of null redraws; more null precision ≠ more evidence.
- **Maximum attainable outcome of this brick:** a *characterized, curve-class-specific, family-wise-
  corrected* weak anomaly **at secp scale** (E3 is measured at the real prime P and the real keys — NOT
  scale-blocked), OR a bounded magnitude with power+scope, OR a dissolution. **Never** a keyspace reduction,
  a key recovery, or an extractability claim — E3 is a marginal rank-1 statistic on 3321 differences, blind
  to orientation-odd / joint-triple / band-localized subspaces (inherited caveat).
- **Grade targets:** A1/A2 → `[VERIFIED/EMPIRICAL @ secp]` percentile + `p_FWER`, with power+scope, OR
  `[DISSOLVED-ON-TEST]`. A5 → `[EMPIRICAL — form-level]` curve-class table, banner-admissible with its own
  proof obligation. No grade in any other document moves on this run.

## 4. Falsification summary (the run can end any of these ways — all are bricks)

Every branch must end in a **bounded magnitude with power+scope** or a **characterization + named next
probe** — none in a bare closure (roadmap §0-II: never a "door shut"; dissolution is positive).

1. A1 fails structural null (`E3≤U_struct`) → the set-level cubic deviation lives only against a generator
   pool, not against pseudorandom curve points → bound E3's generator-channel magnitude with power+scope;
   **next probe:** group-law E3 `χ₃(x(P_i−P_j))` (Frontier #29), the CM-native operation the field
   difference does not probe.
2. A3 known-MT median ≥90th → E3 is generic to the select-bitlen→curve pipeline → bound it as a
   pipeline-level magnitude (power = A4 curve; scope = marginal cubic energy); **next probe:** a statistic
   that separates set from pipeline (triples `C(82,3)`, band-localized structure).
3. A2 `p_FWER>0.05` → family-wise non-significant on the character family → the character-family
   look-elsewhere **bound** with power+scope (reusable); **next probe:** a non-marginal object (the
   orthogonal-mode suppression at 6.5th pctile, `spectral §Diagnostics`, is itself unexplained structure).
4. A2 `p_FWER≤0.05` + A3 set-specific + A5 fires j=0-only → cubic/μ₆-specific set structure at secp,
   family-wise significant → characterize the β²-excess (which pairs/bands), a sharper law (NOT a break;
   §3 ceiling holds).
5. A4 under-powered → whole run uninformative, recorded, stop (instrument brick owed before re-run).

## 5. Mortar checklist (roadmap §The mortar)
- [ ] exact integer signal path (no float); `check_no_float.sh` passes on new scripts
- [ ] structural (generator-free) null sharing forced symmetries — NOT the MT pool, NOT a forced control
- [ ] firing control (A4) registers a plant with monotone power
- [ ] OOS (A3) before naming any zero
- [ ] count only unforced hits; `a+b+c`, `E3≡0 mod3` are forced (bug-checks, not evidence)
- [ ] `experiment-designer` sign-off recorded here before freeze
- [ ] every output graded with power + scope; magnitudes vs form-level kept on separate ledgers

---
*Predecessors: `RESULT_diffset_cubic_v1.md`, `_secondcontrol_v1`, `_cmvanishing_v1`,
`CORRECTION_e3_cmvanishing_interaction_reading_v1`, `RESULT_spectral_decomp_v1`,
`RESULT_chi2_diffset_FALSE_POSITIVE_v1` (the arm-vary lesson), `RESULT_cm_ring_universality_v1` (the μ₄/μ₆
form prediction). Ledger debt: MASTER_v12 §E.3.*
