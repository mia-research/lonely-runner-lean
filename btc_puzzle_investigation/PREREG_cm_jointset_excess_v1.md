# PREREG — A-joint: CM-structured JOINT-SET synergy excess in the public data of a scalar tuple (v1)

**File:** `PREREG_cm_jointset_excess_v1.md`  **Date frozen:** 2026-08-21
**Status: SPEC ONLY. Written and FROZEN before any confirmatory data is seen. No confirmatory
statistic computed in this task.** Decidable artifact. Designed by the context-isolated
`experiment-designer` agent (object-level; no outcome predicted).
Implementation target (not yet written): `cm_jointset_excess_v1.py`.

---

## 0. SCOPE BANNER (governs every number the run emits — inherited by every Δ, every p, every bound)

- **Curves.** Enumerable model curves `E : y² = x³ + Ax + B` over small prime fields `F_q`,
  `q ≡ 1 mod 3`, PRIME group order `N`. **`q = 2²⁵⁶−2³²−977` is NOT enumerable; nothing here
  transfers to secp256k1.** The scale banner is TOTAL: the primary primes `q ≲ 2¹⁶` are ~240 binary
  orders below `2²⁵⁶` and carry **zero power** against the real curve. This measures a **MECHANISM**
  (whether CM structure produces joint-set synergy at model scale), never the real object.
- **No ECDLP / extraction / security claim** appears anywhere in this spec or any verdict it licenses.
- **Two matched arms at each `q`:**
  - **CM arm** — `j = 0` (`A = 0`), `E : y² = x³ + B`, CM by `Z[ω]`, `ω` = primitive cube root of
    unity; efficient endomorphism `[λ]`, `λ³ ≡ 1 mod N`, `[λ](x,y) = (βx, y)`, `β³ ≡ 1 mod q`, `β ≠ 1`.
  - **non-CM arm** — ordinary curve, `j ∉ {0, 1728}`, CM discriminant `|D| ≥ D_min` (no small-disc CM),
    matched to the CM curve on `q` and (per §6 rule) as closely as possible on prime group order.
- **The object is a JOINT property of a SET**, never a per-point marginal. A per-point readout that
  recovered a scalar would *be* a break; the setup grants single-point public readouts are
  (heuristically) redundant with the point, so the per-point marginal is an EXPECTED null and is
  **subtracted out** by construction (§2). This test is about the SET.

---

## 1. OBJECT (name the object, not a proxy — and the tautology / forcedness rulings up front)

**Hypothesis under test (A-joint).** For a SET of `m` targets — scalars `d_1,…,d_m` drawn
**independently** uniform, each from its own KNOWN short interval `I_i = [2^{b−1}, 2^b)`, `b < log₂ q`,
with public data `P_i = [d_i]G` — the *cross-target* public functions of the set (GLV images,
small-coefficient linear-combination points `x([a]P_i + [c]P_j)`, and Semaev summation-polynomial
values `S_r(x(P_{i₁}),…,x(P_{i_r}))`) carry **synergistic** mutual information about a pre-committed
JOINT label of the tuple that **exceeds what the per-point readouts carry about their own labels**,
AND this excess is a function of the curve's CM structure — present on the CM arm, absent on the
matched non-CM arm at the same `q`.

**The object is the synergy `E`, not raw joint MI.** Because the `d_i` are drawn INDEPENDENTLY,
their labels `T_i` are independent, and any per-point feature `Φ_i^pt` (a function of `P_i` alone) is
independent of `T_j` for `j≠i`. Hence, **with no cross-target feature**, `MI((Φ_i^pt)_i ; (T_i)_i) =
Σ_i MI(Φ_i^pt ; T_i)` **exactly** — the joint MI is forced to equal the sum of marginals. The object
`E` (defined in §2) is exactly the amount by which the **cross-target** public data (Semaev / combo /
GLV-mixing) raises joint MI ABOVE that forced marginal sum. `E = 0` iff the cross features add nothing
beyond per-point readouts. `E ≥ 0` always (data-processing: the cross-augmented feature is a
super-function of the per-point block), so the verdict is a RANK against a matched null, never `E` vs 0.

**Disjointness / tautology ruling (mandatory, decided pre-run).**
- The feature vector is built **entirely from field-side operations on the public points**: cubic
  residue symbols `χ₃(x(P_i)) ∈ F_q`, GLV images `x([λ^k]P_i) = β^k x(P_i)`, combo points
  `x([a]P_i + [c]P_j)` via the exact group law, and Semaev values `S_r(x_{i₁},…,x_{i_r}) ∈ F_q`.
  **No scalar `d_i`, no residue `d_i mod ℓ`, no interval index of `d_i` is ever fed into a feature.**
- The target labels are **scalar-ring** functions of the `d_i` (`d_i mod 3`; the sum `Σ d_i mod 3`;
  the interval-block index). Feature (field `F_q`) and target (ring `Z/N`, interval position) reach the
  common secret through **disjoint operations in disjoint rings**; recovering the target from the
  feature is the DLP. **Not a tautology; test valid before it runs.**
- **Explicitly not the forbidden `r = v − w` artifact:** no feature is a difference/component that
  shares construction with the target. **Explicitly not the linear-relation check:** the prior null
  `Σ a_i d_i ≡ 0 mod N` looks for a coupling IN THE SCALARS (absent — the `d_i` are independent). `E`
  reads the FIELD-side cross features and can be nonzero from CM-nonlinear structure even though the
  scalars are linearly independent. The linear relation appears ONLY as a firing control (§4), never
  as the object.

**Forcedness ruling (rule 4b — "write the set of values `E` can take before any data"): NOT a
singleton.** (a) With independent labels and per-point-only features, `E = 0` (shown above) — the
zero value is reachable. (b) A planted cross-relation (§4) makes `E > 0` — a positive value is
reachable. (c) Saturation is avoided by construction: features are **low-cardinality label-valued**
(alphabet 3 per cubic symbol, ≤3 per Semaev class), so `|image(Φ_i^pt)| = 3 ≪ |I_i| = 2^{b−1}` and
the per-point marginals do **not** saturate `H(T_i)` — leaving room for the cross term. `E`'s
achievable range is therefore not a singleton; the cell is not decoration.

---

## 2. STATISTIC (exactly one primary; targeted at the CM channel; low-df; not a max-over-cells)

Fix `m = 3` targets per set (primary). Per-point block `Φ^pt = (χ₃(x(P_1)), χ₃(x(P_2)), χ₃(x(P_3)))`,
each `∈ {0,1,2}` (cubic-residue index of the x-coordinate; `χ₃(0):=0`). Targeted cross-feature and
joint label are aimed AT the μ₃ / CM channel (where the `λ³≡1` endomorphism would couple the set):

- **Targeted cross-feature** `Ψ = χ₃( S_3(x(P_1), x(P_2), x(P_3)) ) ∈ {0,1,2}` — the cubic class of
  the `r=3` Semaev summation-polynomial value on the set's three x-coordinates. This is a single
  small-alphabet function of ALL THREE points jointly (not any one point).
- **Targeted joint label** `J = (d_1 + d_2 + d_3) mod 3 ∈ {0,1,2}` — the μ₃-covariant joint residue.

**PRIMARY statistic (conditional MI — isolates the synergy):**
```
Î_prim(arm) = Î( Ψ ; J | Φ^pt )
            = Σ_{u∈Φ^pt strata} p̂(Φ^pt=u) · Î( Ψ ; J | Φ^pt = u )   (bits, Miller–Madow corrected)
```
This is the info the Semaev cross-feature `Ψ` adds about `J` **beyond** the per-point readouts `Φ^pt`
— i.e. `E` in targeted form. Aimed at the predicted channel (df ≈ 4 per non-empty stratum for the
`3×3` `Ψ×J` table). Low-df for power; **not** a max over many cells.

**VERDICT-BEARING statistic (the pre-registered headline):**
```
Δ = Î_prim(CM) − Î_prim(non-CM)     at matched (q, order-match, |I|, m, feature set, G-rule)
```

**CO-PRIMARY OMNIBUS (catches cross structure the targeted `Ψ` misses — the "subspace we are not
projecting onto" guard):** `Î_omni(arm) = Î( (L_{12}, L_{13}, L_{23}) ; (T_1,T_2,T_3) | Φ^pt )`, where
`L_{ij} = χ₃(x([1]P_i + [1]P_j)) ∈ {0,1,2}` and `T_i = d_i mod 3`. Higher df; ranked against the SAME
null family; **never overrides the primary** — it exists so a null on `Î_prim` is reported as
"no synergy in the *Semaev-μ₃* channel," not "no synergy," and a firing here with `Î_prim` null names
a *different* cross channel as the next probe.

**SECONDARY LABEL (pre-registered, separate ledger):** repeat `Î_prim` and `Î_omni` with the
**interval-position** joint label `J' = (Σ_i block(d_i)) mod 2`, `block(d_i)∈{0,1}` = upper/lower half
of `I_i`. Reported with its own null and its own power floor; a separate outcome row (§9).

Distribution of each statistic under H0 = the matched permutation distribution (§3). The float `log₂`
inside MI is used ONLY as a monotone scalar RANKED against that null; the reported p-value is the exact
integer permutation count `#{perm : stat_perm ≥ stat_obs} / #perm`.

---

## 3. MATCHED CONTROL (the null reproduces every structure of the real data EXCEPT the cross-coupling)

**PRIMARY matched null (destroys ONLY the object).** Draw `N` sets. Compute `Φ^pt`, `Ψ`, `J` for each.
**Permute the cross-feature block `(Ψ)` — and, for the omnibus, `(L_{12},L_{13},L_{23})` jointly — across
the `N` sets, holding each set's per-point block `Φ^pt` and its label(s) `J`/`(T_i)` FIXED.** Recompute
`Î_prim`/`Î_omni`. Rank the observed value against `≥10⁴` such permutations; report `p =` exact integer
count `/ #perm`.
- **PRESERVES:** each set's per-point marginals `Φ_i^pt ↔ T_i` (the by-definition μ₃ readout of each
  point is never touched — this is the fix for the "6–7σ soft-shadow" null-mismatch, where a shuffle
  destroyed a symmetry the readout has by definition); the marginal distributions of `Ψ`, of the combo
  labels, and of `J`/`(T_i)`; the full `Φ^pt` joint law; the label independence structure.
- **DESTROYS:** ONLY the `cross-feature ↔ label` coupling — exactly `E`.

**SECONDARY calibration null (full-tuple label shuffle).** Permute the whole label tuple across sets.
Destroys marginal AND cross coupling; used only to confirm the estimator's zero-point and that
`Î_prim ≈ 0` when all coupling is removed. Never the verdict null.

**Why a fresh-random-key surrogate is INVALID here:** the `d_i` are already independent uniform draws,
so a "fresh independent draw" is distributionally identical to the real arm — it tests nothing. The
discriminating null must act on the `feature↔label` coupling, not on the key distribution.

**CM-vs-non-CM contrast null for Δ.** `Î_prim(CM)` and `Î_prim(non-CM)` are each ranked against their
OWN primary matched null. `Δ`'s significance is the paired sign of `Δ` across the frozen prime schedule
(§6) assessed by a paired permutation (swap the CM/non-CM arm label within each matched `q`, recompute
`Δ`, rank) — so a `Δ>0` driven by a generic (arm-independent) estimator bias cancels.

---

## 4. PLANTED CONTROL (positive controls; ALL must fire or the arm's null is uninformative — full stop)

All plants inject structure into the CONDITIONED-IN cross channel (`Ψ` / combo block), because a plant
into `Φ^pt` would leave `Î(Ψ;J|Φ^pt)` unmoved and fail to fire — recorded so the control cannot be
silently mis-built. **Plant/null overlap (rule 4b-a):** the matched null perturbs the `cross↔label`
coupling; every plant injects into that same coupling ⇒ the plant can clear the null.

- **PC-LIN (linear-relation plant — machinery, MUST fire).** Build synthetic sets with a genuine hidden
  linear relation `d_3 := (−a·d_1 − c·d_2) mod N` (small `a,c`), so the tuple is coupled and `J` becomes
  partly determined by `(d_1,d_2)` ⇒ the cross combo `L_{ij}`/`Ψ` gain joint info. Require
  `Î_omni` (and where the μ₃ algebra lands on `Ψ`, `Î_prim`) to fire at exact perm `p < 0.01`, `z ≥ 5`.
  Proves the instrument detects a real joint relation. **This is a control, NOT the hypothesis.**
- **PC-SEM (Semaev-type nonlinear plant — the hypothesis-shaped positive, MUST fire).** Build sets where
  a subset of size 3 is FORCED to satisfy a Semaev relation `S_3(x_1,x_2,x_3)=0` (choose `P_3` on the
  curve so that `±P_1±P_2±P_3 = O` for a pre-fixed sign pattern; the `d_3` this implies is then labeled).
  This injects NONLINEAR cross structure that the linear-relation check is blind to. Require `Î_prim`
  to fire at exact perm `p < 0.01`. Proves the instrument fires on nonlinear joint structure — the exact
  shape of A-joint.
- **PC-GRADE (graded plant — calibrates the resolution floor).** `Ψ_plant := J XOR₃ Uniform₃(mix ρ)`
  for a schedule of mixing rates `ρ` giving true `MI(Ψ_plant;J) ∈ {MI_min, 2·MI_min, 4·MI_min}` (§5);
  require monotone firing and that the `MI_min` rung fires at ≥80%. Confirms the instrument resolves at
  its stated floor.
- **PC-nonCM (arm control).** The matched non-CM arm is itself the control for CM-specificity of `Δ`.

**VOID rule.** If PC-LIN or PC-SEM does not fire at a given `(q, N)`, the instrument is dead at that
scale ⇒ the real result on that arm is **VOID**; no null claimed (`feedback_prereg_abstention_is_the_finding`).

---

## 5. POWER (pinned as numbers, before the run)

Detection model: `G = 2N · MI · ln2 ~ χ²_df` under H0, noncentral `λ_nc = 2N · MI_true · ln2` under H1.
`MI_min(N) = λ_nc / (2N · ln2)` at 80% power, `α = 0.01`.

- **PRIMARY `Î_prim`** (`Ψ×J` = 3×3, `df ≈ 4`; `λ_nc ≈ 15.0` for 80% power at `α=0.01`):
  `MI_min ≈ 15.0 / (1.386·N) ≈ 10.8 / N` bits.
  - Discovery cell `N = 5,000`: **`MI_min ≈ 2.2×10⁻³` bits.**
  - Confirmation cell `N = 20,000`: **`MI_min ≈ 5.4×10⁻⁴` bits.**
- **OMNIBUS `Î_omni`** (`27 × 27` conditioned; effective `df ≈ 40` after pooling empty cells;
  `λ_nc ≈ 60`): `MI_min ≈ 43 / N` bits ⇒ `≈ 8.6×10⁻³` (N=5k), `≈ 2.2×10⁻³` (N=20k). The omnibus is
  under-powered relative to the targeted arm by ~4× — this is WHY `Î_prim` is primary and the omnibus
  is a co-primary guard, not the headline (a max-over-many-cells omnibus is upward-biased and low-power).
- **Sample-count feasibility.** Sets are `(d_1,d_2,d_3)` from `|I|^3 = 2^{3(b−1)}` possibilities; at
  `b ≥ 9`, `|I|^3 ≥ 2^{24} ≫ N` ⇒ no exhaustion; `N` independent sets are drawn with a pinned seed.
  Where `|I|^m ≤ 10⁷` the **entire product `I^m` is enumerated** and the EXACT-law `E` (a rational,
  no estimator noise) is reported alongside the sampled statistic as an oracle cross-check.
- **A null is scoped to "`MI < MI_min(N)`", NEVER "no synergy."** No feasible model-scale sample
  approaches the Kohel–Shparlinski single-character floor `O(√q/N_ord)`; the test detects only GROSS
  synergy.

---

## 6. SCOPE / PARAMETERS (frozen; deterministic selection, no post-hoc choice)

- **Prime schedule (deterministic, computed in setup from public curve data only — NOT a verdict
  statistic, logged with the run):**
  - `q ≡ 1 mod 3`, and the `j=0` curve `y² = x³ + B_q` has PRIME order `N`, where `B_q` = smallest
    positive `B` yielding prime order (the "B witness rule").
  - **DISCOVERY primes:** the smallest 3 such `q > 500`.
  - **CONFIRMATION primes (disjoint, OOS):** the smallest 3 such `q > 2000`.
  - **SCALE ladder (reads Δ vs `q`):** the smallest such `q` exceeding each of `2^{10}, 2^{12}, 2^{14},
    2^{16}` (may overlap the above; deduplicated). The ladder is the pre-committed instrument for
    "grows / holds / shrinks with `q`."
- **non-CM matching rule (frozen):** over the SAME `q`, the ordinary curve `y²=x³+Ax+B`, `j∉{0,1728}`,
  Frobenius-CM discriminant `|D| ≥ D_min := ⌊√q⌋`, minimizing `|N_non − N_CM|` over a deterministic
  enumeration of `(A,B)`; tie-break by smallest `j`, then smallest `(A,B)` lex. Report `N_non`, `N_CM`,
  and the order gap on every Δ.
- **Generator rule (both arms):** `G` = the prime-order point of smallest `x`, then smaller `y`.
- **`m` = 3** primary; `m = 2` reduced cross-check (pairs only, `Î` on `L_{12}`); `m = 4` scale-up
  only where power (§5) permits.
- **Interval:** `b` = `⌊log₂ q⌋ − 2` (so `|I| = 2^{b−1} < q`, wrap-free `d_i < N` for the schedule).
- **`ℓ = 3`** primary label modulus (μ₃/CM channel). Interval-block secondary label as in §2.
- **`N`:** 5,000 (discovery), 20,000 (confirmation), pinned seed `20260821`. `#perm ≥ 10⁴`.
- **Every reported `Î`, `Δ`, `p` carries `(arm, q, N_CM, N_non, |I|, m, N, MI_min)`.**

---

## 7. FALSIFICATION (single condition, written before the run)

- **A-joint RETAINED (CM-specific joint synergy) ⇔** on the CM arm `Î_prim` FIRES (matched-null exact
  `p ≤ 0.01`) AND `Δ = Î_prim(CM) − Î_prim(non-CM) > 0` beyond the paired contrast null across the
  frozen schedule, with PC-LIN, PC-SEM, PC-GRADE having fired.
- **A-joint ABANDONED at this scope ⇔** `Δ ≤ 0` within the permutation null across the whole frozen
  schedule (all discovery + confirmation + ladder primes), with every positive control fired. Reported
  as a **scoped magnitude bound** `|Δ| < MI_min(N)` carrying power + scope, plus the untested-channel
  list (§9) as next candidates — **never** "no structure / avenue dead / generic."
- **VOID (no verdict) ⇔** PC-LIN or PC-SEM did not fire at a given `(q,N)`.

---

## 8. EXACTNESS (int / Fraction signal path — project no-float rule)

- Curve arithmetic (group law, doubling, `[λ]`, combo points `[a]P_i+[c]P_j`) over `F_q` via `int` and
  modular inverse `pow(z, q−2, q)`; x-coords `int mod q`.
- `χ₃(z) = ` cubic-residue index via `pow(z,(q−1)//3, q)` matched to `{1, g^{(q−1)/3}, g^{2(q−1)/3}}`
  (`g` fixed primitive root) → `{0,1,2}`; integer comparisons only.
- Semaev `S_3(x_1,x_2,x_3)` evaluated as an exact `F_q` polynomial (`int mod q`); `Ψ = χ₃(S_3)`.
- Labels `d_i mod 3`, `(Σ d_i) mod 3`, interval-block index: `int` arithmetic.
- MI counts are `int`; `p̂` are `Fraction`; all balance/ratio comparisons by integer cross-product.
- **Float carve-out (justified, analytic-size only, no key in path):** the `log₂` inside MI and the
  ordering of `Î` values — a monotone analytic function of already-exact rational counts, used ONLY to
  produce a scalar RANKED against the matched permutation null. **The verdict is the exact integer
  permutation-count p-value.** No key/coord/feature-derived value is thresholded by a float.
- `check_no_float.sh` (btc_puzzle_investigation) must exit 0 with float flags confined to the
  statistic/plant/reporting layer before any run.

---

## 9. PRE-COMMITMENT (every outcome is a named POSITIVE characterization; grade slot filled before run)

| Outcome | Trigger | Pre-committed conclusion | Grade |
|---|---|---|---|
| **CM-specific joint synergy** | PC-LIN+PC-SEM+PC-GRADE fired; `Î_prim(CM)` `p≤0.01`; `Δ>0` beyond paired null across schedule | CM structure produces Semaev-μ₃ joint-set synergy absent on the matched non-CM arm. Report `Δ` (bits) + 95% rank interval + scope `(q, N_CM/N_non, |I|, m=3, N)` + ladder trend (grows/holds/shrinks with `q`). **NEXT PROBE:** cell-decompose which `Φ^pt` stratum carries it; test higher `r` Semaev, `m=4`, other `ℓ`; report symmetry type — do NOT verdict, do NOT claim ECDLP transfer. | **EMPIRICAL (mechanism, model-scale)** |
| **CM-independent joint synergy** | `Î_prim` fires on BOTH arms; `Δ ≈ 0` within paired null | Joint synergy exists but is GENERIC to the `d↦(x,y)` map, not CM-specific. Reclassify as a bounded arm-independent magnitude; characterize the shared channel. | **EMPIRICAL (generic)** |
| **Synergy in a channel we did not project onto** | `Î_prim(CM)` null but `Î_omni(CM)` (or the interval-label arm) fires `p≤0.01`, `Δ_omni>0` | Effect lives in the combo/interval cross channel, not the Semaev-μ₃ one. Record the firing channel as a NAMED next probe; do NOT report the "abandoned" row. | **EMPIRICAL (off-target channel)** |
| **Scoped null (A-joint not retained at scope)** | All PCs fired; `Î_prim` AND `Î_omni` AND interval-label arm all within matched null; `Δ ≤ 0` across schedule | `|Δ| < MI_min(N)` (`≈2.2×10⁻³` bits @N=5k, `≈5.4×10⁻⁴` @N=20k): no CM-specific joint synergy in the projected {Semaev-μ₃, combo, interval} channels at `q ≲ 2¹⁶`, `m=3`. A BOUNDED MAGNITUDE with power+scope, NOT a closure — KS floor uncrossed. **Untested next candidates:** `r≥4` Semaev; `m≥4`; `ℓ∈{other primes | N}`; GLV-mixed features `x([λ]P_i+[λ²]P_j)`; a coordinate-pair (x&y) joint statistic; a finer interval-position label. Structure in these is NOT excluded. | **VERIFIED-scope (scoped null)** |
| **Void** | PC-LIN or PC-SEM did not fire at `(q,N)` | Instrument dead at that scale; bank NO null; report power ceiling and the `N` needed. | **VOID** |

The **scoped-null row takes the symmetric burden** (anomaly-drill §4c): it names OBJECT (CM-specific
Semaev-μ₃/combo/interval joint synergy of an `m`-set), CLASS of observable (label-valued cross features
up to `r=3` Semaev), POWER (`MI_min`), SCOPE (`q≲2¹⁶`, `m=3`) — it is a scoped null, not a dismissal;
no dismissal vocabulary is licensed.

---

## Owed gates (no grade moves up until these clear)
- `citation-verifier` on the Semaev summation-polynomial `S_3` definition and on the Kohel–Shparlinski
  single-character floor used in §5, **before** any grade cites their strength.
- `compile-diff` if this line is ever folded into a master / handover document.
- `experiment-designer` pass: this spec IS that artifact; a second independent read is owed before the
  run promotes any Δ.
