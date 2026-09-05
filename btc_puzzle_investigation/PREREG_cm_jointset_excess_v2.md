# PREREG — A-joint v2: CM-structured JOINT-SET synergy excess in the public data of a scalar tuple

**File:** `PREREG_cm_jointset_excess_v2.md`  **Date frozen:** 2026-08-21
**Supersedes:** `PREREG_cm_jointset_excess_v1.md` (NOT runnable as frozen — its second-read found
4 defects). This v2 applies every fix; the object, the disjointness ruling, and the choice of statistic
are UNCHANGED (all passed). **Status: SPEC ONLY. No confirmatory statistic computed in producing this.**
Implementation target (not yet written): `cm_jointset_excess_v2.py`, importing `model_curve_infra_v1.py`.

**Change log v1→v2 (each traced to a second-read audit item or citation deviation):**
- **[item 3] §3 matched null:** global permutation of `Ψ` → **restricted permutation WITHIN each `Φ^pt`
  stratum** (the exact matched null for a conditional-MI statistic).
- **[item 4] §4 PC-SEM:** the v1 plant forced `±P₁±P₂±P₃=O` ⇒ `S₃≡0` ⇒ `Ψ≡0` constant ⇒ it could
  never fire, and the VOID rule named it ⇒ every arm spuriously VOIDed. Replaced by a **non-degenerate
  mixture plant** (below), with an explicit non-constant-`Ψ` guard.
- **[item 5] §5 power:** `df = 4` → **`df = 4·s`**, `s = #non-empty `Φ^pt` strata` (=27 at m=3); floor
  recomputed (`MI_min ≈ 7.9×10⁻³` @N=5k, `2.0×10⁻³` @N=20k). §7/§9 figures updated.
- **[item 8 / D4] §6 selection:** anomalous (trace-1) exclusion now applied to **BOTH** arms (CM and
  non-CM matching), not the CM arm only.
- **[D2] §8:** Semaev S₃ vanishing stated over `K̄` (exact over `F_q` for genuine `E(F_q)` x-coords),
  hypothesis `char q ≠ 2,3` added.
- **[D3] §5:** the `O(√q/N_ord)` floor re-attributed to a **Weil-type** bound (KS 2000's single-character
  elliptic theorem covers additive `e_p(rational f)`, not the multiplicative `χ₃`/`χ₃(S₃)` features).

**Freeze protocol:** at run start the runner prints this file's SHA-256 into the RESULT and opens
`PREREG_cm_jointset_excess_v2_DEVIATIONS.md`. Any post-freeze change to statistic/null/filter/scope/
falsification is a disclosed deviation.

---

## 0. SCOPE BANNER (governs every number the run emits)

- **Curves.** Enumerable model curves `E : y² = x³ + Ax + B` over small prime `F_q`, `q ≡ 1 mod 3`,
  PRIME group order `N`. **`q = 2²⁵⁶−2³²−977` is NOT enumerable; nothing here transfers to secp256k1.**
  Primary primes `q ≲ 2¹⁶` are ~240 binary orders below `2²⁵⁶` and carry **zero power** against the real
  curve. This measures a MECHANISM (does CM structure produce joint-set synergy at model scale), never
  the real object.
- **No ECDLP / extraction / security claim** appears anywhere in this spec or any verdict it licenses.
- **Two matched arms at each `q`:**
  - **CM arm** — `j = 0` (`A = 0`), `E : y² = x³ + B`, CM by `Z[ω]`; efficient endomorphism `[λ]`,
    `λ³ ≡ 1 mod N`, `[λ](x,y) = (βx, y)`, `β³ ≡ 1 mod q`, `β ≠ 1`.
  - **non-CM arm** — ordinary, `j ∉ {0, 1728}`, CM discriminant `|D| ≥ D_min := ⌊√q⌋`, matched to the CM
    curve on `q` and as closely as possible on prime group order.
  - **BOTH arms exclude anomalous (trace-1, `N=q`) curves** (§6, D4) — anomalous curves admit Smart's
    per-point `d` recovery, which would confound a joint-synergy contrast on either side.
- **The object is a JOINT property of a SET**, never a per-point marginal (subtracted out by
  construction, §1–§2). A per-point readout that recovered a scalar would BE a break.

---

## 1. OBJECT  (UNCHANGED from v1 — passed the second-read)

**Hypothesis (A-joint).** For a SET of `m` targets — scalars `d_1,…,d_m` drawn INDEPENDENTLY uniform,
each from its own KNOWN short interval `I_i = [2^{b−1}, 2^b)`, `b < log₂ q`, public data `P_i = [d_i]G`
— the CROSS-target public functions of the set (GLV images, small-coefficient combination points
`x([a]P_i + [c]P_j)`, and Semaev values `S_r(x(P_{i₁}),…)`) carry SYNERGISTIC information about a
pre-committed JOINT label of the tuple that EXCEEDS what the per-point readouts carry about their own
labels, AND this excess is CM-specific (present on the CM arm, absent on the matched non-CM arm at the
same `q`).

**The object is the synergy `E`, not raw joint MI.** The `d_i` are independent ⇒ the pairs
`(Φ_i^pt, T_i)` are mutually independent across `i`, so with per-point-only features
`MI((Φ_i^pt)_i ; (T_i)_i) = Σ_i MI(Φ_i^pt ; T_i)` EXACTLY (chain rule; verified sound by the
second-read). `E` is the amount the CROSS-target data raises joint MI ABOVE that forced marginal sum.
`E ≥ 0` (data-processing), so the verdict is a RANK against a matched null, never `E` vs 0.

**Disjointness / tautology ruling (passed).** Features are field-side `F_q` functions of the public
points (`χ₃(x(P_i))`, `x([λ^k]P_i)=β^k x(P_i)`, combo x-coords, `χ₃(S_3(...))`); labels are scalar-ring
(`Z/N`, interval) functions of the `d_i`. No scalar/residue/interval index of `d_i` is ever a feature.
Feature and target reach the common secret through disjoint operations in disjoint rings; recovery is
the DLP. Not the `r=v−w` artifact; not the linear-relation check (that is a control, §4). The one
per-point CM relation `χ₃(βx)=1+χ₃(x)` is conditioned out by `Φ^pt`.

**Forcedness ruling.** `E`'s reachable set is not a singleton: `E=0` under per-point-only features
(shown); `E>0` under the §4 mixture plant; features are low-cardinality (alphabet 3) so per-point
marginals do not saturate `H(T_i)`.

---

## 2. STATISTIC  (statistic choice UNCHANGED; df accounting moved to §5)

Fix `m = 3` (primary). Per-point block `Φ^pt = (χ₃(x(P_1)), χ₃(x(P_2)), χ₃(x(P_3))) ∈ {0,1,2}³`
(27 strata). Targeted at the μ₃/CM channel:
- **Targeted cross-feature** `Ψ = χ₃( S_3(x(P_1),x(P_2),x(P_3)) ) ∈ {0,1,2}` — the cubic class of the
  Semaev `r=3` value on the three x-coordinates (a single small-alphabet function of ALL THREE points).
- **Targeted joint label** `J = (d_1 + d_2 + d_3) mod 3 ∈ {0,1,2}` — the μ₃-covariant joint residue.

**PRIMARY statistic (conditional MI — isolates the synergy):**
```
Î_prim(arm) = Î( Ψ ; J | Φ^pt ) = Σ_{u} p̂(Φ^pt=u) · Î( Ψ ; J | Φ^pt = u )   (bits, Miller–Madow)
```
This is `E` in targeted form (the chain-rule excess `I(Φ^pt,Ψ;J) − I(Φ^pt;J)`).

**VERDICT-BEARING statistic:** `Δ = Î_prim(CM) − Î_prim(non-CM)` at matched `(q, order-match, |I|, m,
feature set, G-rule)`, its significance from the paired CM/non-CM sign across the frozen schedule (§3).

**CO-PRIMARY OMNIBUS (guard against a channel `Ψ` misses):**
`Î_omni(arm) = Î( (L_{12}, L_{13}, L_{23}) ; (T_1,T_2,T_3) | Φ^pt )`, `L_{ij}=χ₃(x([1]P_i+[1]P_j))`,
`T_i=d_i mod 3`. Higher df, ranked against the SAME null family; NEVER overrides the primary — a primary
null is reported as "no synergy in the *Semaev-μ₃* channel," and an omnibus-only firing names a
different cross channel as the next probe.

**SECONDARY LABEL (separate ledger):** repeat with the interval-position label
`J' = (Σ_i block(d_i)) mod 2`, `block(d_i)∈{0,1}`. Own null, own power floor, own outcome row (§9).

The float `log₂` inside MI is a monotone scalar RANKED against the §3 permutation null; the reported
p-value is the exact integer permutation count.

---

## 2R. ANTI-TAUTOLOGY  (UNCHANGED — passed)

Features (`F_q`) and labels (`Z/N`, interval) are built by disjoint code paths sharing no intermediate
beyond `(E, q, the set)`; recovering a label from a feature is the DLP. Enforced by two separate
functions with disjoint inputs. No feature is a difference/component sharing construction with the
target.

---

## 3. MATCHED CONTROL  ([item 3] within-stratum permutation)

**PRIMARY matched null (destroys ONLY the object).** Draw `N` sets; compute `Φ^pt`, `Ψ`, `J` per set.
**Permute the cross-feature `Ψ` WITHIN each `Φ^pt` stratum** — i.e. among the sets sharing a given value
`Φ^pt = u`, permute their `Ψ` values, holding `Φ^pt` and the labels fixed; repeat for every `u`. For the
omnibus, permute the `(L_{12},L_{13},L_{23})` block within each `Φ^pt` stratum jointly. Recompute
`Î_prim`/`Î_omni`; rank the observed value against `≥10⁴` such restricted permutations; report
`p =` exact integer count `/ #perm`.
- **PRESERVES:** every set's per-point marginals `Φ_i^pt↔T_i`; the FULL conditional law `p(Ψ|Φ^pt=u)` in
  every stratum `u` (the fix — v1's GLOBAL permutation destroyed the `Ψ↔Φ^pt` association and thereby
  tested the stronger, wrong null `Ψ⊥(Φ,J)` instead of `Ψ⊥J|Φ`; measured `I(Ψ;Φ^pt)=0.0083` bits > 0 at
  q=541 confirms the two nulls provably differ, and the gap can be CM-arm-larger so it is NOT netted by
  the paired Δ — the "shuffle breaks a forced symmetry" class); the marginal of `Ψ`; the label structure.
- **DESTROYS:** ONLY the `Ψ ↔ J` coupling within strata — exactly `E`.

**SECONDARY calibration null (full-tuple label shuffle).** Permute the whole label tuple across sets —
confirms the estimator's zero-point (`Î_prim ≈ 0` when all coupling removed). Never the verdict null.

**Why a fresh-random-key surrogate is INVALID:** the `d_i` are already independent uniform, so a fresh
draw is distributionally identical — it tests nothing. The discriminating null acts on the
`feature↔label` coupling, not the key distribution.

**CM-vs-non-CM contrast null for Δ.** Each arm's `Î_prim` is ranked against its OWN within-stratum null;
`Δ`'s significance is the paired sign across the frozen schedule (swap the CM/non-CM arm label within
each matched `q`, recompute `Δ`, rank) — so a generic (arm-independent) estimator bias cancels.

---

## 4. PLANTED CONTROL  ([item 4] non-degenerate mixture PC-SEM; VOID rule repaired)

All plants inject into the CONDITIONED-IN cross channel (a plant into `Φ^pt` leaves `Î(Ψ;J|Φ^pt)`
unmoved — the second-read confirmed this placement). ALL required plants must fire or the arm's null is
uninformative (VOID).

- **PC-LIN (linear-relation plant — machinery, MUST fire).** Synthetic sets with a hidden linear
  relation `d_3 := (−a·d_1 − c·d_2) mod N` (small `a,c`), coupling the tuple so `J` is partly determined
  by `(d_1,d_2)`; the cross combo `L_{ij}` gains joint info. Require `Î_omni` (and `Î_prim` where the μ₃
  algebra lands on `Ψ`) to fire at exact perm `p < 0.01`, `z ≥ 5`. **A control, NOT the hypothesis.**
- **PC-SEM (Semaev-feature plant — the hypothesis-shaped positive, MUST fire) — REBUILT.** Draw `N`
  sets. For a planted fraction `ρ` (primary `ρ=0.30`): keep `d_1,d_2` as drawn; **resample `d_3` (fresh
  uniform in `I_3`) until `χ₃( S_3(x(P_1),x(P_2),x(P_3)) ) == (d_1+d_2+d_3) mod 3`** — i.e. force the
  Semaev cubic class `Ψ` to equal the joint residue `J` on planted sets, using a REAL `E(F_q)` point
  `P_3=[d_3]G` (so `S_3` is generically NONZERO — the v1 degeneracy `S_3≡0 ⇒ Ψ≡0` is gone). A match is
  found in ~3 draws (`χ₃(S_3)` is ~uniform over `{0,1,2}` as `d_3` varies); if `>K_max=100` draws fail
  for a set, that set is dropped (logged). The unplanted `1−ρ` fraction is generic (`Ψ ⊥ J`).
  - **Requirement:** `Î_prim(Ψ;J|Φ^pt)` fires at exact perm `p < 0.01` at `ρ=0.30`, and is **monotone
    increasing** across `ρ ∈ {0, 0.15, 0.30, 0.60}`. Because `Ψ=χ₃(S_3)` is NOT a function of `Φ^pt`
    (`S_3` mixes coordinates nonlinearly), conditioning on `Φ^pt` does not absorb the coupling.
  - **Non-degeneracy guard (the v1 defect, now asserted):** on the planted fraction `Ψ` MUST be
    non-constant (assert `#distinct(Ψ_planted) ≥ 2`) and `S_3 ≠ 0` on ≥99% of planted sets. If `Ψ` is
    constant or `S_3≡0`, the plant is mis-built ⇒ STOP (do NOT VOID the science arm — fix the plant).
  - This proves the instrument fires on a genuine **Semaev-feature↔label** coupling — the exact shape of
    A-joint. (Note: `S_3=0 ⟺ ±d_1±d_2±d_3≡0 mod N` is LINEAR in the scalars; PC-SEM's distinctiveness is
    the FEATURE path `χ₃(S_3)`, not scalar nonlinearity — v1's characterization corrected.)
- **PC-GRADE (graded plant — resolution floor).** `Ψ_plant := J XOR₃ Uniform₃(mix ρ')` for
  `ρ'` giving true `MI(Ψ_plant;J) ∈ {MI_min, 2·MI_min, 4·MI_min}` (§5); require monotone firing and the
  `MI_min` rung to fire at ≥80%.
- **PC-nonCM (arm control).** The matched non-CM arm is the control for CM-specificity of `Δ`.

**VOID rule (repaired).** If **PC-LIN or PC-SEM** does not fire at a given `(q,N)`, the instrument is
dead at that scale ⇒ the real result on that arm is VOID; no null claimed. **A mis-built plant (guard
above tripped) is a STOP-and-fix, not a VOID** — it must be distinguished from a genuine non-firing.

---

## 5. POWER  ([item 5] df = 4·s; [D3] Weil-type floor)

Detection model: `G = 2N · MI · ln2 ~ χ²_df` under H0, noncentral `λ_nc = 2N · MI_true · ln2` under H1.
`MI_min(N) = λ_nc / (2N · ln2)` at 80% power, `α = 0.01`.

- **PRIMARY `Î_prim` — df is `4·s`, NOT 4.** `Î_prim` conditions on `Φ^pt`, so its G-statistic has
  `df = Σ_{non-empty strata u} (|Ψ|−1)(|J|−1) = 4·s`, `s = #non-empty Φ^pt strata`. At `m=3` all `s=27`
  strata are non-empty by `N=5k` (verified in the second-read). `λ₈₀(df=108) = 54.9` (α=0.01) ⇒
  `MI_min = 54.9/(1.386·N) ≈ 39.6/N` bits:
  - Discovery `N=5,000`: **`MI_min ≈ 7.9×10⁻³` bits.**
  - Confirmation `N=20,000`: **`MI_min ≈ 2.0×10⁻³` bits.**
  `s` is computed EXACTLY per `q` before the power line is reported (empty strata reduce `df` and the
  floor). The exact within-stratum permutation p-value is the verdict and is unaffected by the df model.
- **OMNIBUS `Î_omni`** (27 conditioned tables; effective `df` large, heavily under-sampled): higher
  `MI_min`; the omnibus is a co-primary guard, not the headline (a many-cell omnibus is upward-biased,
  low-power).
- **Sample-count feasibility.** Sets are `(d_1,d_2,d_3)∈I^3`; at `b≥9`, `|I|^3≥2^{24}≫N` ⇒ no
  exhaustion; `N` sets drawn with a pinned seed. Where `|I|^m ≤ 10⁷` the whole product is enumerated and
  the EXACT-law `E` (a rational) is reported alongside as an oracle cross-check.
- **A null is scoped to "`MI < MI_min(N)`", NEVER "no synergy."** The relevant single-character floor is
  a **Weil-type** bound of order `√q/N_ord` (general Weil/Deligne bound for MULTIPLICATIVE and
  multivariate character sums — the class `χ₃(x)`, `χ₃(S_3)` live in; KS 2000's single-character elliptic
  theorem covers ADDITIVE `e_p(rational f)` readouts and is NOT the authority here — citation-verified,
  D3). No feasible model-scale sample approaches it; the test detects only GROSS synergy.

---

## 6. SCOPE / PARAMETERS  ([D4] anomalous excluded on BOTH arms)

- **Prime schedule (deterministic setup from public curve data; logged, NOT a verdict statistic;
  frozen in `schedules_v1/schedule_A_joint_v1.json`, SHA `c533f669…`):**
  - `q ≡ 1 mod 3`; the `j=0` curve `y²=x³+B_q` has PRIME order `N` **AND trace `t=q+1−N ≠ 1`**
    (D1/D4: exclude anomalous), `B_q` = smallest such `B` (B-witness).
  - **DISCOVERY:** smallest 3 with `q>500` = **{541, 571, 577}** (547 dropped, anomalous-only).
  - **CONFIRMATION (disjoint, OOS):** smallest 3 with `q>2000` = {2029, 2053, 2089}.
  - **SCALE ladder:** smallest such `q` exceeding each of `2^{10},2^{12},2^{14},2^{16}` = {1033, 4111,
    16417, 65539}.
- **non-CM matching rule (frozen; D4):** over the SAME `q`, ordinary `y²=x³+Ax+B`, `j∉{0,1728}`,
  `|t²−4q| ≥ ⌊√q⌋`, **`t ≠ 1` (exclude anomalous — D4)**, minimizing `|N_non − N_CM|`; tie-break
  smallest `j`, then `(A,B)` lex. Report `N_non`, `N_CM`, the order gap, AND `t_non` on every Δ.
- **Generator rule (both arms):** `G` = prime-order point of smallest `x`, then smaller `y`.
- **`m` = 3** primary; `m=2` pairs-only cross-check; `m=4` scale-up where power permits.
- **Interval:** `b = ⌊log₂ q⌋ − 2`.  **`ℓ = 3`** primary label modulus; interval-block secondary.
- **`N`:** 5,000 (discovery), 20,000 (confirmation); pinned seed `20260821`; `#perm ≥ 10⁴`.
- **Every reported `Î`, `Δ`, `p` carries `(arm, q, N_CM, N_non, t_non, |I|, m, N, s, MI_min)`.**

---

## 7. FALSIFICATION  (single condition; MI_min at the corrected floor)

- **A-joint RETAINED (CM-specific joint synergy) ⇔** on the CM arm `Î_prim` FIRES (within-stratum null
  exact `p ≤ 0.01`) AND `Δ = Î_prim(CM) − Î_prim(non-CM) > 0` beyond the paired contrast null across the
  frozen schedule, with PC-LIN, PC-SEM, PC-GRADE having fired.
- **A-joint ABANDONED at this scope ⇔** `Δ ≤ 0` within the permutation null across the whole frozen
  schedule, every positive control fired. Reported as a scoped magnitude bound
  `|Δ| < MI_min(N) (≈7.9×10⁻³ @5k, ≈2.0×10⁻³ @20k)` with power + scope, plus the untested-channel list
  (§9) — NEVER "no structure / dead / generic."
- **VOID (no verdict) ⇔** PC-LIN or PC-SEM did not fire at a given `(q,N)` (plant mis-build ⇒ STOP-fix,
  distinct from VOID, §4).

---

## 8. EXACTNESS  (int / Fraction signal path)

- Curve arithmetic (`add`, `double`, `[λ]`, combos), x-coords, `χ₃` (via `pow(z,(q−1)//3,q)` matched to
  the fixed `{0,1,2}` labels), `S_3` (exact `F_q` polynomial) — all `int mod q`.
- **Semaev S₃ (citation-verified, D2):** `S_3=0 (mod q)` iff there exist `y_i ∈ K̄` (algebraic closure)
  with `(x_i,y_i)∈E` and `±P_1±P_2±P_3=O`; for `x_i` = x-coords of genuine `E(F_q)` points (this test's
  use) the `y_i` are in `F_q`, so the `E(F_q)` restatement is exact. Hypothesis `char q ≠ 2,3` (held:
  `q > 500` prime). Coefficients match Semaev Thm 1 exactly (verified — do not "correct" them).
- Labels `d_i mod 3`, `(Σd_i) mod 3`, interval-block: `int`. MI counts `int`; `p̂` `Fraction`; ratio
  comparisons by integer cross-product.
- **Float carve-out (analytic-size only):** the `log₂` inside MI, used ONLY as a monotone scalar RANKED
  against the exact integer within-stratum permutation-count p-value. No key/coord/feature value is
  float-thresholded. `check_no_float.sh` must exit 0 (flags confined to the statistic/plant/report layer).

---

## 9. PRE-COMMITMENT  (every outcome a named POSITIVE characterization; MI_min at corrected floor)

| Outcome | Trigger | Pre-committed conclusion | Grade |
|---|---|---|---|
| **CM-specific joint synergy** | PC-LIN+PC-SEM+PC-GRADE fired; `Î_prim(CM)` `p≤0.01`; `Δ>0` beyond paired null across schedule | CM structure produces Semaev-μ₃ joint-set synergy absent on the matched non-CM arm. Report `Δ` (bits) + 95% rank interval + scope `(q, N_CM/N_non, t_non, |I|, m=3, N, s)` + ladder trend. **NEXT:** cell-decompose which `Φ^pt` stratum carries it; higher `r` Semaev; `m=4`; other `ℓ`. Do NOT verdict, do NOT claim ECDLP transfer. | **EMPIRICAL (mechanism, model-scale)** |
| **CM-independent joint synergy** | `Î_prim` fires on BOTH arms; `Δ ≈ 0` within paired null | Joint synergy exists but is GENERIC to `d↦(x,y)`, not CM-specific. Characterize the shared channel. | **EMPIRICAL (generic)** |
| **Off-target channel** | `Î_prim(CM)` null but `Î_omni(CM)` or interval-label arm fires `p≤0.01`, `Δ>0` | Effect lives in the combo/interval channel, not Semaev-μ₃. Record the firing channel as a NAMED next probe. | **EMPIRICAL (off-target)** |
| **Scoped null** | all PCs fired; `Î_prim` AND `Î_omni` AND interval arm within matched null; `Δ ≤ 0` across schedule | `|Δ| < MI_min(N)` (`≈7.9×10⁻³` @5k, `≈2.0×10⁻³` @20k): no CM-specific joint synergy in the projected {Semaev-μ₃, combo, interval} channels at `q≲2¹⁶`, `m=3`. A BOUNDED MAGNITUDE with power+scope, NOT a closure — Weil floor uncrossed. **Untested next:** `r≥4` Semaev; `m≥4`; `ℓ∈{other primes|N}`; GLV-mixed features; a coordinate-pair (x&y) statistic; finer interval label. | **VERIFIED-scope (scoped null)** |
| **Void** | PC-LIN or PC-SEM did not fire at `(q,N)` | Instrument dead at that scale; bank NO null; report power ceiling and the `N` needed. | **VOID** |

The **scoped-null row carries the symmetric burden** (anomaly-drill §4c): OBJECT (CM-specific
Semaev-μ₃/combo/interval joint synergy of an `m`-set), CLASS (label-valued cross features up to `r=3`
Semaev), POWER (`MI_min` at df=4·s), SCOPE (`q≲2¹⁶`, `m=3`). A scoped null, not a dismissal.

---

## Owed gates (status)
- `citation-verifier` on Semaev S₃ + the single-character floor: **DISCHARGED 2026-08-21** — S₃ SUPPORTS
  (exact); floor re-attributed to the Weil bound (D3). No grade may cite KS "single-character elliptic
  theorem" strength for the χ₃ features.
- **Second independent `experiment-designer` read of THIS v2: OWED** before any Δ promotes.
- `compile-diff` if this line is ever folded into a master / handover document.
