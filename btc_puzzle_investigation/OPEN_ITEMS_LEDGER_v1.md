> **⛔ FROZEN — NOT CURRENT.** This file is a historical snapshot. The single current-state
> document is **`CLAIMS.md`**. Do not read status, grades, or open items from here; do not
> write a successor version of this file. (Frozen 2026-09-01.)

# OPEN ITEMS — navigational ledger (2026-07-24)

> **THIS SUPERSEDES NOTHING AND PROMOTES NOTHING.** It is an index *into* the two authoritative
> frontier ledgers — `POSITIVE_FINDINGS_MASTER_v4.md §XI` (items 1–14, plus "Also live") and
> `POSITIVE_FINDINGS_ADDENDUM_1_v1.md §A5` (status deltas + items 15–25) — with today's additions
> appended. Every numbered item from both is carried; none is merged, reworded into a closure, or
> dropped. `compile-diff` was **not** run because this is not a promotion; if any of this is ever
> folded into a master, that gate applies then.
>
> **Why the paranoia:** `DEGRADATION_AUDIT_H3_TO_MASTER_v1.md` records live frontiers going **5 → 0**
> across one consolidation, invisible to tag-count auditing. Consolidation is the failure mode.

**Grouping is by whether the item involves the scalar `d` at all** — that was the question asked.

> **2026-07-24/25 — the reciprocity-bridge programme** (rows §A "new" below) is consolidated in
> **`BRIDGE_PROGRAMME_COMPENDIUM_v2.md`**, which carries all its open items, bounds, controls and
> deviations. **2026-07-25 extension** → `RESULT_ell_ge5_mutual_information_v1.md`: the ℓ≥5 blind spot
> that D3 left open is now **bounded away** — a choice-free mutual-information statistic (M0 verified
> choice-free; M1 proved it sees the uniform-correction case the old 2×2 was blind to; C+ fires on the
> known ℓ=3 bridge at p=0.0001) finds **no bridge at ℓ=5,7,11,13**. Two in-sample flickers (ℓ=11 MI
> p=0.002, ℓ=13 p=0.013) **both DIED out-of-sample** (0.66, 0.11) — drill protocol working.
> **2026-07-25 further extension** → `RESULT_ell_ge5_conditional_MI_v1.md`: the **conditional** blind
> spot the marginal probe pre-committed it could not see is now **also bounded away**. A choice-free
> stratified/targeted conditional-MI statistic mediated by `w = (t−1)/ℓ mod ℓ` (the pre-registered `3→ℓ`
> substitution of the mediator in the **[VERIFIED, not proved]** ℓ=3 law E3; an ℓ≥5 analogue existing is
> the hypothesis, not "forced") — **Mc+ shows the statistic rejects a synthetic uniform-shift coupling
> (p=0.0003) that marginal MI misses (p≈0.68–0.91)**; **C+ fires on the ℓ=3 bridge (p=0.0000)**; FPR
> tracks α; C-cong natural null with a planted positive that fires (p=0.0000, control has power) — finds
> **no conditional bridge at ℓ=5,7,11,13**. Two
> in-sample flickers (again ℓ=11,13, same seed-13 sample, Icond≈0.0014) **both DIED OOS** (ℓ=11→0.87
> deep null). `experiment-designer` audited the spec pre-data (required: Tcond primary at ℓ≥11 + C-cong
> planted positive — both folded in, independently verified). ⚠ Bound at the **OOS-achieved ~6%
> copy-fraction floor** (D1: 32-bit build fell short of N=12000), not a closure. **Still open (NOT
> closed):** **other mediators** — `v mod ℓ`, the second ℓ-adic digit `(t−1)/ℓ² mod ℓ`, global `(t,v)`
> structure (each a distinct conditional channel unaimed-at); secp's own factors `149, 631, …` (out of
> MI reach — `ℓ²` cells).
> **2026-07-25, the ideal-level item — CM ROUTE ANSWERED** → `RESULT_ideal_level_symbol_collapse_v2.md`:
> it **collapses by forced algebra**. `ν=1−π` ⇒ `π≡1 mod ν` ⇒ one CM factor is trivially 1 (factorization
> degenerate); the full-orbit ideal symbol in `ℚ(ζ_{3ℓ})` is ≡1; and **`π̄ ≡ t−1 (mod ν)` element-wise
> (250/250)** ⇒ **both bridge sides are symbols of the same RATIONAL `U=|t−1|`** — no ideal-level content
> in this route, because the elements reduce to rationals. ℓ=3 escapes because its correction rides on
> `μ₆` units + the ω-supplement, forced trivial at ℓ≥5 by `gcd(6,ℓ)=1` (200/200; **ℓ=3 live at 63/200**).
> ⇒ the ℓ≥5 question is exactly the **shared-`U`** channel (C-cong: null, with a planted positive that
> fires). ⚠ **The QUESTION is not void** — R1–R4 re-express both sides; a relation would still show in
> the same test at the same ~6% floor. ⚠ **Still open:** the classical law's OWN object (symbols of
> `ℤ[ζ_ℓ]`-elements with a choice of prime ideal) is **not** covered by this — `π̄,ν∈ℤ[ω]⊄ℤ[ζ_ℓ]`; and
> the **mechanism is UNGRADED**. ⚠⚠ **The `citation-verifier` pass on Lemmermeyer Ch. 7 was ATTEMPTED
> 2026-07-25 and FAILED (agent died on a session limit) — IT DID NOT COMPLETE, produced no artifact,
> and MUST BE RE-RUN.** The ★ literature item below therefore remains **fully undone**. Unverified lead
> from the failed run, to check not to cite: Silverman–Stange reportedly cites **Lemmermeyer Thm 7.10,
> sextic reciprocity in `ℚ(ω)`** — our CM field, so possibly a law stated for the right ring.
> ⚠ **v1 of that compendium is DEFECTIVE** — it self-certified completeness and a
> `compile-diff` run that had not happened; the audit found 11 DROPPED / 10 WEAKENED items. v1 is kept
> only as the audit trail. Audits: `AUDIT_citation_verification_v1.md` (2 corrections, 1 upgrade,
> **(B3) regraded to prior art**), `AUDIT_bridge_laws_independent_retest_v1.md` (post-hoc debt
> discharged, one flag **withdrawn**). **No novelty claim is supportable** until the literature sweep
> named in the compendium §4 is done.

---

## A. PURE CURVE / ARITHMETIC STRUCTURE — no `d`-side, no leakage question

These are open mathematics about `E: y²=x³+7`, `ℤ[ω]`, and secp's CM data. None of them needs a
leakage framing to be worth doing.

| # | item | status | why it is tractable |
|---|---|---|---|
| **16** | **`(†) C′−C = Σ_{s≤H} χ₂(s)·sgn(ρs mod p − s) = 3·h(−p)`** | `[VERIFIED 134 primes]`, the **single** open step of P2 | Proving it promotes **`|FLD| = 6h(−p)`** to a theorem. Elementary manipulation is *provably* circular; needs **generalized Dedekind sums / Rademacher**. The `3` is **not** a compositum class number (`h(−12p)/h(−p)` ranges `0.49…20.0`) — that route is closed off. |
| **8 / §XI.8** | **`L1`: `|Σ_{T⁺}χ₂| = F4`** (ONLY this is open) | OPEN, verified 86/86 | ⚠ **CORRECTED 2026-07-24:** this row previously bundled `H1`'s lemma `|T⁺|≡0 mod6 ⟺ χ₂(2)=1` as open — **it is NOT open: PROVED in `RESULT_flap_lemmas_P1P2_proofstatus_v2.md` (2026-07-21), = P1, `(−1)^N=χ₂(2)` via Gauss/Eisenstein.** The "two open items, one tool" note (also `NEXT_DIRECTIONS §4`) is **STALE/WRONG** — `(†)` (class-number tool) and `H1` (Eisenstein tool, already proved) are orthogonal (h-valued vs h-independent). Only `L1` (the `F4` magnitude) remains open. |
| **15** | **Jacobi sign law `J(χ₃,χ₄) = ∓p`** | ⚠ **UPDATED 2026-07-25** → `RESULT_jacobi_sign_law_semiprimitive_v1.md`. **`p≡11 mod 12` half `[PROVED — modulo (S)]`; `p≡7 mod 12` half OPEN and re-typed; `m=1` at secp STILL `[CONDITIONAL]`** | Classical input **(S) `g(χ_d) = (−1)^{(p+1)/d}·p` for `d\|p+1` over `F_{p²}`** (semiprimitive/subfield-trivial), **`[VERIFIED 43/43 cells, 12 primes]` — but its CITATION IS UNCHECKED** (the `citation-verifier` run failed on a session limit); used as verified-not-cited. **★ Sub-item DONE: the `G(χ₄)` 3-point rule is the `d=4` instance of (S)** — derived, then **verified 12/12 (9 out-of-sample)** ⇒ **bar lifted**, it was never a fit. **`p≡11 mod 12`: PROVED** — Frobenius forces `J` real (`χ₃^p=χ₃⁻¹`, `χ₄^p=χ₄⁻¹` ⇒ `conj J = J`, 12/12), and all three of `χ₃,χ₄,χ₁₂` are semiprimitive so the sign exponent is `4k+3k−k=6k`, always even ⇒ `J=+p` (6/6). **`p≡7 mod 12`: OPEN.** There `χ₃` is a norm-lift and `χ₁₂` is neither lift nor semiprimitive (`g(χ₁₂)` is **not** rational, 6/6); Frobenius yields only `σ₇`-invariance ⇒ `J∈ℤ[ζ₃]`, `\|J\|=p`, which **does NOT force `J=−p`** — `p` splits in `ℤ[ω]` so **`π²` also has norm `p²`** (exhibited every cell). **Re-typed: the gap is now "prove `J` is RATIONAL", not "prove a sign".** ⚠⚠ **The proved half is NOT secp's half** — secp is `p≡7 mod 12`, so `m=1` gets **no promotion**. |
| **new** | **The volcano's large-`ℓ` corner: `ℓ = 79, 349`** | OPEN | `f = 3·79·349·C112`. `h(O_ℓ) = 1` for `ℓ=1,2,3` (so the frame value is single-valued), but **`h(O_ℓ) > 1` at `ℓ ≥ 4`** ⇒ the frame value is a **SET**. Also open: **structure in which primes divide `f`**; and whether descending to `O_3/O_79/O_349` offers or removes a lever (explicitly **not foreclosed** — the "no d-side content" dismissal was withdrawn). |
| **new** | **`ord_n(p) = (n−1)/6` and `ord_n(2) = (n−1)/64`** | ⚠ **EXPLAINED 2026-07-24** — `RESULT_ord_n_residue_structure_v1.md` | Both dissolved, and both dissolutions are *scoped*. **`c₂=64`: selection effect** — `ν₂(n−1)=6`, so this is just "2 has odd order", and **5** of 168 primes `q<1000` do the same (`2,79,137,199,367`; expected 2.62). **`c_p=6`: a `1/6` draw** — H-sextic (CM forces it via Eisenstein reciprocity) **FALSIFIED**, cube rate `0.3349`, `z=+0.27`, control `0.3325`. Built en route, all `[PROVED]`: **(L3)** `3∣n−1` forced for prime-order `j=0` (4977/4977) — the derivation GLV rests on; **(L1)** `sf(\|t−1\|)∣6 ⇒ (p/n)=+1` forced when `n≡1 mod 24` (`1546/1546`, 0 violations); **(L2)** its density `∝p^{−1/4}`, so `≈10^{−19}` at secp — a **derived**, not extrapolated, null at `2²⁵⁶`. **Cubic analogue now DONE** → `RESULT_cubic_sextic_bridge_v1.md`: **(B1)** `χ₃(p mod n) = ω^{c₃}·χ₃(n mod p)`, `c₃` **closed form**, `[PROVED\|classical inputs]`, `12050/12050`, 8→256 bits; **(B4)** `c_p = 6 ⟺ n` sextic residue mod `p` (`150/150` at 256 bits + secp itself, where `c₃=0` and it degenerates to `p` sextic mod `n` ⟺ `n` sextic mod `p`). An **exact identity does not decay** — the one statement here that reaches `2²⁵⁶` intact. **`ℓ ≥ 5` now ANSWERED** → `RESULT_bridge_dichotomy_v1.md`: reduction `n ≡ p (mod \|t−1\|)` makes it classical; **(D1)** prime-order CM curves exist **iff `D ≡ 5 mod 8`** (2 inert) — `0` exceptions in `67,477` twists, and this is why 4 arms were empty (**blocker, not sampling**); **(D2)** `w=4` branch is **empty** (only `D=−4`, ramified); **(D3)** bridge present at `ℓ=3` **only** for `D=−3` (`ratio 1.69`, `p=1/20001`, power `16.1σ`), absent at `ℓ=5,7,11,13` (power `9.7/7.0/4.5/3.6σ`) and at `ℓ=3` for `D=−11,−19,−43,−67,−163` (power `≈16σ`) — **all negative controls clean, positive control hit its pre-committed effect size**. ⇒ **`D=−3` is the unique prime-order CM discriminant with a bridge past `ℓ=2`; secp sits on it** (a restatement of `j=0`, no security content). **Mechanism + constant + `h>1` now done** → `RESULT_bridge_mechanism_and_constant_v1.md`: **(M1)** matched control (same `Δ=n−p` multiset, power `27.5σ`) gives ratio `0.993` vs CM's `1.645` ⇒ the bridge is **CM-generated**, shape-generated association **bounded `<~1.06` at 3σ** (a BOUND, scoped to 30-bit `p`/this `Δ`/this statistic — *not* an absence); **(E1–E4)** exact laws, `0` violations/12000, collapsing the correction to **`c₃ ≡ s·(t−1)/3 (mod 3)`** — no character evaluation needed; **(M2)** dichotomy keyed to `w` **not** class number (ten `h=2` discriminants, ratios `0.96–1.02`, power `12.7–15.0σ`). ⚠ **The prereg's anti-fit guard FIRED:** `e(ν′)⊥e(π̄′)` is **FALSE**, so `P(c₃=0)=5/9` / ratio `5/3` are `[CONSISTENT, not verified]` — a passing number did not rescue a wrong model. **Still open:** ★ `citation-verifier` — **nothing claimed as new**; **`P(s=0)` runs low in both samples (`z=−1.92` combined)** — resample one twist per `p`; (E1–E4) are **post-hoc, same-sample** and owe an independent retest; the `+1` primarizing sign unexplained; the **uniform-correction blind spot** untouched; `h≥3`, `ℓ≥17` untested, `ℓ=11,13` weakly bounded; (B5)'s density under-powered; the L1 free cell **bounded** at `0.5` (`±0.015`), not proved. |
| **new (today)** | **N1's phase law: is `|sin θ₁ + sin θ₂| ≤ 1`?** | OPEN — this is exactly what `½` requires | Today's result reduced `|V(a)|` to `2√p·|sin θ₁ + sin θ₂|` (two real parameters). Current scope is **6 unforced cells** (`p=13,43`). Running `p = 61, 67, 79` takes it to ~40 cells. `p=61` is `1.4×10⁷` field elements at `k=4` — the binding cost. |
| **12** | **A discriminating signature for the CM layer `L3` (N3)** | OPEN, both designed tests failed | A real test must target the **CM type** (the embedding of `ℚ(ζ₁₂)` on the tangent space), **not** which field `L_new` splits over. Also: supersingular order sets `{1,3}` vs `{3,4}` need a larger sample before they are a law. |
| **—** | **`k = 8` cover** (genus 7, new dim 4) | unbuilt | The last member of the Kummer family never constructed. `8 ∤ p−1` at secp ⇒ same "character not over `F_p`" prior as `χ₄`/`χ₁₂`, **unverified**. |
| **—** | **The Kummer family's `p`-dependence** | untouched | `(★) S_d(c³b) = χ_d(c)³S_d(b)` bounds the **`b`**-dependence at `≤ log₂3`. **Supersingularity, the `m`-law, `p mod 12` are all untouched by it** — that is the open direction, and the conductor/volcano family is the one direction `(★)` does not bound (it varies the endomorphism lattice, not the curve constant). |
| **—** | **Is `ε` an arithmetic object?** (symbol / norm condition) | "also live" | And: does `ε` relate to the μ₃/μ₆ covers by **anything beyond sharing the argument `4b`**? Now sharper — the shared constant `28 = 4b` is **explained** and is *not* evidence of a relation. |
| **9** | **FLD-sign intrinsic-ness** | OPEN, carried verbatim | `sign(FLD) = −χ₂(M)` verified 54/54 but reduces to no tested intrinsic invariant. ⚠ **Do not run the `π_p↔π̄_p` chirality probe** — it is void (`X∈ℤ` is conjugation-fixed). Voiding a check is not closing the question. |
| **—** | **"Also live", lower stakes** | | Full-resolution `σ₁,σ₂` boundedness; large-prime rank-10 μ₃ split; a `p mod 8` law for `⟨σ,χ₃⟩` or `⟨ε,χ₂⟩`; deriving `H1` from the Cap Law's continuum geometry; the `λ₂` transfer eigenvector (~50% μ₃-covariant — **inherits the gauge question that dissolved `λ₃` and has not been separately re-run**). |
| **★** | **PRIORITY / LITERATURE SEARCH — never run** | overdue | `NEXT_DIRECTIONS_v1 §2` lists **10** claimed-original results (Cap Law, `H1`, `|FLD|=6h(−p)`, Claims S/F, `A_new` supersingularity, secp amicability, the `m` quantum number, three `U` conservations, bilinear closure, `k_den` Farey comb) — **unaudited against the literature**. This record's own history: **reading the source dissolved the obstacle four times.** `citation-verifier` exists for exactly this. |

## B. CURVE STRUCTURE THAT TOUCHES THE LEAKAGE QUESTION

| # | item | status |
|---|---|---|
| **17** | ⚠ **STALE AS WRITTEN — ALREADY RUN TWICE (2026-07-24), status ABSTAIN, not untouched.** See `RESULT_row_budget_lowtail_v1.md` and **`_v2.md`** (+ `PREREG_row_budget_lowtail_v1/v2`, `_DEVIATIONS`, `RESULT_row_budget_secondaries_S1_S6_v1/v2`, scripts `row_budget_*.py`). **v1 abstained on P-DET criterion 3; v2's repair FIXED that — criterion 3 now PASSES at every prime, as do 1, 2, 4 and the new `C-SELFZ`/`C-DISP` gates — but the arm abstains AGAIN on a DIFFERENT control, `P-DET-A` criterion 5 (P-SIZE), which the result itself records as "demonstrably mis-calibrated". Pre-registered Arm A3 also failed its slope band.** Forced checks clean (`C-EQ-int` exactly 0 at all 10 primes; `C-BUDGET` rel `≤1.2e−15`). **⇒ The genuine open work is NOT a re-design and NOT a re-run: it is to RECALIBRATE the P-SIZE control (and re-examine A3's slope band), then re-issue the verdict.** The underlying question (is the near-zero excess a shadow of `Σ_a\|U\|²=n(n−1)`?) remains **undecided — abstained, not closed**. ⚠ Do **not** re-run `M4` (4th moment blind to the low tail); must **not** be a re-basing. |
| **18** | **The `(b,c)`-locus of the sub-Rayleigh deficit and its equivariance** under the exact `(a,b) ↦ (λa, βb)` action (available as an exact partition, `1e−12`). Distinct from every statistic frozen so far. |
| **1 / §XI.1** | **A cheap partial of the joint `(x,y)` shadow** — *Part 0's primary target.* Two new **explicit exclusions**: non-unitary/**oblique** transforms, and **higher-degree (non-linear)** readouts. Still open: the **non-μ₆-covariant cheap readouts** (raw coordinate bits — `x mod 2`, high bits of `x`) which live outside the μ₆ decomposition and are bounded **on one curve at one `n` only**; multi-bit and multi-point joint readouts; sub-floor `φ`; larger `p`. |
| **3 / §XI.3** | **The non-homomorphic amicable correspondence.** Only the group-homomorphism case is ruled out (`Hom = 0`, coprime orders). **Today's ARM 4 gave it its first parity-legal measurement** — a bound at `0.5%` copy-fraction, sextant quantisation. **Named next: finer than 6 cells; the `xy` readout (proved odd in `d`, and the object behind the `(X·Y) mod 64 → D mod 64` shadow); `K = 4×10⁶`.** |
| **7** | **Two-point / joint-SET bilinear.** Diagonal `v = k·u` is KS-covered at fixed `k`. **Open: `k` growing with `p`; genuinely joint multi-key readouts of the SET `{x([dᵢ]G)}`; the full two-point panel beyond Theorem B.** |
| **25** | **Two untouched hunts**, named at the close of the λ₃ drill and addressed by nothing since: the **`ε` carry-trajectory**, and the **≥3-key / amicable joint-SET** object. |
| **4** | **`S₄⁺` / first-fall degree.** Re-graded `[HEURISTIC+CITED]`. Open: `m ≥ 5`, larger `p`, **non-Semaev index calculus**. |
| **13** | **Cover transfer into `Jac(C)` — Route 3 (N4).** `Õ(p^{4/3})` is the cost of the best *known* genus-3 algorithms on *one* cover, not a proof over the cover family. Also open: **D2** (Lang-torsor twist bridge), and a non-affine but efficiently invertible `ℓ`. |
| **14** | **Growing-degree corner of the character-sum bounds (N5)** `[GAP]` — the KS constant grows with readout degree; no reduction in hand for general poly-time readouts. |
| **19** | **Curve-side image of the `T=1` Dirichlet island lattice** beyond the tested families: other Farey labels, larger `M`, higher-order joint statistics, and the d-side↔curve-side question across the now-verified amicable bridge. |
| **20** | **μ₆-matched feature/target pairs at `n > 5·10⁴`** — the LBE grid is symmetry-mismatched by construction. Needs its own pre-registration. |
| **22** | **The `T=2` stratum, and whether `T=3` ever opens.** Is there a nested reciprocal lattice `⌊lo/q₁⌋ ± ⌊lo/q₂⌋` inside `T ≤ 2`? `max T = 2` is verified only to `7×10⁵`. |
| **24** | **A per-`n`-density null for the `(n,k)` coprimality net**, and *which* cycles carry the `~3×` β₁ excess — organised by Stern–Brocot depth / the continued-fraction tree? A **location** test, not a count. |

## C. UNFINISHED FROM TODAY

- **Spec `ARM 2`** — `T₂ = ‖ΠDΠ‖_F²`, hashed calibration, 9 primary + 6 holdout of the frozen 37
  curves. The properly-designed version of the `C_T` question; **the exploratory ARM A2 is not it**.
- **Spec `ARM 3`** — exact-vanishing census at composite order. ⚠ **DC5 forbids any transfer to secp
  whatever the outcome** (at prime modulus a full-orbit character sum cannot vanish exactly unless the
  readout is constant).
- **`C_T`, the record's own next step (#6):** `‖D_odd‖_F` at `n ~ 10⁶–10⁷`, **varying generator and
  prime**. Today's finding sharpens the caution: the AP-complete estimator is **dependence-dominated**,
  so its floor must be measured before it is used for any bound.

## D. GLOBAL CAVEATS THAT BOUND EVERY ITEM ABOVE

- **#5 — the banner.** *Everything at secp's actual `p`.* No measurement at `p ≈ 10⁵` has power against
  a structure at `2²⁵⁶`: **~239 binary orders of magnitude**, governing every `[VERIFIED]`/`[EMPIRICAL]`
  conclusion in the record. ARM 4 and the `m`-law/`μ₆`-cover derivations are the exceptions that
  actually reach scale.
- **#21 — ABSTAINED, not closed.** Diffuse family-wise dependence in the LBE grid: the empirical rank
  cannot resolve below `~5e−3` and so cannot test the family-wise level `1e−5`. Next step is **more
  null draws, not re-analysis of existing data.**
- **#23 — unresolved, not degenerate.** Individual slow-mode eigenvectors of the walk operator need
  `n ~ 10⁵–10⁶` by the measured `n ∝ 1/gap²` scaling — at or beyond accessible prime-order range.
- **#2, #11 — resolved, listed so they are not re-run:** the odd-half/`T_y` max bound (KS), and `N2`
  (`A_new` supersingular at secp, `[PROVED]` §A1.1). ⚠ `N2` carries one attached caveat: **independent
  adversarial re-derivation of its two standard external inputs is still outstanding.**
