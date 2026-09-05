# PREREG v2 — Brick E: minimal polynomial degree of `c⁺(d) = dlog_{A_new(F_p)}(S([d]G))`

**Grade slot: `[PRE-REGISTERED — frame-gate CLEARED, R2]`.** Supersedes v1 (`71c2a985…`), which two
isolated `experiment-designer` passes found inadequate (`PREREG_brick_e_cd_degree_v1_GATE_REVIEW.md` R1,
`PREREG_brick_e_cd_degree_v2_GATE_REVIEW.md` R2). R2 **adjudicated the design on the merits and cleared
it**: the QR-half scalar arm with a μ₃-matched null resolves both R1 frame defects (F1 null-mismatch, F2
ill-posedness). This spec folds in R2's design (a–e) and its scope fix. The real `c⁺(d)`-vs-`d` run is
**unblocked** once this file is frozen (SHA below). No leakage/ECDLP/key-recovery claim. Exact integer /
finite-field arithmetic only; no float in any signal-path step.

---

## 0. Object (corrected)

`E : y² = x³+7` over `F_p`, **`p ≡ 7 mod 12` AND `n=#E(F_p)` prime with `6 ∣ (n−1)`** — the second
clause is NOT implied by the first (v1's §0 error: `n` is composite at `p=331,307,367,…`; each rung is
individually verified, §6). GLV `φ_GLV:(x,y)↦(βx,y)=[λ]`, `λ` order 3 in `(Z/n)*`. Cover `C:w⁴=x³+7`,
genus 3, `Jac(C)~E×A_new`, `A_new` 2-dim **supersingular** at `p≡3 mod4` (Prong 1, `RESULT_anew_…_v3`).
`ζ₄:(x,w)↦(x,iw)` induces `ρ∈End(A_new)`, `ρ²=[−1]`; `ζ₄²`=deck of `C→E`. Isotypic projection
`S(P)=Q₀+β²Q₁+βQ₂` (`Qⱼ=lift(φ_GLV^j P)`), the `ζ₃`-eigenvector; `σ(S)=[κ]S`, `κ=1849`, `κ³≡1 mod 1893`
at `p=43` (verified, `lbe_dlog.sage`).

**Structural grounding (`brick_e_anew_Lpoly_v1.sage`, cross-checks `|Jac(F_43)|=58683`):**
`|A_new(F_p)|=1893=3·631`, `|A_new(F_{p²})|=3²·631²`. **√−1 exists mod no divisor** (3,631 both `≡3 mod4`)
⇒ `ρ` is not scalar on any cyclic subgroup — the full group is genuinely 2-dim. But `φ(−P)=ρ·φ(P)`
universally and (`−1` a non-residue) exactly one of `±P` lifts rationally, so **the non-QR half equals
`ρ·(QR half)`** — no independent content. This is the empirical warrant for the domain restriction.

## 1. The two gate defects and their resolution (R2, on the merits)

- **F1 (null omitted the `ζ₄`/`ρ` symmetry).** Resolved by the DOMAIN, not by enlarging the null: the
  QR-half is a union of full `μ₃`-orbits and has **no `±d` pairs** (`d,−d` never both QR), so the `ζ₄`
  relation is intrinsically cross-domain and does not close in-domain. Three grounds (R2 §F1): only `μ₃`
  preserves QR-status; the intertwiner word `(ρσ)^6=[−1]≠id` vs `(−λ)^6=id`; `ρ²`=deck=`id` on `E`
  forces no cross-orbit relation. **⇒ the `μ₃`-null is matched and unbiased on the QR-half.**
- **F2 (single-scalar `c` ill-posed on the full group).** Resolved: on the QR-half `φ(P)∈A_new(F_p)=
  ⟨S(G)⟩` cyclic order 1893, so `c⁺(d)∈Z/1893` is a genuine scalar.

## 2. (a) Domain — QR-half scalar arm

`Q := {d∈[1,n) : y_{[d]G} is a QR mod p}`; statistic `c⁺(d)=dlog_{S(G)}(S([d]G)) ∈ Z/|A_new(F_p)|`.
**Freeze the `√y_P` sign rule:** the square root in `[1,(p−1)/2]` (deterministic; `μ₃`-consistent since
`λ` fixes `y`). The full-group `F_{p²}` readout is kept ONLY as structural control (d-iv); the v1
"two arms agree on D" cross-check is DROPPED (structurally different objects).

## 3. (b) Null — μ₃-matched — and (Q3) the degree statistic

Draw `c'⁺` uniform on ONE representative per `μ₃`-orbit of `Q` (`(n−1)/6` reps); propagate by
`c'⁺(λd)=κ·c'⁺(d)`, `κ` the GLOBAL cube-root eigenvalue (verify `κ³≡1`, `κ≠1`, and globality on the
instrument). No other constraint. **≥2000 draws.** Real and null use the **same** domain `Q` (no
selection bias). Degree read per CRT factor (DEVIATIONS D1): headline `D = max` over the LARGE prime
factor(s) of `|A_new(F_p)|` (631 at p=43, where the `Q`-values are distinct); the small factor (3) is a
consistency flag, not a degree. Fitter = `brick_e_degree_fitter_v1.py` (exact, unit-tested).

## 4. (c) Low-D threshold = null-histogram percentile

Compute the μ₃-null `D`-histogram (per large factor, over `Q`). Declare **"low D"** iff
`D_obs ≤` null 1st-percentile (`π≤0.01`) **AND** `INV` (the degree-`D` fit inverts uniquely for `d∈Q`
given `c⁺(target)`). The absolute `D≤N/3` gate is DROPPED (uncalibrated for few free values).

## 5. (d) Firing controls — four; ALL must fire before the real read

- **(i) Engine** (v1): planted `c*(d)=a₂d²+a₀ → D=2`, inversion recovers `d`. *(done — `brick_e_degree_fitter_v1.py`.)*
- **(ii) Pipeline**: plant a μ₃-COVARIANT low-degree `c` (`c(d)=a·d^{i₀}` with `λ^{i₀}=κ`) and route
  through the FULL null+π pipeline; require `π≤0.01` to FIRE. Exercises the permutation path (i) skips.
- **(iii) Calibration**: draw `c⁺` FROM the μ₃-null; require `π ≈ Uniform[0,1]` — proves the p-value is
  calibrated (empirical guard against the F1 failure mode).
- **(iv) Structural (ρ-identity)**: for each non-QR `d`, compute `φ([d]G)` in `A_new(F_{p²})` and,
  independently, `ρ·φ([−d]G)` (`−d∈Q`); assert EXACT equality. Verifies the `F_{p²}`/`ρ` instrument and
  that the non-QR half carries no independent content. CAN fail ⇒ genuine control. Requires the explicit
  order-4 `ζ₄` endomorphism `ρ` on the instrument.

If any control fails ⇒ **VOID the rung, do not read the real arm** (the forced-zero-control lesson,
`VOID_anew_cartier_c4_…`).

## 6. (e) Ladder, per-rung power, falsification

`#free values per rung = (n−1)/6` (μ₃-orbit reps). **Verified admissible rungs** (`p≡7 mod12`, `n` prime,
`6∣n−1`):

| p | 43 | 67 | 79 | 163 | 211 | 547 |
|---|---|---|---|---|---|---|
| `n=#E` | 31 | 79 | 67 | 139 | 199 | 547 |
| μ₃-reps | 5 | 13 | 11 | 23 | 33 | 91 |

**`p=331` DROPPED** (`#E=364=4·7·13` composite, `3∤n−1`, μ₃ undefined; also fails 307/367/379/439).
**Power:** `p=43` (5 reps) = **LEAD only** (a low-degree fit to 5 values is unsurprising; broad null
histogram). Single-rung power begins at `p≥163` (reps≥23). The **powered claim is degree-STABILITY**
across reps `{5,13,11,23,33,91}`. **Null-independent falsification arms (decisive regardless of the
null):** `D_obs ≥ max` over null draws (no reduction), OR `D` not stable across the ladder ⇒ hypothesis
refuted and `D_obs` is the cover-scramble degree bound.

## 7. Outcome grades, freeze, owed

| outcome | grade |
|---|---|
| low `D` (`π≤0.01` + INV) stable across ladder | `[EMPIRICAL — form-level, model scale]`; secp transfer separately gated (needs Prong-1 N2 ✓ + `A_new` `k=3` DLP cost) |
| high `D` / not stable | `[VERIFIED-scope — degree ≥ D₀ bound]` |

- **Freeze:** SHA-256 in `PREREG_brick_e_cd_degree_v2.md.sha256`; the run script echoes the hash before
  reading the real arm.
- **Deviations:** append to `PREREG_brick_e_cd_degree_v1_DEVIATIONS.md` (D1 carries over) or a v2
  deviations file; never edit this file.
- **Owed:** `compile-diff` before any master/handover promotion. Prong-1 gates are discharged.
- **Frame gate: CLEARED** (R2) — the real run is authorised on this frozen spec.

*Enabler: `RESULT_anew_…_v3.md` (Prong 1, both caveats resolved). Authority: `..._v1_GATE_REVIEW.md`,
`..._v2_GATE_REVIEW.md`. Engine: `brick_e_degree_fitter_v1.py`. Instrument: `lbe_dlog.sage` (p=43),
to be generalized to the ladder.*
