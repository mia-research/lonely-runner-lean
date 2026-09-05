# PREREG — Individual Isotypic Faction Projection (LBE / D1-lift eigenspace residues)

**File:** `PREREG_isotypic_faction_projection_v1.md`  **Date:** 2026-07-20  **Status:** PRE-RUN. No residue-vs-predicate correlation has been computed. No arm scored.

**Scope, up front.** Enumerable model curves `E : y^2 = x^3 + 7` over small `F_p` (`p ≡ 1 mod 6`, prime group order `n`, up to a few thousand). On the model the A_new discrete log is easy because `A_new` is small; **that is exactly what is unavailable at secp**, where enumerating all `d` is impossible. **Nothing in this run transfers to `p = 2^256 − 2^32 − 977`.**

---

## 0. TWO PREMISES CARRIED AT THEIR REAL GRADE (not baked into the setup)

- **P0a — the `m=1` clockwork is [EMPIRICAL], not analytic.** The law `p ≡ 7 mod 12 ⇒ m = 1 unless B is a cubic residue` is validated on ~26 primes below 500 and on record as *not reaching secp* (the scale-free upgrade — the closed-form Jacobi sum for `S = Σχ₄(x³+B)` — is open). On the model we therefore **compute `m` per prime** (via `mu4_eigenvalue_individual_v1.py`) and *select* the `m=1` curves to test the `m=1` instrument; `m=1` is never assumed for a row. secp's mode stays an empirical extrapolation with stated scope.
- **P0b — the "0.93/0.94 alignment" is NOT a target.** The char-vs-random control flattened its *scalar magnitude* (0.999 vs 0.999): the number is the coordinate geometry's phase-only reconstruction quality, not shown to carry `d`. What IS established structure is the **even/odd d-parity** (`x_{−d}=x_d`, `y_{−d}=−y_d`; cross-orthogonality ≤1e-15) `[PROVED]`. The success target of this run is **not** "capture a fraction of 0.94 / escape a 0.47 floor" — that optimizes toward an unseparated magnitude. The target is the distribution/subspace of the residues against a strong null (§3).

---

## 1. OBJECT

Cover `C : w^4 = x^3 + 7`, `Jac(C) ~ E × A_new`, `dim A_new = 2`; `A_new` supersingular at `p ≡ 3 mod 4` (`secp_N2_supersingular_closed`). For `P = [d]G` on `E`:

- **D1 lift (non-homomorphic):** `Q(P) = [P^+] − [P^-]` in `Jac(C)`, `P^± = (x_P, ±w)`, `w^2 = y_P`. Rational only when `y_P` is a QR mod `p` ("liftable `d`"); restrict to liftable `d` (≈ half). Built exactly by `d1_supersingular_lift_v3.Qdiv`.
- **A_new residue:** `ℓ(d) = dlog_{A_new}(Q([d]G))`, computable (easy A_new dlog), an element of the structured `A_new` group.
- **Isotypic factions:** the four 1-dim Frobenius eigenspaces with eigenvalues `√p·{ζ_12, ζ_12^5, ζ_12^{-1}, ζ_12^{-5}}` (the `m=1` `z^4 − z^2 + 1` roots). `M_j` = eigenprojection (public, from `p mod 12` + eigendata). **Faction residue** `V_j(P) = M_j · Q(P)` (equivalently the eigencomponent of `ℓ(d)`).

---

## 2. FORCED / ANCHOR FACTS — contribute ZERO evidence

- **A1 — affine handle absent `[PROVED]`.** `ℓ(d)` is not affine in `d`: `0/666` additivity, `0/339` affine triples, controls fired (`RESULT_D1_lift_affine_test_v1.md`). This run does **not** re-seek an affine transfer; it asks a *different* question (non-affine rank association). A1 is the anchor, not a target. Reproduce it once as a baseline (`best_affine` → non-affine) to confirm the pipeline.
- **A2 — even/odd d-parity `[PROVED]`** (§0 P0b). Used as a readout check on how `V_j` transforms under `P → −P`; forced, zero evidence.
- **A3 — torsion/rationality readouts.** liftable-`d` fraction; `2Q ~ 0`, `3Q ~ 0` structure; `Σ_j V_j` reconstructs `ℓ(d)`. Forced checks; fire by holding.
- **A4 — supersingular rigidity** (`√p·ζ` exactness) is a property of `Frob` on `A_new`, i.e. of the zeta function, not of any single scalar `d`. It constrains the eigenvalues `V_j` can take, not their `d`-dependence. Forced.

---

## 3. STATISTICS (frozen)

Liftable `d` only. All primary decisions are rank/permutation (float carve-out §7).

### ARM A — characterization (NO pass/fail): how non-affine, and where the residue mass sits
- **Non-affinity magnitude** of `ℓ(d)`: the residual-rank / second-difference profile of the best affine fit (a bounded structure, per `feedback_negative_bias_enlarge_nulls` `0/666` is a magnitude, not "nothing"). Report the distribution, not a verdict.
- **Faction mass:** for each eigenspace `j`, the distribution of `|V_j(P_d)|` (or the discrete-order profile of the residue) across liftable `d`, and its parity content (A2). Reported as bounded magnitude with power + scope.

### ARM B — the leakage test: does a faction residue carry a predicate of `d`?
- **Feature:** `f_j(d) := V_j(P_d)` — computed from the point `P_d` only (tautology guard §4).
- **Targets (pre-committed):** `π(d) ∈ { LSB(d), d mod 3 }`. No other predicate is added post hoc.
- **Statistic:** rank association `S_j` between `f_j` and `π` (Spearman for ordered residues; mutual information for the discrete/mod-3 case), over liftable `d`.
- **STRONG matched null (the load-bearing fix).** Not `{d, n−d}`. Apply the group automorphism `φ_s : P ↦ [s]P`, `s ∈ (Z/n)^*` random. The point-set geometry is **preserved**; only the `d`↔geometry labeling is scrambled. Null value `= S_j` recomputed with `π` relabeled by `π(s^{-1}·)`; null distribution over `R ≥ 500` random `s`. Report the true (`s=1`) `S_j`'s two-sided rank in that null (empirical p-value; no threshold pre-set — the number is the output). `{d, n−d}` is the single `s = −1` member, recorded as a **forced-symmetry readout only**, never the evidential null.
- **Why this null does not destroy artifact and signal identically** (`feedback_residue_vs_component_tautology`): a *geometric* artifact rides along with `[s]P` and is therefore *reproduced* by every null draw, so it cannot masquerade as extreme; only a `d`-labeling-specific association survives as extreme. The failed `r=v−w` shuffle broke both identically; this one preserves the geometry and breaks only the labeling.

### ARM C — D2 Lang-torsor twist (pre-registered comparison, secondary)
Apply the Lang-torsor character twist to the lift and recompute Arm A's **affinity/invertibility** statistic on the twisted `ℓ`. Report as a bounded comparison `twisted vs D1` (does the twist increase affine capturability, and by how much) — a magnitude, not a claim about "opening a gate."

---

## 4. TAUTOLOGY GUARD (code-level, load-bearing)

`V_j` is defined via `M_j` (which depends on the target-matched eigenvalue) — so the feature must be a function of the **point** alone, never of `d`.
- `f_j` is implemented with signature **exactly** `f_j(xP, yP, p, eigendata_j)`; via `inspect.signature` the run asserts its argument set ⊆ `{xP, yP, p, eigendata_j}` and contains **no** `d`, `xs`, `ys`, or any `d`-indexed array. A violation aborts the run.
- The enumeration computes `P_d = [d]G`, then passes **only** `P_d`'s coordinates to `f_j`. `d` never enters the feature path.

---

## 5. CONTROLS (all must fire; no verdict if any fails)

- **C1 — planted positive (Arm B MUST detect).** Synthetic feature `g(d) = LSB(d) ⊕ (low-rate noise)` injected as a faction: Arm B's `S` must be extreme vs the strong null. **If C1 does not fire, no result is reported.**
- **C2 — label-independent negative.** A per-point random value (fixed by point, independent of true `d`-labeling): must land in-band vs the strong null. Confirms the null does not manufacture extremes.
- **C3 — affine-baseline.** Reproduce A1 (`best_affine` → non-affine, `0/666`-class) on ≥2 primes: confirms pipeline.
- **C4 — readouts (A2/A3, forced).** parity transform of `V_j`; liftable fraction; `Σ_j V_j = ℓ(d)` to machine/exact tolerance; `{d,n−d}` (`s=−1`) behavior printed as forced.

---

## 6. POWER & SCOPE

- Primes `p ≡ 1 mod 6`, prime `n`, model set e.g. `{163, 211, 349, 433, 577, 1009, 2011, ~6000}` as compute allows; **`m` computed per prime, `m=1` curves selected**. Liftable `d` ≈ `(n−1)/2`.
- **Arm B power:** with `R ≥ 500` null draws, p-value resolution ≤ `1/501 ≈ 0.002`; smallest detectable rank association ≈ the strong-null spread at the liftable sample size (report the measured spread, so the detectable step is printed, not assumed).
- **Arm A / C:** report the non-affinity/affinity magnitude with its sampling spread.
- **Scope (restated):** model-only; A_new dlog easy only because A_new is small here; `2^256` enumeration impossible; no transfer.

---

## 7. FLOAT / EXACTNESS CARVE-OUT

Divisor/Jacobian arithmetic (`d1_supersingular_lift_v3`, Sage exact classes) and group arithmetic are **exact**. Float appears only in eigenprojection magnitudes/phases. No pass/fail is decided by float: all Arm-B/C decisions are rank/permutation; the only float thresholds are the A3 reconstruction/readout tolerances (validations, not evidence).

---

## 8. PRE-COMMITTED OUTCOME TABLE (no dismissal language)

| Case (from printed output) | Reported as |
|---|---|
| C1/C3 fire; Arm B: some faction `j` extreme vs the **strong** null | "Eigenspace `j`'s residue carries a rank-detectable, non-affine association with `π(d)` on these model primes: magnitude `X`, power `Y`, scope model-only. Next probe: stability across `p` / the D2 twist. Not a transfer to `2^256`." |
| Arm B: extreme vs `{d,n−d}` (weak) but **in-band vs strong** null | "The apparent association is reproduced by geometry-preserving relabeling — a bounded property of the point geometry in this basis, magnitude `X`, not `d`-specific. This is a flat statistic in the tested basis, **not** an absence of structure; finer bases, other predicates, and the D2 twist are untested and out of scope." |
| Arm B: in-band everywhere vs the strong null | "No faction residue shows rank association with `π(d)` above the strong-null floor on these primes (power `Y`). Conditional null bound to method + sample + floor; does not exclude non-affine associations below floor, other predicates, larger `p`, or the D2 twist." |
| Arm A (always) | non-affinity magnitude of `ℓ(d)` + faction-mass/parity profile, as bounded characterization. |
| Arm C (always) | twisted-vs-D1 affinity magnitude, as a bounded comparison. |
| C1 does not fire | **No result reported.** Debug detector; re-run. |

---

## 9. OUTPUT TYPE (pre-committed)

A **bounded characterization** anchored on the `[PROVED]` affine-handle-absent fact (A1) and the even/odd parity (A2). Never a verdict about ECDLP, extraction, security, or a "gate" open/closed. Nulls are conditional (method + sample + floor). The non-affinity is a magnitude/structure (the object the D2 bridge targets), not "nothing"; a flat residue statistic is a bounded magnitude in the tested basis, not "no leak."

---

## Files this run will produce
- `isotypic_faction_projection_v1.py` (reuses `d1_supersingular_lift_v3.Qdiv/dlog`, `mu4_eigenvalue_individual_v1` for `m` + eigendata; ≤ ~300 lines).
- `isotypic_faction_projection_v1.log` — every §8 row decidable from it.
- `RESULT_isotypic_faction_projection_v1.md` — characterization + bounds.
- `PREREG_isotypic_faction_projection_v1_DEVIATIONS.md` — any departure.
