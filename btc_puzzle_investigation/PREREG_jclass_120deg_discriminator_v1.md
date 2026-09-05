# PREREG — does the 120° lock track the curve's automorphism group? (j-class discriminator, v1)

**Date:** 2026-07-31. **Status: SPEC ONLY — no data touched, no `V` computed on any non-`j=0` curve.**
**Executes nothing until the `experiment-designer` gate returns.**

---

## 0. Why this test exists (the hypothesis under test, stated as a hypothesis)

`RESULT_n1_120deg_exact_v1.md` establishes `[PROVED-exact]` that
`g(p,a) = deg gcd(L*(T), L*(ζ₃T)) = 2` at every surviving cell of 22 primes (2464 cells), for
`E: y² = x³ + 7`. The eigenvalue multiset is `{α, ζ₃α, −ᾱ, −ζ̄₃ᾱ}`.

A **mechanism hypothesis** (2026-07-31, unreviewed, NOT a result) proposes that this shape is the
eigenvalue shadow of a decomposition `H¹ ≅ W_a ⊕ (W_a ⊗ ξ)`, `ξ` the unramified cubic character,
with the `ζ₃` originating in the curve's CM / automorphism structure (`μ₆ = Aut(E)`,
`ℚ(ζ₁₂) ⊂ End⁰(A_new)`).

**Two things this spec explicitly does NOT assume.**
1. **Eigenvalue shape ≠ sheaf decomposition.** A multiset of the form `W ⊔ ζ₃W` is compatible with a
   non-split extension. This test does **not** test the decomposition. It tests a **necessary
   condition** of the mechanism.
2. **The `End⁰` route is not derived.** Over `F_p`, `ℚ(ζ₁₂) ⊂ End⁰` is commutative and commutes with
   Frobenius — that gives the standard CM splitting, *not* an eigenvalue twist. Whether Frobenius
   conjugation over `F_{p³}` produces the `ζ₃` factor is unproven and is **not** presupposed here.

**What is actually tested:** whether the lock is present on curves whose automorphism group does not
contain `μ₃`. That is a clean yes/no, and it is a necessary condition for *any* mechanism that routes
the `ζ₃` through `Aut(E)` / CM by `ℤ[ω]`.

## 0a. Why the `a=0` anchor is NOT the test (recorded, so it is not re-proposed)

`RESULT_120deg_anchor_from_mlaw_v1.md` §4a: at `p ≡ 11 mod 12` the anchor has `m = 2`, root orders
`[4,4,4,4]`, hence `g = 0` — while `RESULT_n1_120deg_exact_v1.md` D4 records that **every `a≠0` cell
at those same primes has `g = 2`**. The lock at `a≠0` is therefore *not* inherited from the anchor,
and an anchor-level cross-`j` table would measure an object the law does not live on. The
discriminator must be at `a≠0`. **Cost of this decision:** the run needs the `O(p²)` `hist_k2` pass
and a dlog table, i.e. the existing census pipeline, not a closed form.

---

## 1. Object (FROZEN)

For a curve `E_{A,B}: y² = x³ + Ax + B` over `F_p` with `p ≡ 3 mod 4` and `n = #E(F_p)` **prime**:

- `c(d) = χ₂(y_{[d]G})`, `V_k(a) = Σ_{P∈E(F_{p^k})} χ₂(y_P)·e_n(a·d_P)` for `k = 1, 2`
  (exactly the record's `hist_k1` / `hist_k2` objects, unchanged).
- `e₁ = −V₁`, `e₂ = (V₁² + V₂)/2`, `e₃ = χ₂(−1)·p·e₁`, `e₄ = p²`;
  `L*(T) = T⁴ − e₁T³ + e₂T² − e₃T + e₄`.
- **Primary statistic:** `g_k(p, A, B, a) = deg gcd(L*(T), L*(ζ_k T))`, computed **multi-modularly**
  over 5 primes `l ≡ 1 mod (k·n)` (reduction only raises gcd degree ⇒ true `g` = min over `l`).
  Computed for `k ∈ {3, 4, 6}`. `k=3` is the record's statistic, unchanged.

**Justification that the reconstruction transfers off `j=0`:** `e₃`, `e₄` follow from purity plus the
closure `α ↦ −ᾱ`, which follow from `χ₂(−1) = −1` at `p ≡ 3 mod 4` and the functional equation;
`dim H¹_c = 4` follows from `C: w⁴ = f(x)` having genus 3 for any separable cubic `f`, with
`dim Jac(E) = 1`. **None of these uses `j = 0`** (`RESULT_anew_identification_v1.md` §1 derives
`b₁ = 0` from the `μ₄` argument, which needs only `p ≡ 3 mod 4`).

**Cells.** For `j = 0`, `V` is `μ₃`-invariant and odd ⇒ cells are the `(n−1)/6` cosets of `μ₆`
(unchanged from the record's freeze). **For `j ≠ 0` there is no `λ`**, so `V` is only odd ⇒ cells are
the `(n−1)/2` cosets of `μ₂`. This is a required change, not a deviation: using `μ₆` cells off `j=0`
would presuppose an invariance that does not hold. Class rep = least positive residue.

## 2. Arms (pre-committed; curve selection rule is deterministic and data-blind)

| arm | curve family | `Aut(Ē)` | selection rule |
|---|---|---|---|
| **J0** | `y² = x³ + B` | `μ₆` | least `B ∈ [1,p)` with `n` prime, then next 2 |
| **J1728** | `y² = x³ + Ax` | `μ₄` | least `A ∈ [1,p)` with `n` prime, then next 2 |
| **JGEN** | `y² = x³ + Ax + B` | `μ₂` | least `(A,B)` in lex order with `j ∉ {0,1728}` and `n` prime, then next 2 |

**Primes (FROZEN, data-blind):** all `p ≡ 3 mod 4` with `60 < p < 400`. Both residue classes mod 12
are included deliberately (the D4 correction shows the law is not stratum-specific at `a≠0`).
Budget: 900 s/prime/arm, ABSTAIN-and-do-not-substitute on overrun.

## 3. ★ PRE-COMMITTED PREDICTION (written before any non-`j=0` `V` is computed)

| arm | `g₃` at `a≠0` cells | `g₄` | `g₆` |
|---|---|---|---|
| **J0** | **2 at every surviving cell** (reproduction of the record) | 0 | 2 |
| **J1728** | **0 at (essentially) every cell** | **2 at every surviving cell** | 0 |
| **JGEN** | **0** | **0** | **0** |

The `J1728` `g₄` row is the **positive** prediction and is the informative one: the mechanism says
the lock is `Aut`-driven, so a `μ₄` curve should show a `ζ₄` (90°) lock where the `μ₆` curve shows a
`ζ₃` (120°) one. A test that only predicted nulls off `j=0` would be much weaker.

*(`g₆ = 2` on J0 is expected as a near-corollary of `g₃ = 2` given the `α↦−ᾱ` closure and is reported
as a consistency readout, not as independent evidence.)*

## 4. FALSIFICATION (pre-committed, in order of consequence)

- **F-A — mechanism REFUTED.** `JGEN` shows `g₃ = 2` at a substantial rate. The `ζ₃` is then not an
  automorphism/CM phenomenon at all, and a considerably larger question opens (what forces it on a
  curve with `Aut = μ₂`?). **This outcome is the most interesting one available and must be reported
  as a positive finding, not as a failed prediction.**
- **F-B — mechanism REFUTED in its `μ₃`-specific form.** `J1728` shows `g₃ = 2`. The `ζ₃` is then not
  tied to `μ₃ ⊂ Aut`.
- **F-C — mechanism SURVIVES but is not `Aut`-shaped.** `J1728` shows `g₃ = 0` **and** `g₄ = 0`
  (no lock of any order). The lock is then `μ₃`-specific rather than "the automorphism group acts",
  which weakens the `W ⊗ R` reading (it predicts a lock, not its absence).
- **F-D — prediction confirmed.** The §3 table holds. This is a **necessary condition met**, and
  explicitly **not** evidence for the decomposition (see §0). It licenses the `a≠0` uniformity
  programme (small-cofactor route) and nothing else.

## 5. Controls (all must fire before any arm's numbers are read)

- **C-PLANT** — the existing `plant_check()` of `run_n1_120deg_v1.py`, unchanged, extended to `k=4,6`:
  synthetic quartics with roots planted at ratio `ζ_k` (want `g_k=2`) and at generic ratios
  (want `g_k=0`), through the **same** `deg_gcd` routine. **If any plant misses, HALT.**
- **C-REPRO** — arm J0 at `p ∈ {67, 79, 127, 163}` must reproduce `RESULT_n1_120deg_exact_v1.json`
  cell-for-cell. This is the instrument check: a pipeline that does not reproduce the known answer on
  the known curve says nothing about a new one. **If it misses, HALT.**
- **C-ORDER** — `ζ_k` used in the multi-modular embedding must have **exact** order `k` in `F_l`
  (asserted per `l`, per `k`). The existing `primitive_root_of_order` assumes `k` prime and is
  **wrong for `k ∈ {4,6}`**; it must be replaced, and the replacement asserted.
- **C-CELL** — cell count assertion per arm (`(n−1)/6` for J0, `(n−1)/2` off `j=0`), and an explicit
  check that `V(λa) = V(a)` **holds** on J0 and **fails** on JGEN. A `μ₃` invariance silently holding
  off `j=0` would mean the curve was mis-specified.
- **C-EXACT** — `check_no_float.py` on the run script; signal path is `int` / modular only.

## 6. Scope — what a confirmed §3 table would and would not license

**Would:** the statement that the `ζ₃` lock at `a≠0` is present on `μ₆` curves and absent on `μ₂`
curves, over `p ∈ (60,400)`, `p ≡ 3 mod 4`, 3 curves per arm, at every surviving cell —
`[EMPIRICAL — exact, scoped]`.

**Would NOT:** (i) any statement about the *decomposition* `H¹ ≅ W ⊕ W⊗ξ`, which is untested by any
eigenvalue-level statistic (§0.1); (ii) uniformity in `a` at secp's `p` — this is `p < 400`;
(iii) any leakage or ECDLP consequence; (iv) promotion of the mechanism hypothesis above
`[CONJECTURAL]`. A necessary condition met is not a mechanism.

## 7. Deviations register

Any change to §1–§5 after this file is frozen is logged in
`PREREG_jclass_120deg_discriminator_v1_DEVIATIONS.md` with the reason, before the affected number is
read. Freeze = SHA-256 of this file, printed by the run script and recorded in the RESULT.
