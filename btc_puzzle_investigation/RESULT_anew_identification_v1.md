# RESULT — the `A_new` identification, closing the residual of the (★) review

*2026-07-30. Closes the one item `RESULT_star_adversarial_review_v1.md` §2 left open: tying the
`χ₄`-isotypic factor of `Jac(C)`, `C : w⁴ = f(x)`, to **"the new part complementary to `E`"** — the
project's definition of `A_new` (`RESULT_mu4_eigenvalue_individual_v1.md:6`,
`POSITIVE_FINDINGS_ADDENDUM_1_v1.md:64`). Scripts `test_anew_identification_v1.py` (+ `.log`) and
`test_anew_identification_controls_v1.py` (+ `.log`). Exact integers only; `F_{p²} = F_p[t]/(t²+1)` as
integer pairs, `χ₄(x) = x^{(q−1)/4}` evaluated **in the field** and recorded as an exponent in `ℤ/4` — no
discrete log, no float. No leakage or ECDLP claim.*

---

## 1. The identification

> **`[PROVED — UNREVIEWED]`** *(my derivation; no independent pass has been run on it — CLAUDE.md §3/§7)*
>
> The subgroup `⟨−1⟩ ⊂ μ₄` acts on `C : w⁴ = f(x)` by `w ↦ −w`. The quotient `C/⟨−1⟩` is `y² = f(x) = E`
> via `y = w²`. Pullback embeds `Jac(E) ↪ Jac(C)` with image the `⟨−1⟩`-**invariant** part, i.e. the
> `j`-even eigenspaces of the `μ₄`-action on `H¹` (and `j=0` contributes nothing, so: the `j=2` part).
> Hence the complement — **"the new part"** — is the sum of the eigenspaces on which `−1` acts by `−1`,
> i.e. `j` odd, i.e. `j ∈ {1,3}`. And `j ∈ {1,3}` are exactly the **faithful** characters of `μ₄`, i.e.
> the `χ₄`-isotypic part (`χ₄` and `χ̄₄ = χ₄³`).
>
> **⇒ "new part complementary to `E`" = "`χ₄`-isotypic factor". The two descriptions coincide.** ∎

Dimensions agree: `C` has genus 3 (degree-4 cyclic cover of `P¹`, `deg f = 3`, `gcd(4,3)=1` so `∞` is
totally ramified), `dim Jac(E) = 1`, so `dim A_new = 2` — the project's stated dimension.

**Why `b₁ = 0` follows** (and is a *derivation*, matching `RESULT_anew_isogeny_type_correction_v1.md:32`
*"§A1.1 Fact 1 **derives** it"*): at `p ≡ 3 mod 4`, `χ₄^p = χ̄₄`, so `Frob_p` **interchanges** the `j=1`
and `j=3` blocks. A block-off-diagonal matrix has trace 0. This is §A1.1's conjugation relation
`π ζ₄ π⁻¹ = ζ₄⁻¹` (`RESULT_mu6_cover_and_conductor_v1.md:31`) in coordinates.

---

## 2. Numerical confirmation of the two consequences

For `C : w⁴ = x³ + B` (`B ≢ 0 mod p`, else the curve is singular), 8 primes `p ≡ 3 mod 4` × up to 5 `B`:

| test | statement | result |
|---|---|---|
| **T1** | `#C(F_p) = p + 1 − a_p` ⟺ `b₁(A_new) = 0` | **38/38** |
| **T2** | `#C(F_{p²}) = p² + 1 − a_p² + 2p + 2S` ⟺ `b₂(A_new) = S` | **38/38** |
| **T3** | `m = S/p` is an integer in `{−2,1,2}` **and** equals the A2.1 branch; `Im S = 0` | **38/38** |

`Σβᵢ² = b₁² − 2b₂`, so the `S`-to-`b₂` conversion `b₂ = −½Σβᵢ²` needs `b₁ = 0` — which §1 supplies. This
independently reproduces the dictionary the (★) reviewer verified at 58 pairs, on a disjoint prime set.

### ★ Forced / unforced accounting (drill rule: count only unforced hits, and reproduce the count)

- **T1 is FORCED.** `b₁ = 0` is derived by the `μ₄` argument, so all 38 rows are an **instrument check on
  my code**, not evidence for `b₁ = 0`. `RESULT_anew_isogeny_type_correction_v1.md:32` grades its own
  22/22 exactly this way; this file does the same rather than re-banking it.
- **T3 is 12 distinct, not 38.** `S` depends on `B` only through `χ₃(B)`, and the two cubic **non**-residue
  classes give the *same* `S` (both `−J`, since `ω + ω² = −1`). So per prime there are at most 2 distinct
  outcomes, and at `p ≡ 11 mod 12` exactly 1 (`S = 2p`, `B`-independent). Count:
  `4 primes ≡ 11 × 1 branch = 4`, `4 primes ≡ 7 × 2 branches = 8` ⇒ **12 distinct; 26 of the 38 rows are
  forced repeats.**
- **T2's unit is `(p,B)`** — `#C(F_{p²})` and `a_p` both vary with `B` even where `S` does not, so each row
  is a separate equation among three independently computed integers. But T2 tests the **point-count
  dictionary**, a step of the derivation, so it carries **zero independent weight for the `m`-law**.

### Firing controls — all three fire

| control | expectation | result |
|---|---|---|
| **FC1** T1 run at `p ≡ 1 mod 4`, where `b₁=0` is **not** forced | must fail somewhere, else T1 is vacuous | **FIRES — 9 of 24 fail** (`p = 13, 37, 61`; holds at `5, 17, 29, 41, 53`) |
| **FC2** T2 fed a perturbed `S+1` | must reject | **FIRES — 11/11 rejected** |
| **FC3** T2 fed the correctly-computed `S` of a *different* `B` at the same prime | must reject where the two differ | **FIRES — 14/14 rejected** |

FC1 is the load-bearing one: it shows `#C(F_p) = p+1−a_p` is a real constraint rather than an identity
that holds regardless. Its pattern also reproduces the known fact that `b₁ = 0` is **not exclusive** to
`p ≡ 3 mod 4` (`PREREG_mu4_eigenvalue_individual_v1_DEVIATIONS.md` item 5: `b₁=0` also at `p = 233, 257`)
— here at `p = 5, 17, 29, 41, 53`. The `μ₄` argument gives one direction only; the converse is false, as
that file already recorded.

**A defect in my own control run, logged:** FC2's first execution aborted on its own guard because I omitted
the `B ≡ 0 mod p` skip, feeding it the singular curve at `p = 7, B = 7`. Fixed; the skip matches the main
run's. Recorded because the guard firing is the only reason it was caught.

---

## 3. Ledger effect and scope

| item | before | after |
|---|---|---|
| `A_new` identification (§2 residual of the (★) review) | *"one line owed"* — coincidence stated, not proved | **`[PROVED — UNREVIEWED]`** (§1), consequences verified 38/38 with 3 firing controls |
| `b₁ = 0` | derived in §A1.1; not restated in the `m`-law files | **derived here in coordinates**; T1 is an instrument check, not evidence |
| `b₂ = S` | verified 58 pairs by the (★) reviewer | **reproduced on a disjoint prime set**, 38 equations, FC2/FC3 fire |

**Scope — what this does NOT do.**
- **`(D2)`/Katre is untouched.** `m = 1` still carries the three Katre caveats, caveat 1 load-bearing.
  Closing this residual removes one of the two debts named in `RESULT_star_adversarial_review_v1.md` §5;
  the citation debt is the other and is unaffected by anything here.
- **§1 is unreviewed.** It is my derivation. It is short and standard (the `μ_n`-cover eigenspace
  decomposition), but by the standard applied to (★) it is `[PROVED — UNREVIEWED]` until an independent
  pass runs, and it should not be cited as more.
- **No `a≠0` content.** All of this is the `a=0` anchor. The 120° law's uniformity gap is over
  `a ∈ (ℤ/n)*` and is untouched — see `RESULT_120deg_anchor_from_mlaw_v1.md` §5.
- **Novelty not claimed.** The eigenspace decomposition of a cyclic-cover Jacobian is textbook.
