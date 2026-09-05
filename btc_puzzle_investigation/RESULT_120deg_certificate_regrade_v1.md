# RESULT — the 120° law regraded: `[VERIFIED]` → `[PROVED-exact, conditional on two FORCED premises]`

**Date:** 2026-08-01. **Item:** A of `NEXT_SESSION_PROMPT_2026-08-01_v2.md`.
**Supersedes the grade set by** `CORRECTION_120deg_census_certification_direction_v1.md` §4.
**Derivation + measurement:** `ANALYSIS_120deg_exact_factorization_certificate_v1.md`.
**Scripts:** `verify_120deg_symbolic_factorization_v1.py`, `verify_120deg_exact_certificate_v2.py`
(both pass `check_no_float.py`; logs and `RESULT_120deg_exact_certificate_v2.json` on disk).

---

## 1. What moved

The CORRECTION demoted the census's 2464 `g = 2` cells from `[PROVED-exact]` to `[VERIFIED]`,
correctly: `min_l g_l ≥ g_true` is an **upper** bound, so a computed `2` certifies only `g ≤ 2`, and
the gate's own PLANT-B (true `g₃ = 0`) reads `2` at `l = 13, 37`.

The missing **lower** bound is now supplied — not by the resultant certificate the CORRECTION §5
specified, but by **exhibiting the common quadratic factor in closed form**:

> `D(T) = T² + ζ₃·e₁·T + χ₂(−1)·p·ζ₃²`

`D` divides both `L(T)` and `L(ζ₃T)` as a **polynomial identity in `ℤ[e₁, p, ζ₃]/(ζ₃²+ζ₃+1)` with
`e₁` and `p` free**, given `e₂ = e₁² − χ₂(−1)p`, `e₃ = χ₂(−1)p·e₁`, `e₄ = p²`. `D` is monic of
degree 2 for every `e₁, p` — no degeneracy locus. Hence `g ≥ 2` unconditionally.

Conjoined with the census's exact `g ≤ 2`: **`g = 2` exactly.**

| item | CORRECTION (2026-07-31) | now |
|---|---|---|
| census `g = 0` cells | `[PROVED-exact]` | unchanged |
| census `g = 2` cells (2464, 22 primes) | `[VERIFIED — upper bound only]` | **`[PROVED-exact]`**, conditional — §3 |
| the 120° law at those cells | `[VERIFIED]` | **`[PROVED-exact]`**, conditional — §3 |
| `min_l g_l` reasoning | one-sided | still one-sided; now **conjoined** with a lower bound, as §5 demanded |

**The CORRECTION is not retracted.** Its diagnosis was right and its §5 demand — *state and use the
conjunction* — is exactly what is met here. Only its proposed *route* to the lower bound is
bypassed (§2).

## 2. Why the specified repair was not used

CORRECTION §5 specifies `Res_T = 0 ∧ S₁ = 0` computed in `ℤ[ζ_M] = ℤ[y]/Φ_M(y)`, `M = lcm(N,k)`,
with `ζ_N, ζ_k` pinned jointly, plus a rewrite of `reduce_phi_prime` for general `Φ_M`. All of that
is correct and all of it is unnecessary: `M = 3n` gives a ring of degree `φ(3n) = 2(n−1) ≈ 5000`,
and the computation would be **per cell, per prime**. The exhibited identity is proved **once**, with
`e₁` and `p` free, covering every cell of every prime — including primes never enumerated. It also
sidesteps the zero-ring hazard that forced §5's first retraction, and needs no `Φ_M` rewrite.

**Consequence for the record:** `reduce_phi_prime`'s prime-only limitation
(`audit_n1_vsign_v2_core.py:198`) remains a real defect, but is **no longer blocking** for this item.
It still blocks anything that genuinely needs composite `Φ_M` — e.g. the cofactor-2 arms of item B.

## 3. The conditions — this grade is conditional and the conditions are named

`[PROVED-exact]` here means: *given the two forced coefficient relations, the law follows exactly at
every cell of the 22 census primes.* Two premises are inherited, not proved in this work:

1. **`e₃ = χ₂(−1)·p·e₁` and `e₄ = p²`** — `[PROVED — FORCED]` from the closure per
   `ANALYSIS_n1_charpoly_collapse_v1.md` §1. Independently re-measured only at `p = 43, 67, 127`
   (record's `[CONFIRMED-independent]`); re-measuring at scale needs `V₃, V₄`, i.e. `O(p³)`/`O(p⁴)`
   point counts, which is why it was not done here. **This is the weakest link in the chain and it
   is a citation-to-own-record, not a check run today.**
2. **`e₂ = e₁² − χ₂(−1)·p`** — MEASURED exactly, 22/22 primes, all cells (§4 of the ANALYSIS).
   Deriving it remains the open item; it is unchanged by this work.

**Scope, stated plainly.** This covers **the 22 census primes** (`p ≤ 2503`). It does **not** prove
uniformity in `p`, and nothing here bears on `p` at cryptographic size. What changed is the *kind* of
statement at those primes — from "overwhelming but non-certifying odds over 5 ells" to "exact, given
one measured integer per prime". The uniform-`p` gap (#26, the monodromy theorem) is untouched.

## 4. Second result — a branch error in the collapse identity

`e₂ = e₁² + p` (`ANALYSIS_n1_charpoly_collapse_v1.md` §2, and every file quoting it) is the
`p ≡ 3 mod 4` case only. The general law is

> **`e₂ = e₁² − χ₂(−1)·p`**, i.e. `V₂ = V₁² − 2·χ₂(−1)·p`

Derived §1/§3 of the ANALYSIS, then **measured**: 5/5 at the stratum-C primes (577, 733, 1237, 1249,
1669), which are `p ≡ 1 mod 12` and where the target is `−2p`. The flipped-branch sign matches at
0/22 — the test discriminates.

Every prime at which the `V₂` identity had previously been verified is `p ≡ 3 mod 4`
(`RESULT_e2_identity_extended_verification_v1.md`: 43, 67, 79, 127, 163, 211, 547; scoped `p ≡ 7 mod 12`).
Stratum C exercised the `ε = +1` branch but never read `e₂` against a prediction, so nothing
contradicted the over-general statement.

**Action on the record:** the `V₂ = V₁² + 2p` identity carries scope **`p ≡ 3 mod 4`**. Any file
stating it branch-free is over-general. This does not change any `p ≡ 3 mod 4` result — the
in-scope arithmetic is unaffected.

## 5. Consequence for queue item B (cross-`j` Aut-contrast) — a LEAD, not a result

`NEXT_SESSION_PROMPT_2026-08-01_v2.md` §B asks for a relevance check before rebuilding the cross-`j`
discriminator. This work changes its cost structure and should be weighed before that decision.

**The observation.** §1 routes the `ζ₃` lock through a chain that mentions `Aut(E)` nowhere:
`e₃, e₄` are forced by the closure (Weil, generic), and the only special input is
`e₂ = e₁² − χ₂(−1)p`. The `ζ₃` in `D(T)` is the **twist variable of the statistic**, not the curve's
automorphism. So the necessary-condition question B was built to ask —
*is the lock present without `μ₃ ⊂ Aut`?* — becomes:

> **does `V₂(a) − V₁(a)² = −2χ₂(−1)p` hold on curves whose `Aut` lacks `μ₃`?**

That is **one integer per curve**, from one exact convolution. It needs no `deg gcd`, no `ℓ`-selection,
no `±`-coset cells.

**Why this matters for B's three recorded deaths.** All three were artifacts of the *cell/gcd*
construction, not of the question:

| B's death cause | does the `e₂` route hit it? |
|---|---|
| (1) `y²=x³+Ax` has `(0,0)` ⇒ `2 \| #E` ⇒ never prime order | **no** — the convolution route never required prime `n` |
| (2) `j=1728` supersingular at `p≡3 mod 4` ⇒ 0/22 frozen primes met the arm rule | **no** — no prime-order arm rule to meet |
| (3) `b₁=0` derived from `χ₄^p=χ̄₄`, valid only at `p≡3 mod 4` | **unknown — this is the one to check first** |

**⚠ The unverified premise, stated as such.** (3) is the live risk. The prompt records `b₁ = 0` as
what "the whole 4-dim reconstruction rests on" — and the quartic `L` is the object this entire
certificate is about. **If the quartic construction is itself `j=0`-specific, there is no `e₂` to
compare at `j≠0` and this lead evaporates.** Nothing here establishes that it survives; I did not
test it. The `μ₃`-block structure of the `V_k` at `j≠0` has not been examined in this session.

**Recommended order for B**, if it is taken up: settle whether `V₁, V₂` and the quartic reconstruction
are defined at `j≠0` *before* any arm is built. That is a definitional question, answerable from the
construction, and it decides B outright — it is the cheapest possible relevance check and it
strictly precedes the availability/cofactor engineering the prompt's revival plan describes.
**Graded: `[LEAD — one premise unverified]`. Not a finding, and not a licence to skip B's own defect
list** (F-EMPTY must still be ordered first, per v2's gate audit).

## 6. What this does NOT do

- Does not prove the cap. The chain `e₂ = e₁²−εp ⇒ V₂ = V₁²−2εp ⇒ S_y ≤ 2 ⇒ |V| ≤ 2√p` still has
  its first link open, and that link is a derivation target, not a measurement.
- Does not prove uniformity in `p`. No finite sweep does; this is not a sweep, but its measured
  premise is still per-prime.
- Does not touch purity at every embedding (A3, `[CITED]`, untested), which the cap needs alongside.
- Does not bear on ECDLP, key recovery, or anything at `2^256`. It is an exactness repair to a
  structural law at `p ≤ 2503`.
