# VERIFY SPEC — the `J(χ₃,χ₄)` sign law via Stickelberger

**Frozen 2026-07-25, BEFORE any cell of the verification was computed.** This is the "define the check
up front" artifact (`CLAUDE.md` §3), not an experiment pre-registration: the object below is a
**derivation**, and the script's job is to *falsify* it if the derivation is wrong. There is no
hypothesis being fished for, so there is no multiple-comparison structure and no outcome-conditional
reporting — a single disagreeing cell kills the claim.

---

## 0. What is being claimed

> **Theorem (to be verified).** Let `p ≡ 3 mod 4`, `q = p²`, and let `χ₃`, `χ₄` be characters of
> `F_q^*` of order 3 and 4. Then
> ```
> J(χ₃,χ₄) = −p   if p ≡ 1 mod 3   (i.e. p ≡ 7 mod 12 — secp's class)
> J(χ₃,χ₄) = +p   if p ≡ 2 mod 3   (i.e. p ≡ 11 mod 12)
> ```
> for **every** choice of `χ₃` and `χ₄`.

This **supersedes the route** of `RESULT_jacobi_sign_law_semiprimitive_v1.md` §4–§5 rather than
extending it. That file proved the `p ≡ 11 mod 12` half **modulo (S)**, the semiprimitive Gauss-sum
evaluation, whose citation is `[UNVERIFIED]` (its `citation-verifier` pass failed). The route below
**does not use (S) at all**, so if it holds it discharges the unverified dependency on *both* halves,
not just the open one.

## 1. The derivation being checked (stated so the script can attack it)

- **(D1)** All four archimedean conjugates of `J` are Jacobi sums of nontrivial characters with
  nontrivial product, so all have absolute value `√q = p`.
- **(D2) [load-bearing, external]** Stickelberger's valuation formula for Jacobi sums, in the form
  `v_𝔭(J(ω^{−a},ω^{−b})) = [s(a) + s(b) − s(⟨a+b⟩)]/(p−1)`, `s` = base-`p` digit sum on `[0,q−1)`,
  `v_𝔭(p) = 1`; conjugates via `v_{σ_t^{−1}𝔭}(J) = v_𝔭(J(χ^t,ψ^t))`.
- **(D3)** With `m = 12`, `M = (q−1)/12`, `χ₃ = ω^{−4M}`, `χ₄ = ω^{−3M}`, the digit sums are closed-form
  and give `v_t = 1` for **all four** `t ∈ {1,5,7,11}` ⇒ `(J) = (p)` as ideals of `ℤ[ζ₁₂]`.
- **(D4)** `(J) = (p)` + (D1) + Kronecker ⇒ `J/p` is a root of unity ⇒ `J = ζ·p`, `ζ ∈ μ₁₂`.
- **(D5)** Reduce mod the prime above **2** (where `i ≡ 1`): `J ≡ −1`, which forces the `μ₃` part of `ζ`
  to be trivial ⇒ **`ζ ∈ μ₄`**.
- **(D6)** Reduce mod the prime above **3** (where `ω ≡ 1`): `J ≡ −1`, which pins `ζ = −1` when
  `p ≡ 1 mod 3` and `ζ = +1` when `p ≡ 2 mod 3`.

**(D2) is the only step taken from the literature, and its citation is NOT yet verified** — the
`citation-verifier` run launched for it died on a session limit, twice now for this project. Check C3
below is therefore not a convenience: it is the *substitute* for the citation, settling the
normalization by arithmetic rather than by reading. Whatever C3 returns, the grade of (D2) stays
`[UNVERIFIED CITATION — normalization confirmed numerically]` until a primary text is actually opened.

## 2. Pass criteria — all frozen, all exact-integer, no floats anywhere

Arithmetic: `ℤ[ζ₁₂] = ℤ[x]/(x⁴−x²+1)` as 4-vectors of Python `int`; `F_{p²} = F_p[T]/(f)`; characters
by discrete log against a verified generator. Project rule `btc_puzzle_investigation/CLAUDE.md`
(no floating point in the signal path) is in force.

| id | check | pass condition | on failure |
|---|---|---|---|
| **C1** | exact `J(χ₃,χ₄)` over `F_{p²}`, **all 4** character pairs `(χ₃^u, χ₄^w)` | `J = −p` (`p≡7 mod 12`) / `J = +p` (`p≡11 mod 12`), as an exact `ℤ[ζ₁₂]` element, **zero** failures | theorem false; report the cell |
| **C2** | `\|J\|² = q` (forced) | exact equality every cell | instrument broken — C1 uninterpretable |
| **C3** | Stickelberger predictor `v_t` vs the **directly computed** ideal factorization of `J` | agreement in every cell, all four `t` | (D2)'s normalization is wrong as I stated it |
| **C4** | closed-form digit lemmas (`s(4M)=s(M)=2(p−1)/3`, `s(3M)=p−1` for `p≡7 mod 12`; all `=p−1` for `p≡11 mod 12`) vs direct base-`p` digit sums | agreement for every `p ≡ 3 mod 4` in the scale sweep | (D3) false |
| **C5** | (D5)/(D6) congruences `J ≡ −1` mod the primes above 2 and 3 | exact, every cell | (D5)/(D6) false |

**C2 and C5 are forced checks** — they carry zero evidential weight for the theorem and are recorded as
instrument validation only. C1 and C3 are the load-bearing checks. C4 is the scale check.

## 3. Firing controls — the instrument must be shown able to REJECT

Recorded because the predecessor file was correctly criticized for reporting `43/43` from an instrument
never shown to fire. Each control below must fire; **any that does not names an unguarded component.**

- **FC1 — discrimination.** Run the *same* code at `p ≡ 1 mod 4` (where `χ₄` is **not** semiprimitive
  and the theorem's hypothesis fails). It must return a **non-rational** `J` in the great majority of
  cells. If it emits `±p` there too, C1's agreement is a constant-output artifact.
- **FC2 — the character map is not vacuous.** Feed a deliberately corrupted, non-multiplicative
  character. **C2 must FAIL.**
- **FC3 — sign discrimination.** The sign-flipped rule (`+p` at `p≡7`, `−p` at `p≡11`) must agree in
  **0** cells.
- **FC4 — the Stickelberger predictor discriminates.** Run the predictor on a case whose answer is
  known to be **not** `(p)`: the classical cubic `J(χ₃,χ₃)` over `F_p`, `p ≡ 1 mod 3`, where the ideal
  is a *single* prime of norm `p` (`v = 0` at one `t`, `1` at the other). The predictor must return
  `(0,1)`, **not** `(1,1)`. If it returns `1` everywhere it is a constant and C3 is worthless.
- **FC5 — planted wrong ideal.** A planted `J := π²` (norm `p²`, satisfies (D1), is the competitor
  §5 of the predecessor exhibited) must be **rejected** by C3.

## 4. Scale

The theorem is general in `p`, so scale is not evidence — but the *derivation's* arithmetic (C4) is
checkable at any size for free, since `s` reads only two base-`p` digits. Frozen scale ladder:

1. **C1/C2/C3/C5** at every `p ≡ 3 mod 4` with `p < 260` (field enumeration is `O(p²)`).
2. **C4** at every `p ≡ 3 mod 4` up to `10⁵`.
3. **C4 at secp's own `p = 2²⁵⁶ − 2³² − 977`**, together with an explicit re-derivation of
   `p mod 12` from the integer itself.

Item 3 is the one that matters for the ledger: if the theorem holds and C4 holds at secp's `p`, the
`m = 1` grade moves **without** any secp-scale field computation, because the proof is scale-free.

## 5. What a PASS licenses — and what it does not

- **Licenses:** `J(χ₃,χ₄) = −p` at `p ≡ 7 mod 12` graded `[PROVED — modulo (D2), citation unverified]`;
  the `p ≡ 11 mod 12` half **re-proved without (S)**; and, given the `m`-law's dependence recorded in
  `RESULT_jacobi_closed_form_m_law_v4.md`, **`m = 1` at secp moves `[CONDITIONAL] → [PROVED]` under the
  same (D2) proviso.**
- **Does NOT license:** any statement about leakage, key recovery, or ECDLP. `m = 1` is a statement
  about the curve's CM/quantum-number label. It is not a break and does not bear on one.
- **Does NOT license** dropping the (D2) citation debt. The literature item stays **OPEN** on the ledger
  with `citation-verifier` still owed, and the grade above carries the proviso in its tag, not in a
  footnote.
