# The `c₂(a)` splitting law for `A_new(C_a)` — SYMBOLIC PROOF, modulo the Stickelberger citation

**Date:** 2026-08-10 · Verification script: `scratchpad/session_2026-08-11/prove_c2_law.py` (exact `ℤ[ζ₁₂]`
arithmetic, no float in the signal path). Companion point-count checks: `scratchpad/session_2026-08-11/verify_tower_s1.py`.

**No ECDLP, leakage, or key-recovery claim.** `c₂` is a CM label on the Frobenius eigenvalues of a
supersingular abelian surface; pinning it extracts no bit of any scalar. Public data only.

---

## 1. The result

> **Theorem (c₂ law).** Let `p ≡ 7 mod 12`, and let `A_new(C_a)` be the new part of the Jacobian of
> the cover `C_a : w⁴ = x³ + a` (`a ∈ F_p^*`). Its Frobenius characteristic polynomial over `F_p` is
> `X⁴ + c₂ X² + p²` (the linear/cubic coefficients vanish, `e₁ = e₃ = 0`), with
> ```
>   c₂(a) = −2p    if a is a cubic residue mod p        (char poly (X²−p)²,  eigenvalues ±√p)
>   c₂(a) = +p     if a is a cubic non-residue mod p    (eigenvalues √p·{primitive 3rd, 6th roots})
> ```
> **`[PROVED — modulo (D2)]`**, where **(D2)** is Stickelberger's Jacobi-sum valuation formula, the
> single external input inherited unchanged from `RESULT_jacobi_sign_law_stickelberger_v1.md`.

This upgrades the status recorded in the external audit document
`splitting-field-and-galois-audit-v3.md` §1, which stated the law as *"discovered and proved"* but
supported it only by **exhaustive point-count at `p ∈ {43,67,79}`** — i.e. verified at three primes,
conditional in general. The argument below is **prime-independent** (character-sum algebra), so it
proves the general-`p` statement, resting on exactly one classical citation.

## 2. The proof

Work over `F_{p²}`, where the quartic character `χ₄` (order 4) and cubic character `χ₃` (order 3)
both exist (`4, 3 ∣ p²−1`). Fix `χ₄, χ₃` of those orders; `χ₄(0)=χ₃(0)=0`.

**(P1) `c₂ = Re T(a)`, where `T(a) = Σ_{x∈F_{p²}} χ₄(x³+a)`.**
Since `e₁ = 0`, the sum of squared Frobenius eigenvalues is `Σπᵢ² = e₁² − 2e₂ = −2c₂`. That sum is
the new-part Frobenius trace over `F_{p²}`, and the new part of `#C_a(F_{p²})` is carried by the
`χ₄` and `χ₄³ = χ̄₄` sums, `T(a) + T̄(a)`. Bookkeeping `#C = q+1−t` gives `−2c₂ = −(T(a)+T̄(a))`,
i.e. **`c₂ = (T(a)+T̄(a))/2 = Re T(a)`.**

**(P2) `χ₄(a) = 1` for every `a ∈ F_p^*`.**  For `a ∈ F_p^*`, `χ₄(a) = a^{(p²−1)/4}`; since
`(p²−1)/4 = (p−1)(p+1)/4` and `a^{p−1}=1`, this is `1`. So the `a`-dependence enters **only** through
`χ₃`.

**(P3) The character-sum reduction.**  Writing the number of cube-roots of `t` as
`Σ_{i=0}^2 χ₃^i(t)` and substituting `t = a s`,
```
   T(a) = χ₄(a) · [ χ₃(a) · J(χ₃,χ₄) + χ̄₃(a) · J(χ̄₃,χ₄) ]  =  χ₃(a)·J₁ + χ̄₃(a)·J₂
```
using (P2), where `J₁ = J(χ₃,χ₄)`, `J₂ = J(χ̄₃,χ₄)` are Jacobi sums over `F_{p²}`.
*(The `i=0` term cancels the isolated `t=0` term; standard.)*

**(P4) The sign law (the one external input).**  By
`RESULT_jacobi_sign_law_stickelberger_v1.md`, for `p ≡ 7 mod 12` **both** order-3 characters give
`J(χ₃,χ₄) = J(χ̄₃,χ₄) = −p`. Hence
```
   T(a) = −p · (χ₃(a) + χ̄₃(a)).
```

**(P5) Trace of a cube root of unity.**  `χ₃(a) + χ̄₃(a) = 2` if `χ₃(a)=1` (a cubic residue),
`= ω+ω² = −1` otherwise. Therefore `T(a)` is rational and
```
   c₂ = Re T(a) = T(a) = −p·(χ₃(a)+χ̄₃(a)) = −2p  (residue)  /  +p  (non-residue).   ∎
```

## 3. Exact verification (spec: every link, all `a`, exact ℤ[ζ₁₂])

`scratchpad/session_2026-08-11/prove_c2_law.py`, `F_{p²} = F_p[t]/(t²−ns)`, characters via discrete log into
`ℤ[ζ₁₂] = ℤ[x]/(x⁴−x²+1)` (4-vectors of Python `int`). No float in the signal path.

| id | check | `p=43` | `p=67` |
|---|---|---|---|
| V1 | `χ₄(a)=1` for all `a∈F_p^*` | PASS | PASS |
| V2 | `J₁ = J₂ = −p` exactly (ring elt `[−p,0,0,0]`) | PASS | PASS |
| V3 | `T(a) = χ₃(a)J₁ + χ̄₃(a)J₂` for **all** `a` (P3) | PASS | PASS |
| V4 | `c₂ = Re T(a)` matches the sign-law prediction `−p(χ₃(a)+χ̄₃(a))`, all `a` | PASS |  PASS |
| V5 | both `== ` independent point-count `c₂` (`−2p`/`+p`) (from `scratchpad/session_2026-08-11/verify_tower_s1.py`) | PASS | PASS |

Point-count corroboration across the full fibre at `p∈{43,67,79}` (residue counts 14/22/26 → `−2p`;
non-residue 28/44/52 → `+p`; `e₁=0` throughout): PASS. Eigenvalue root-orders `[1,1,2,2]` (residue) /
`[3,3,6,6]` (non-residue) — matches the corrected memory
`[[secp-mu4-eigenvalue-individual-2026-07-20]]`; the ζ₁₂ root-system error is **not** present.

## 4. Grade ledger — what is proved, and the one debt

| link | grade | note |
|---|---|---|
| (P1) `c₂ = Re T(a)` | `[PROVED]` (elementary, verified V4/V5) | Newton + point-count bookkeeping |
| (P2) `χ₄(a)=1` on `F_p^*` | `[PROVED]` (verified V1) | order argument |
| (P3) reduction `T = χ₃(a)J₁+χ̄₃(a)J₂` | `[PROVED — UNREVIEWED]` | elementary char-sum algebra; verified exactly for all `a` at 2 primes, but **same-model, no adversarial review** (CLAUDE.md §3) |
| (P4) `J = −p` sign law | `[PROVED — modulo (D2)]` | inherited from `RESULT_jacobi_sign_law_stickelberger_v1.md`, unchanged |
| (P5) `χ₃+χ̄₃ ∈ {2,−1}` | `[PROVED]` | trace of a root of unity |
| **assembled `c₂` law** | **`[PROVED — modulo (D2)]`** | adds **no** new debt beyond the sign law's (D2) |

**The one debt (D2), unchanged.** Stickelberger's Jacobi-sum valuation formula for composite `m=12`,
`f=2` remains a **named, unverified literature citation** — the `citation-verifier` pass has failed
three times on session limits. This does not affect any algebraic step above; it is the sole external
premise. Candidate sources: Ireland–Rosen 2nd ed. Ch. 14; Berndt–Evans–Williams Ch. 11; Washington
Ch. 6; Lang *Cyclotomic Fields* Ch. 1.

**No grade was moved up on a citation's strength here** (CLAUDE.md §2): the assembled law inherits the
sign law's existing `[PROVED — modulo (D2)]` grade; it does not upgrade (D2). Running
`citation-verifier` on (D2) is still owed and would discharge the last debt for *both* results at once.

## 5. Provenance / relation to the external documents

- Verifies and **upgrades** `~/Downloads/splitting-field-and-galois-audit-v3.md` §1 (batch-vetting
  document 9): its numbers are exact (c₂ law, counts, eigenvalue root-orders, the degree-10 minimal
  polynomial `T¹⁰+155T⁸+6138T⁶+92070T⁴+555861T²+1060975`, and the degree-40 tower cycle types
  `[20,20]/[4,4,16,16]/[2,2,18,18]/[4,36]/[10,30]`, all reproduced independently). Its §1 wording
  *"proved"* is corrected to `[PROVED — modulo (D2)]`; its §3 *"SL₂/Sp₄-type monodromy"* remains a
  heuristic reading (only `G ⊆ A₄₀` is verified, via even parity of all five cycle types).
- The proof chain is the same `(★)` reduction named in `[[secp-mu4-eigenvalue-individual-2026-07-20]]`,
  here re-derived independently and verified exactly for all `a`.
