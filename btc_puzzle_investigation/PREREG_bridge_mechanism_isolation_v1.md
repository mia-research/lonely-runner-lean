# PREREG — what generates the bridge, and is its effect size a derived constant?

**Date:** 2026-07-24 · **Frozen BEFORE any run.** Exact integers; verdicts from exact permutation
counts. Follow-on to `RESULT_bridge_dichotomy_v1.md` §6 (open: `h>1` never tested; effect size
unexplained; mechanism never isolated).

---

## P1 — Mechanism isolation: is the bridge CM-generated, or shape-generated?

Every CM instance satisfies **`n − p = 1−t = ±U`** exactly (`U = |t−1|`) — the two primes differ by
`U`. The proved cubic bridge used `ν = 1−π`, `π̄ ∈ ℤ[ω]` and Eisenstein reciprocity, i.e. **CM**.
But there is a live competing account:

> **Shape account.** `χ₃(U mod p)` factors over `ℤ[ω]` primes `λ ∣ U`; reciprocity sends each
> `χ_𝔭(λ) → χ_λ(𝔭)`, which depends on `𝔭 mod λ`. Since `n ≡ p (mod U)`, *if* the primes above `p`
> and `n` were correspondingly congruent mod `λ`, the association would follow **from `n−p = ±U`
> alone, with no CM input.**
> (It is not obvious that they are: `N(π_p) = p` does **not** fix `π_p mod λ`. This is exactly why the
> experiment is needed.)

**Matched control (frozen).** For each CM instance `(p, t, n)`, record `Δ := n − p = ±U`. Draw an
**unrelated** prime `p′ ≡ 1 mod 3` of the *same bit length*, set `n′ := p′ + Δ`; keep if `n′` is prime
and `≡ 1 mod 3`. Test the same 2×2 association on `(p′, n′)`. **`Δ` is matched exactly** — sign and
magnitude — so the only thing broken is the CM tie.

**Both outcomes are pre-interpreted (I am not required to predict correctly):**
- **Control ABSENT** ⇒ the bridge is **CM-generated**; `n−p=±U` alone does not produce it.
- **Control PRESENT** ⇒ the bridge is **shape-generated**; CM supplies only the exact correction, and
  `RESULT_cubic_sextic_bridge_v1`'s framing ("it comes from `ℤ[ω]`") is **too narrow and must be
  corrected in the record.**

## P2 — Effect size as a derived constant

`c₃ = s·(e(π̄′) − e(ν′)) mod 3`. If `s` is uniform on `ℤ/3` and `e(π̄′), e(ν′)` are independent
uniform on `ℤ/3`, then

```
P(c3 = 0) = P(s=0) + P(s!=0)*P(e_pib = e_nu) = 1/3 + (2/3)(1/3) = 5/9
association ratio = P(A and B)/(P(A)P(B)) = (1/3 * 5/9)/(1/9) = 5/3 = 1.6667...
```

> **H-constant:** `P(c₃=0) = 5/9` and the `D=−3, ℓ=3` association ratio is **exactly `5/3`**.

**Sub-claims, each tested separately (a composite fit is not accepted):**
(i) `s` uniform on `{0,1,2}`; (ii) `e(ν′)`, `e(π̄′)` each uniform; (iii) `e(ν′) ⊥ e(π̄′)`;
(iv) `k ⊥ c₃`; (v) `P(c₃=0) = 5/9`; (vi) ratio `= 5/3`.
**Falsified** if any sub-claim fails at `N = 20000` while the others hold — that localises the error
rather than rescuing the constant.

⚠ **Anti-fit guard.** `5/3` was computed from the *already observed* `1.69`/`1.62`, so it is
**post-hoc as a number**. Its protection is that it is (a) derived from a stated independence model,
(b) **parameter-free**, and (c) decomposed into six separately-falsifiable sub-claims above. It is
graded `[VERIFIED]` only if **all six** hold; if only (vi) holds it is a coincidence, not a law.

## P3 — The `h > 1` gap

`RESULT_bridge_dichotomy_v1` tested `w=2` only at `h=1` (`D = −11,−19,−43,−67,−163`). Run
`D = −35, −51, −91, −115, −123, −187, −235, −267, −403, −427` (all `≡ 5 mod 8`, all `h > 1`) at `ℓ=3`.
**Prediction: absent**, since `w=2` regardless of `h`. If any fires, H-dichotomy is keyed to something
other than `w` and must be restated.

## 4. Controls that must fire

| # | control | required |
|---|---|---|
| **C1** | `D=−3, ℓ=3` CM association | **must fire** (else all void) |
| **C2** | random base vs `B`, every arm | must stay clean |
| **C3** | P1's matched control must actually *sample matched* `Δ` | verify `Δ` distributions identical by construction |

## 5. Scope

Public data only (`p`, `n`, `t`); no leakage/ECDLP content. Nothing here is claimed novel — cubic
reciprocity and its supplements are classical (see `RESULT_bridge_dichotomy_v1` §5);
`citation-verifier` remains unrun.
