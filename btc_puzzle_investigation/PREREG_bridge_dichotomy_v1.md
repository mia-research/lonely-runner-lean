# PREREG — where does the reciprocity bridge exist? A dichotomy across `ℓ` and across CM discriminant

**Date:** 2026-07-24 · **Frozen BEFORE any run.** Exact integers only; no float threshold decides any
verdict. Follow-on to `RESULT_cubic_sextic_bridge_v1.md` §6 (the `ℓ ≥ 5` probe).

## 0. The reduction that makes this a classical question (derived, not assumed)

`n = p+1−t` ⇒ `n − p = 1−t`, so with `U := |t−1|`:

> **`n ≡ p (mod U)`**, and for **odd** `ℓ` (where `χ_ℓ(−1)=1`):
> `χ_ℓ(p mod n) = χ_ℓ(U mod n)` and `χ_ℓ(n mod p) = χ_ℓ(U mod p)`.

So the bridge question is: **for two primes `p ≡ n (mod U)`, is `χ_ℓ(U mod n)` related to
`χ_ℓ(U mod p)`?** Classically:
- `ℓ = 2`: `(U/·)` is a congruence condition (`ℚ(√U)/ℚ` abelian) ⇒ a bridge must exist, **for every `D`**.
- `ℓ ≥ 3`: `ℚ(ζ_ℓ, U^{1/ℓ})/ℚ` is **non-abelian**, so no congruence determines it. The `ℓ=3`, `D=−3`
  bridge did **not** come from the congruence — it came from `ν = 1−π`, `π̄ ∈ ℤ[ω]` and Eisenstein
  reciprocity, i.e. from `ζ₃` lying **in the CM field**.

## 1. Hypothesis

> **H-dichotomy.** For a CM elliptic curve with CM order `O`, `w := #O^*`, and prime order `n`:
> a reciprocity bridge relating `χ_ℓ(p mod n)` to `χ_ℓ(n mod p)` exists **iff `ζ_ℓ ∈ Frac(O)`**,
> i.e. **iff `ℓ | w`**, `w ∈ {2,4,6}`.

Predictions, fixed now:

| arm | family | `ℓ` | prediction |
|---|---|---|---|
| **1 — POSITIVE CONTROL** | `D=−3` (`w=6`) | `3` | **association PRESENT** (bridge known, `RESULT_cubic_sextic_bridge_v1`) |
| **2** | `D ∈ {−7,−8,−11,−15,−19,−20,−43,−67,−163}` (`w=2`) | `3` | **absent** — `ζ₃ ∉ Frac(O)` |
| **3** | `D=−3` | `5,7,11,13` | **absent** — `ζ_ℓ ∉ Frac(O)` for `ℓ≥5` |
| **4 — NEGATIVE CONTROL** | all | all | replace `p` by a random base `r`: **absent everywhere** |
| **5 — BLOCKER** | `D=−4` (`w=4`) | `4` | **structurally untestable**: `y²=x³+ax` has the 2-torsion point `(0,0)`, so `#E` is **always even** ⇒ prime `n` impossible. To be **verified by enumeration**, not asserted. |

## 2. Statistic (choice-free) and the exact test

Higher-power characters have no canonical generator of `μ_ℓ` in `F_n` vs `F_p`, so any statistic on
*exponents* depends on an arbitrary labelling. The primary statistic is therefore **generator-free**:

```
A := [ p is an l-th power residue mod n ]      B := [ n is an l-th power residue mod p ]
```
2×2 table of `(A,B)`; association measured against an **exact permutation null** (shuffle `B`, recount
agreements, `10^4` shuffles, p-value = integer count / integer count). No float threshold.

**Pre-committed effect size for Arm 1.** Under the known cubic bridge `j = k + c₃` with `P(c₃=0) ≈ 0.58`:
`P(A∧B) = P(k=0)·P(c₃=0) ≈ 0.194` against `P(A)P(B) = 1/9 ≈ 0.111`. Arm 1 **must** reproduce this.

**Secondary (scope-limited):** uniformity of `(j−k) mod ℓ` under the frozen labelling
`ζ_q := g^{(q−1)/ℓ}`, `g` the least primitive root. Reported, but **not** used for any verdict.

## 3. The blind spot, stated before the run

This test detects a bridge **only if its correction `c` is non-uniformly distributed**. If a bridge
existed at `ℓ≥5` whose correction were exactly uniform over `ℤ/ℓ` and independent of `k`, then `A ⊥ B`
and the test would report "absent" — **wrongly**. Therefore:

> **A null in Arms 2/3 is scoped as: "no bridge with a non-uniform correction is detectable by a
> generator-free 2×2 association at this N."** It is **not** "no bridge exists." This wording is
> pre-committed and must appear in the result file verbatim.

## 4. Falsification

- **H-dichotomy is FALSE** if Arm 2 or Arm 3 shows association at the Arm-1 effect size (with Arm 4
  clean), or if Arm 1 shows **no** association (⇒ machinery broken, **all arms void**).
- **Arm 4 firing ⇒ machinery broken, all arms void.**

## 5. Prior art — checked BEFORE the run, and the honest grade

External search run 2026-07-24 (WebSearch). Cubic/quartic/Eisenstein reciprocity, the `p = a²+27b²`
criterion, sextic twists of `j=0`, and "an elliptic curve `y²=x³+k` over `F_p`, `p≡1 mod 6`, has at
most six orders as `k` varies, by sextic residue class" are all **classical**. One retrieved source
states the governing principle directly — *a number field containing the `n`-th roots of unity enables
power reciprocity laws* — which is **exactly** H-dichotomy's mechanism.

> **Therefore H-dichotomy is a PREDICTION OF STANDARD THEORY, not a new law.** Confirming it is
> **verification in a specific family**, and it is to be graded `[VERIFIED — classical mechanism]`.
> **No originality is claimed for the dichotomy.** What is genuinely ours is only the *measurement*:
> the boundary located empirically across `(D, ℓ)`. `citation-verifier` has **not** been run and
> remains outstanding for any novelty claim (ledger ★ item).

## 6. Scope

Everything here is computed from **public** data (`p`, `n`, `t`). No leakage/ECDLP content; none is
claimed. The purpose is to describe curve structure.
