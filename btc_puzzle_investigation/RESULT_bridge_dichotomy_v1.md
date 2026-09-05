# Where the reciprocity bridge exists: a dichotomy located empirically across `(D, ℓ)`

**Date:** 2026-07-24 · Pre-registered: `PREREG_bridge_dichotomy_v1.md` (frozen before any run).
Scripts: `scratchpad/bridge_dichotomy_v{1,2}.py`. Exact integers; every verdict from an **exact
permutation count**, no float threshold. External literature search run **before** the design (§5).

---

## 0. The reduction (derived, elementary, and it is the whole question)

`n = p+1−t ⇒ n − p = 1−t`. So with `U := |t−1|`:

> **`n ≡ p (mod U)`**, and for odd `ℓ`: `χ_ℓ(p mod n) = χ_ℓ(U mod n)`, `χ_ℓ(n mod p) = χ_ℓ(U mod p)`.

The bridge question is therefore the classical one: *for two primes `p ≡ n (mod U)`, are the `ℓ`-th
power characters of the same `U` related?* `ℓ=2`: yes, `ℚ(√U)/ℚ` is abelian. `ℓ≥3`:
`ℚ(ζ_ℓ, U^{1/ℓ})/ℚ` is **non-abelian**, so no congruence can do it — a bridge then needs `ζ_ℓ` to lie
**in the CM field**, which is what `ℓ=3, D=−3` had.

## 1. First result: which CM discriminants can have prime order at all

Every `D` in a 23-discriminant sweep (including class number `> 1`: `−35,−51,−91,−115,−123,−187,
−235,−267,−403,−427`), all twists, `p < 1.2·10⁵`:

| `D mod 8` | 2 in `K` | odd `n` found | prime `n` found |
|---|---|---|---|
| `5` (`−3,−11,−19,−35,−43,−51,−67,−91,−115,−123,−163,−187,−235,−267,−403,−427`) | **inert** | yes, all | yes, all |
| `1` (`−7,−15`) | split | **0 of 16,864** | 0 |
| `0,4` (`−4,−8,−20,−24,−40`) | ramified | **0 of 50,613** | 0 |

> **(D1) Prime-order CM curves exist exactly for `D ≡ 5 (mod 8)`** — i.e. exactly when `2` is inert in
> the CM field. **0 exceptions in 67,477 twist orders.** `[VERIFIED — classical]` (`2 ∣ #E` unless 2 is
> inert). This is *why* four arms of the prereg returned no instances: **a structural blocker, not a
> sampling shortfall.**

**Corollary that collapses one branch of the hypothesis.** The only imaginary quadratic discriminant
with `w = #O^* = 4` is `D = −4`, and `−4 ≡ 4 (mod 8)` is ramified. So:

> **(D2) Among prime-order CM curves, `w ∈ {2, 6}` only — the `w=4` (quartic) branch is empty.**
> The prereg's Arm 5 anticipated this for `D=−4` via the 2-torsion point `(0,0)` on `y²=x³+ax`
> (verified: `35,907` twist orders, `0` odd); (D1) shows it is one case of a general law.

## 2. Main result: the bridge's location, with power

Statistic (generator-free, as pre-registered): `A := [p is an ℓ-th power residue mod n]`,
`B := [n is an ℓ-th power residue mod p]`; agreement count vs an exact permutation null
(`20,000` shuffles). `E` = agreements expected under independence. **Power** is quoted against an
**Arm-1-sized** effect (`ratio 1.62`), as `z ≈ 0.62·√E`. `N = 6000` throughout.

| family | `w` | agree | `E` | ratio | perm `p` | power | control | verdict |
|---|---|---|---|---|---|---|---|---|
| **`D=−3, ℓ=3`** (POS CTL) | 6 | 1144 | 676.3 | **1.69** | `1/20001` | `16.1σ` | clean | **ASSOCIATION** |
| `D=−3, ℓ=5` | 6 | 238 | 246.9 | 0.96 | `15324/20001` | `9.7σ` | clean | absent |
| `D=−3, ℓ=7` | 6 | 123 | 128.4 | 0.96 | `14529/20001` | `7.0σ` | clean | absent |
| `D=−3, ℓ=11` | 6 | 54 | 52.5 | 1.03 | `8671/20001` | `4.5σ` | clean | absent |
| `D=−3, ℓ=13` | 6 | 34 | 33.1 | 1.03 | `9161/20001` | `3.6σ` | clean | absent |
| `D=−11, ℓ=3` | 2 | 680 | 654.7 | 1.04 | `1521/20001` | `15.9σ` | clean | absent |
| `D=−19, ℓ=3` | 2 | 646 | 639.5 | 1.01 | `7241/20001` | `15.7σ` | clean | absent |
| `D=−43, ℓ=3` | 2 | 665 | 666.6 | 1.00 | `10978/20001` | `16.0σ` | clean | absent |
| `D=−67, ℓ=3` | 2 | 644 | 670.0 | 0.96 | `18763/20001` | `16.0σ` | clean | absent |
| `D=−163, ℓ=3` | 2 | 619 | 659.9 | 0.94 | `19834/20001` | `15.9σ` | clean | absent |

**The positive control reproduced its pre-committed effect size**: predicted `agree/N ≈ 0.194` against
independence `0.111`; observed `0.1920` vs `0.1185` (v1, `N=3000`) and `ratio 1.69` (v2, `N=6000`).
**Every negative control (random base vs `B`) came back clean.**

> **(D3) H-dichotomy holds in both testable branches.** The bridge is present at `ℓ=3` **only** for
> `D=−3`, and absent at every `ℓ ≥ 5`. Combined with (D2):
>
> ### Among prime-order CM elliptic curves, the reciprocity bridge exists at `ℓ = 2` for every `D`, and beyond that **only** for `D = −3` at `ℓ = 3` (hence `ℓ = 6`).
>
> `D = −3` is the **unique** discriminant admitting a bridge past the quadratic one — and secp256k1
> (`j = 0`, CM by `ℤ[ω]`) sits on it.

## 3. Scope of the nulls — pre-committed wording, reproduced verbatim

> *"No bridge with a non-uniform correction is detectable by a generator-free 2×2 association at this
> N."* It is **not** "no bridge exists."

Concretely: the test sees a bridge only when its correction `c` is **non-uniformly** distributed (the
cubic bridge is detectable because `P(c₃=0) ≈ 0.58`). A hypothetical `ℓ≥5` bridge whose correction were
exactly uniform and independent of `k` would leave `A ⊥ B` and be reported "absent" — wrongly.
Additionally the `ℓ=13` row has only `3.6σ` power against an Arm-1-sized effect, so it bounds only
large effects; `ℓ=5,7` (`9.7σ`, `7.0σ`) and all `ℓ=3` rows (`≈16σ`) are strongly tested.

## 4. Where secp sits

secp is `D = −3`, `w = 6`, `n` prime — so by (D1) it satisfies the `D ≡ 5 mod 8` condition
(`−3 ≡ 5`), and by (D3) it is on the one discriminant carrying the extra bridge. That is a
**restatement of `j=0` / CM by `ℤ[ω]`**, not an independent property, and it carries **no leakage or
ECDLP content** — both sides of every bridge are computable from public `p`, `n`, `t`.

## 5. Prior art — searched BEFORE the design, and the honest grade

WebSearch, 2026-07-24. Cubic/quartic/Eisenstein reciprocity, Gauss's `p = a²+27b²` criterion, sextic
twists of `j=0`, and the classical count "`y²=x³+k` over `F_p`, `p≡1 mod 6`, takes at most six orders
as `k` varies, by sextic residue class" are all classical. One retrieved source states the governing
principle outright — *a number field containing the `n`-th roots of unity enables power reciprocity
laws* — **which is exactly the mechanism of H-dichotomy**. Likewise `2 ∣ #E` unless 2 is inert is
standard.

> **Nothing here is claimed as new mathematics.** (D1) and (D3) are consequences of standard theory;
> what this file contributes is the **measurement** — the boundary located across `(D, ℓ)` with a
> firing positive control, clean negative controls, and quoted power. Graded
> `[VERIFIED — classical mechanism]`. **`citation-verifier` has NOT been run**; any novelty claim
> requires it (ledger ★ item, still outstanding).

## 6. What stays open

- **The uniform-correction blind spot** (§3) is not closed by anything here. Closing it needs a
  statistic sensitive to a bridge with uniform correction — none is in hand, and the labelling
  obstruction (no canonical `ζ_ℓ` in both `F_n` and `F_p` for `ℓ≥5`) is exactly the mathematical
  content of the null, so the two are hard to separate.
- **`ℓ = 11, 13` are weakly bounded** (`4.5σ`, `3.6σ`); `ℓ ≥ 17` untested entirely.
- **Class number was not varied within the `w=2` arm** — all five tested (`−11,−19,−43,−67,−163`) have
  `h=1`. The `h>1` discriminants appear only in (D1)'s sweep, never in the association test.
- **`w=4` is unreachable**, so H-dichotomy's *"iff"* is verified only at `w ∈ {2,6}`; the quartic
  branch is untestable in the prime-order setting by (D2) and would need a different framework
  (e.g. working modulo the odd part of `#E`, a different object).
