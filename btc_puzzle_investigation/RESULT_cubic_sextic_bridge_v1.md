# The sextic bridge: `χ₆(p mod n)` is determined by `χ₆(n mod p)` — exact, closed-form, scale-free

**Date:** 2026-07-24 · Pre-registered: `PREREG_cubic_sextic_bridge_v1.md` (frozen before any run).
Scripts: `scratchpad/cubic_bridge_v{1,2,3}.py`. Exact integers only; no float in any signal path.
Object: `j=0` curve `/F_p`, `p ≡ 1 mod 3`, prime order `n = p+1−t`, `ℤ[ω]`, `ω = (−1+√−3)/2`.

Answers the probe left open by `RESULT_ord_n_residue_structure_v1.md` §6 (the cubic analogue of L1).

---

## 0. Controls — all fired before anything below was read

| control | result |
|---|---|
| **K0** Eisenstein cubic reciprocity `χ_ν(π̄′) = χ_π̄(ν′)` on primarized pairs | **4000/4000 PASS** |
| **K1** Gauss: `2` is a cubic residue mod `n` ⟺ `n = a²+27b²` | **1200/1200 PASS** |
| **K2** base rate `χ₃^{(n)}(p) = 1` vs random-base control | `0.3395` vs control `0.3250` (chance `1/3`) |
| **K3** `ω_n²+ω_n+1 ≡ 0 (mod n)`, `ω_p²+ω_p+1 ≡ 0 (mod p)` | asserted per instance, all PASS |

K0/K1 were pre-committed as *void-everything* controls. Both passed.

## 1. The result

Set `4p = t²+3v²` (`t,v` odd), `π = (t+v)/2 + vω`, `ν = 1−π` (`N(ν) = n`), `π̄ = (t−v)/2 − vω`.
Two exact facts drive everything: **`π ≡ 1 (mod ν)`** and **`ν ≡ 1−t (mod π̄)`**, and since
`n ≡ 1−t (mod p)`, the second is the ordinary cubic character of **`n` mod `p`**.

> ### (B1) Cubic bridge
> `χ₃(p mod n) = ω^{c₃} · χ₃(n mod p)`, with `c₃ = s·( e(π̄′) − e(ν′) ) mod 3`,
> where `s` is the primarizing-unit exponent and `e(λ) = (a+b+1)/3 mod 3` for primary `λ = a+bω`.
>
> **`[PROVED]`** modulo two classical inputs (Eisenstein reciprocity + its `ω`-supplement), **both
> verified here as controls.** **12,050 instances, 8→256 bits, 0 violations.**

> ### (B2) The correction is closed form
> `χ_λ(ω) = ω^{(a+b+1)/3}` for primary `λ = a+bω` — **6000/6000**. So `c₃` needs **no exponentiation**;
> the bridge is a congruence law, not a computation. `[VERIFIED — classical, Ireland–Rosen Prop 9.3.3]`

> ### (B3) `t ≡ 1 (mod 3)`, hence `s₁ = s₂`
> `p ≡ 1` and `n ≡ 1 (mod 3)` (the latter forced, = **L3**) give `n = p+1−t ⇒ t ≡ 1 (mod 3)`. Hence
> `π̄ − ν = t−1 ≡ 0 (mod 3)`, so `ν` and `π̄` take the **same** primarizing unit. **`[PROVED]`**;
> observed `(s₁,s₂) ∈ {(0,0),(1,1),(2,2)}` only — `993 / 1036 / 971` of 3000, never off-diagonal.

> ### (B4) Full sextic law
> Combining (B1) with quadratic reciprocity `(p/n) = (−1)^{((p−1)/2)((n−1)/2)}·(n/p)`:
> **`c_p = 6 ⟺ n` is a sextic residue mod `p`**, up to the two explicit corrections.
> Verified end-to-end — cubic, quadratic, **and** the combined `c_p` prediction:
> `3000/3000` (19–24 bits), `300/300` (64), `200/200` (128), **`150/150` (256 bits)**.

> ### (B5) Unconditional cubic forcing (the direct analogue of L1)
> `χ₃(−1) = 1`, so `χ₃^{(n)}(p) = χ₃^{(n)}(|t−1|)`; `|t−1|` a perfect cube ⇒ `χ₃ = 1` **forced**.
> Deduplicated (every `p` enumerated once): forced rate **`1.0000`** in all three ranges, `0` violations
> in `64` forced instances; free cells `0.3022 / 0.3436 / 0.3270` against `1/3`.
> Density `∝ p^{−1/3}` (measured `2.3% → 1.2% → 0.37%`), so **`~2^{−85}` at secp** — absent by derivation.

## 2. secp256k1

`s₁ = s₂ = 0` (both `ν` and `π̄` are already primary) ⇒ **`c₃ = 0`**; `n ≡ 1 (mod 4)` ⇒ quadratic sign
`+1`. So at secp the law degenerates to its cleanest possible form:

```
   p is a sextic residue mod n   <=>   n is a sextic residue mod p
```

`n` is a cube mod `p`: **True**. `n` is a QR mod `p`: **True**. ⇒ predicted `c_p = 6` — and the direct
computation agrees (`cube=True, sq=True`). `|t−1|` is **not** a perfect cube, so secp is not in (B5)'s
forced population: **the value is carried by the bridge, not by a forcing.**

## 3. Precision about what this does and does not overturn

`RESULT_ord_n_residue_structure_v1.md` graded `c_p = 6` "a `1/6` draw." **That stands, and is not in
conflict with (B4).** The bridge is a **determination, not a forcing**: it says the `n`-side character
*equals* the `p`-side one up to an explicit correction — it does **not** say either is trivial. The
distribution is still `1/6` (K2: `0.3395` vs control `0.3250`); what the bridge adds is **where the
draw is made** — on the `p`-side, as the sextic residuacity of `n` mod `p`. H-sextic (prereg
`…structure_v1` §3: *CM forces `p` into the index-6 subgroup*) remains **falsified**.

## 4. Scope — stated in the prereg, unchanged by the outcome

Both sides of the bridge are computable from **public** data (`p`, `n`, `t`). This is a **structure
map, not a lever**; it carries no leakage or ECDLP content, and none is claimed. Its one distinctive
property against caveat **#5** is that an *exact identity does not decay* — unlike (L2)'s `p^{−1/4}`
and (B5)'s `p^{−1/3}` densities, it holds at `2²⁵⁶` and was verified there (`150/150`, plus secp).

**Prior art — no originality claimed.** Cubic reciprocity, the `ω`-supplement, Gauss's `a²+27b²`
criterion, and the classical link between sextic characters and point counts on `y²=x³+b`
(Ireland–Rosen ch. 9 & 18; Rajwade) are **classical**, and the packaging here is very likely known.
Graded `[VERIFIED — classical]`. This is exactly the ledger's ★ literature item; `citation-verifier`
has **not** been run on it, and that remains outstanding.

## 5. Loose end closed

`DEVIATIONS #3` recorded `29/5125` unexplained failures of `(p/n) = ((1−t)/p)` for `n ≡ 1 mod 4`.
Retested with the corrected instance construction: **0 violations / 3000**. The superseded script did
not exclude `t = 1` (anomalous `n = p`, where `1−t ≡ 0` and the Legendre symbol is `0`, not `±1`);
those instances are excluded here. **Recorded as attributed-and-resolved.**

## 6. What stays open

- **`citation-verifier` on §4's prior-art claim** — the one thing that would settle whether any of
  (B1)–(B4) is new. Not run.
- **The `(s₁,s₂)` diagonal is proved, but the distribution over `{0,1,2}` is not explained**
  (`993/1036/971` ≈ uniform). Whether `s` is equidistributed and what governs it is untested.
- **(B5)'s excess prediction is consistent but unresolved**: predicted excesses `+0.015/+0.008/+0.003`
  against observed `−0.015/+0.018/−0.004`, with the forced population too rare (`64` instances) to
  resolve at these `N`. The *rate* law is exact; the *density* law is only order-of-magnitude here.
- **Higher `ℓ`.** `ℓ = 2, 3` work because `χ₂`, `χ₃` have classical reciprocity. `n−1`'s other prime
  factors (secp: `149, 631, …`) have **no** such law in hand; whether `χ_ℓ(p mod n)` admits any bridge
  for `ℓ ≥ 5` is untouched.
