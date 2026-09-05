# P2 = a CLASS-NUMBER identity: flap χ₂-imbalance = h(−p). A proved; P2 reduced to one identity.

**Date:** 2026-07-21 · Supersedes `..._v2.md` for the P2 part (**P1 stays a full theorem**, v2).
Script: `scratchpad/prove_P2_hard_v1.py` + closed-form verification. Exact ints; `h(−p)` via reduced
binary quadratic forms (validated vs known values). `p≡7 mod 12`, `H=(p−1)/2`, `ρ` primitive 6th root.

**Headline (verified, 134 primes `p<4000`):** the χ₂-weighted flap sum is a class number —
```
   S′ := Σ_{s∈T⁺} χ₂(s) = (3/2)·h(−p)·(1 − χ₂(2)),      O₊ − O₋ = h(−p)·(1−χ₂(2))/2.
```
So **`S′ = 0 ⟺ χ₂(2)=+1` (P2)**, and when it does NOT vanish (`p≡3 mod 8`) the imbalance is exactly
`h(−p)` (the class number of `ℚ(√−p)`), split `O₊−O₋ = h`. **P2 is a class-number theorem — modulo one
remaining identity (`C′−C = 3h`).**

---

## 1. Reduction `S′ = A + C`  `[PROVED]`
`T⁺ = {s∈[1,H]: ρs mod p ∈ [(p+1)/2, H+s]} = (μ_ρ\text{-set}) \ (M\text{-set})`, `M={s: ρs mod p>H+s}`,
and `M=W` via `×ρ` (P1), with `χ₂(ρ)=−1`. Hence `Σ_M χ₂ = −C` and
```
   S′ = A + C,    A := Σ_{s∈[1,H], ρs mod p>H} χ₂(s),    C := Σ_{s∈[1,H], ρs mod p<s} χ₂(s).
```

## 2. `A = Σ_{s=1}^{H} χ₂(s) = (2−χ₂(2))·h(−p)`  `[PROVED]`
Let `A_full := Σ_{s=1}^{p−1} χ₂(s)·[ρs mod p > H]`.
- **Bijection `t=ρs mod p`:** `A_full = χ₂(ρ⁻¹)Σ_{t>H}χ₂(t) = (−1)(−Σ_{[1,H]}χ₂) = Σ_{[1,H]}χ₂`
  (uses `χ₂(ρ)=−1`, `Σ_{t=1}^{p−1}χ₂=0`).
- **Reflection `s↔p−s`** (`χ₂` odd since `p≡3 mod4`; `[ρ(p−s) mod p>H]=1−[ρs mod p>H]`):
  `A_full = A + (A − Σ_{[1,H]}χ₂) = 2A − Σ_{[1,H]}χ₂`.
- Equate ⇒ **`A = Σ_{s=1}^{H} χ₂(s)`.** By **Dirichlet's class-number formula** (`p≡3 mod4`):
  `Σ_{s=1}^{(p−1)/2} χ₂(s) = (2−χ₂(2))·h(−p)`. ∎  (Verified: `A=(2−χ₂(2))h`, 134 primes.)

## 3. The remaining identity  `C′ − C = 3·h(−p)`  `[VERIFIED 134 primes, NOT PROVED]`
Let `C′ := Σ_{s∈[1,H], ρs mod p>s} χ₂(s)`. Then `C + C′ = Σ_{s=1}^{H}χ₂(s) = A` (`ρs mod p≠s`), i.e.
```
   C′ − C = Σ_{s=1}^{H} χ₂(s)·sgn(ρs mod p − s)  =  3·h(−p).            (†)  [the one open step]
```
Given `(†)` and `C+C′=A=(2−χ₂(2))h`: `C = (A−3h)/2 = −h(1+χ₂(2))/2`, hence
`S′ = A+C = (3h/2)(1−χ₂(2))` — **P2**. Elementary character-sum manipulation of `(†)` is **circular**
(every `s↔p−s` / `t=ρs` step returns an equivalent form); `(†)` is a **character-twisted class-number
identity** — the `3` is the `ℚ(√−3)` (6th-root ρ) contribution. It needs the analytic class-number /
CM machinery (a generalized Dedekind sum `Σχ₂(s)⌊ρs/p⌋`-type evaluation), not done here.

## 4. Status ledger

| item | grade |
|---|---|
| **P1: `(−1)^N=χ₂(2)`** | **`[PROVED — THEOREM]`** (v2) |
| P2 structure `S′=(3/2)h(−p)(1−χ₂(2))`, `O₊−O₋=h·[p≡3 mod8]` | `[VERIFIED, 134 primes]` |
| `S′=A+C`; `C+C′=A` | `[PROVED]` |
| **`A = Σ_{[1,H]}χ₂ = (2−χ₂(2))h`** | **`[PROVED]`** (bijection + Dirichlet) |
| `C′−C = 3h(−p)`  (†) | `[VERIFIED, NOT PROVED]` — **the single open step** |
| P2 easy `S′=0 ⇒ χ₂(2)=+1` | `[PROVED]` (via P1, unconditional) |
| P2 hard `χ₂(2)=+1 ⇒ S′=0` | reduced to `(†)`; **not yet a theorem** |

**Net:** P2 went from an opaque "non-multiplicative balance" (v38) to a sharp class-number statement —
the flap χ₂-imbalance **is** `h(−p)` — with everything proved except the single twisted class-number
identity `(†) C′−C=3h`. The `p≡7 mod 8` conservation (S′=0) is now "class number × (1−χ₂(2))", one clean
identity short of a full theorem. No leakage/ECDLP content — pure CM/analytic number theory.

## 5. Reproduction
```
python3 scratchpad/prove_P2_hard_v1.py 100 900       # S'=A+C, S'=0 at p=7mod8, involutions all fail
# closed-form check: A=(2-x2)h=sum_[1,H]chi2 ; C=-h(1+x2)/2 ; C'-C=3h ; S'=(3h/2)(1-x2)  (134 primes)
```
Exact integers; `h(−p)` by reduced-form count (validated). Prior: v38 §4, `..._v2.md` (P1 theorem).
