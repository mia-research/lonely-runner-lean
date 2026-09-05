# P1 PROVED as a theorem; P2 easy direction PROVED; P2 hard direction still open

**Date:** 2026-07-21 · Supersedes `..._v1.md` (which had P1 as a verified-but-unproven reduction).
**Result: P1 — `(−1)^N = χ₂(2)`, i.e. `N ≡ μ₂ (mod 2)` — is now a COMPLETE THEOREM.** Every link is a
proof (Gauss's lemma, a multiplication-by-ρ bijection, Eisenstein's lemma, the ⌊2y⌋ identity), each also
exact-verified over all `p≡7 mod 12`, `p<6000`. P2's easy direction is proved (now unconditional); P2's
hard direction (the χ₂ balance) remains the single open lemma.

**Setup.** `p ≡ 7 (mod 12)` prime (so `p≡1 mod6`, `p≡3 mod4`), `H=(p−1)/2`. `ρ∈[2,p−1]` the primitive
6th root of unity (`ρ²−ρ+1≡0`), `β:=ρ² mod p`. `χ₂` = quadratic character. `μ_a := #{s∈[1,H]: (as mod p)
> H}` (Gauss count, `χ₂(a)=(−1)^{μ_a}`). `S(a) := Σ_{s=1}^{H} ⌊as/p⌋`. Flap:
`T⁺ = {s∈[1,H] : cent(s)−cent(ρs) > p/2}`, `N=|T⁺|`, and `μ₂=(p+1)/4` (the Gauss count for 2), with
`χ₂(2)=(−1)^{μ₂}`.

---

## THEOREM (P1).  `(−1)^N = χ₂(2)`  (equivalently `N ≡ μ₂ (mod 2)`, `ORB=N/3` even ⟺ `p≡7 mod8`).

### Step 1 — `N = μ_ρ − M`.  `[PROVED]`
For `s∈[1,H]`, `cent(s)=s`, and `s∈T⁺ ⟺ (ρs mod p) ∈ [(p+1)/2, H+s]` (from `cent(s)−cent(ρs)>p/2`
with `cent(ρs)<0`). Splitting the window,
`N = #{s: ρs mod p ≥ (p+1)/2} − #{s: ρs mod p ≥ H+s+1} = μ_ρ − M`, where
`M := #{s∈[1,H] : (ρs mod p) > H+s}`.

### Step 2 — `μ_ρ` is ODD.  `[PROVED]`
`χ₂(ρ)=ρ^{(p−1)/2}`. For `p≡7 (mod 12)`, `(p−1)/2 ≡ 3 (mod 6)`, so `ρ^{(p−1)/2}=ρ³=−1` (ρ has order 6).
Thus `χ₂(ρ)=−1`, and by Gauss's lemma `μ_ρ` is odd. Hence `N ≡ 1 + M (mod 2)`.

### Step 3 — `M = W` via multiplication by ρ.  `[PROVED]`
Let `W := #{s∈[1,H] : (ρs mod p) < s}`. **Claim:** `s' ↦ ρs' mod p` is a bijection `W → M` (inverse
`ρ⁻¹`). Take `s'∈W`, so `ρs' mod p < s' ≤ H`; put `s = ρs' mod p ∈ [1,H]`. Then
`ρs mod p = ρ²s' mod p = βs' mod p`, and since `βs' ≡ ρs'−s'` with `(ρs' mod p)−s' ∈ (−H,0)`, we get
`βs' mod p = (ρs' mod p) − s' + p`. Therefore
`(ρs mod p) − s = (ρs' mod p − s' + p) − (ρs' mod p) = p − s' > H` (as `s'≤H`), i.e. `s∈M`.
The map `ρ` is injective on `F_p^*` and the reverse computation sends `M→W`, so it is a bijection.
**Hence `M = W`, and `N ≡ 1 + W (mod 2)`.**

### Step 4 — `W = S(ρ) − S(ρ−1)`.  `[PROVED]`
Since `ρ²≡ρ−1 (mod p)` and `2≤ρ≤p−1`, **`β = ρ−1` as integers**. For each `s∈[1,H]`, with `x=ρs/p` and
`δ=s/p∈(0,½)`, `⌊x⌋−⌊x−δ⌋ = 1` iff `{x}<δ` iff `(ρs mod p)<s` (and `=0` otherwise; no boundary case
since `ρs≢s`). Summing, `W = Σ_{s=1}^{H}(⌊ρs/p⌋−⌊(ρ−1)s/p⌋) = S(ρ) − S(ρ−1)`, so
`W ≡ S(ρ)+S(ρ−1) (mod 2)`.

### Step 5 — parity of `S(a)`.  `[PROVED, standard]`
- **odd `a`:** Eisenstein's lemma gives `S(a) ≡ μ_a (mod 2)`, hence `(−1)^{S(a)} = χ₂(a)`.
- **even `a=2b`:** `⌊2bs/p⌋ = 2⌊bs/p⌋ + [(bs mod p)>H]`, so `S(2b)=2S(b)+μ_b ≡ μ_b (mod 2)`, hence
  `(−1)^{S(2b)} = χ₂(b) = χ₂(a/2)`.

### Step 6 — assemble.  `[PROVED]`
`χ₂(β)=β^{(p−1)/2}=1` (since `(p−1)/2≡0 mod 3`), i.e. `χ₂(ρ−1)=+1`; and `χ₂(ρ)=−1` (Step 2). `ρ` and
`ρ−1` have opposite parity. Using χ₂ multiplicativity `χ₂(x)=χ₂(2)χ₂(x/2)`:

- **`ρ` even:** `(−1)^{S(ρ−1)}=χ₂(ρ−1)=+1`; `(−1)^{S(ρ)}=χ₂(ρ/2)=χ₂(ρ)/χ₂(2)=−χ₂(2)`. ⇒ `(−1)^W=−χ₂(2)`.
- **`ρ` odd:** `(−1)^{S(ρ)}=χ₂(ρ)=−1`; `(−1)^{S(ρ−1)}=χ₂((ρ−1)/2)=χ₂(ρ−1)/χ₂(2)=+1/χ₂(2)=χ₂(2)`.
  ⇒ `(−1)^W=(−1)·χ₂(2)=−χ₂(2)`.

**Both cases: `(−1)^W = −χ₂(2)`.** With `N ≡ 1+W` (Steps 1–3),
```
        (−1)^N = (−1)^{1+W} = −(−1)^W = −(−χ₂(2)) = χ₂(2).            ∎
```
Equivalently `N ≡ μ₂ (mod 2)` and `(−1)^{ORB}=χ₂(2)` (`ORB=N/3`, `N≡ORB mod 2`): **`ORB` even ⟺ `p≡7 mod 8`.**

**Verification:** every step + the closed forms `(−1)^W=−χ₂(2)`, `(−1)^N=χ₂(2)` hold for all
`p≡7 mod 12`, `p<6000` (194 primes); both roots of `x²−x+1` give the same `W` parity (well-defined).

---

## P2 — easy direction PROVED (unconditional); hard direction OPEN

`χ₂` is constant on μ₃-orbits (`χ₂(β)=+1`), so on the `ORB=N/3` free μ₃-orbits of `T⁺`,
`S′ := Σ_{s∈T⁺}χ₂(s) = 3(O₊−O₋)`, `O₊+O₋=ORB`.

- **PROVED (now unconditional, via P1):** if `χ₂(2)=−1` then `N` is odd (P1) ⇒ `ORB` odd ⇒ `O₊−O₋` odd ⇒
  `S′≠0`. That is **`S′=0 ⇒ χ₂(2)=+1`**.  `[PROVED]`
- **OPEN:** `χ₂(2)=+1 ⇒ O₊=O₋` (the exact balance). `[VERIFIED, NOT PROVED]` — the multiplicative pairing
  candidate (×`c`, `c²=2`) does not preserve `T⁺`; it needs a Jacobi-sum evaluation of `S′` or a
  non-multiplicative involution on the μ₃-orbits. **This is the single remaining gap** in the
  `p≡7 mod 8` conservation.

---

## Status ledger

| item | grade |
|---|---|
| **P1: `(−1)^N=χ₂(2)`** | **`[PROVED — THEOREM]`** (Steps 1–6, all proved + verified) |
| `M=W` (mult-by-ρ bijection) | `[PROVED]` |
| `W=S(ρ)−S(ρ−1)`, `(−1)^W=−χ₂(2)` | `[PROVED]` (Eisenstein + doubling identity) |
| P2 easy: `S′=0 ⇒ χ₂(2)=+1` | `[PROVED]` (unconditional, via P1) |
| P2 hard: `χ₂(2)=+1 ⇒ O₊=O₋` | `[VERIFIED, NOT PROVED]` — the one open lemma |

**The `p≡7 mod 8` flap-parity law is now a THEOREM** (`ORB` even ⟺ `p≡7 mod8`). The 35/35 conservation
(the χ₂-balance `S′=0`) is proved in the `⇒` direction; its `⇐` direction is the last remaining lemma.
No leakage/ECDLP content — pure CM lattice geometry (as flagged throughout).

## Reproduction
```
python3 scratchpad/prove_flap_lemmas_v1.py 100 2000    # N=mu_rho-M ; reduction
python3 scratchpad/prove_flap_lemmas_v2.py 100 1600    # (star), P2 O+/O-
# step-by-step proof verification (beta=rho-1, W=S(rho)-S(rho-1), Eisenstein, S(2b)=2S(b)+mu_b,
#   chi2(rho)=-1, chi2(beta)=+1, M=W bijection, (-1)^W=-chi2(2), (-1)^N=chi2(2)) : scratchpad one-liners.
```
Exact integers throughout. Prior: v38 §3 (two-lemma reduction), `..._proofstatus_v1.md` (the reduction).
