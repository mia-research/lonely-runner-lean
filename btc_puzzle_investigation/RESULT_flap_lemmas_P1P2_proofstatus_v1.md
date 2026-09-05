# P1 / P2 (the p≡7 mod 8 flap conservation): proof STATUS — reduced, not yet theorems

**Date:** 2026-07-21 · **Scripts:** `scratchpad/prove_flap_lemmas_v1.py`, `_v2.py` (exact ints).
Target: prove P1 (`N ≡ μ₂ mod 2`) and P2 (`Σ_{T⁺}χ₂ = 0 ⟺ χ₂(2)=1`) from `masked_structure_findings_v38.md`.
**Honest verdict: I PROVED the reductions and P2's easy direction; I did NOT close the two final
lemmas. They are verified exactly but remain named Dedekind-reciprocity gaps. NOT theorems yet.**
(Per `feedback_proof_not_test`: a verified reduction is not a proof; the gap is named, not papered over.)

Setup: `p ≡ 7 mod 12` (`≡1 mod6`, `≡3 mod4`), `H=(p−1)/2`, `ρ` primitive 6th root (`ρ²−ρ+1≡0`),
`β=ρ²` (cube root), `γ=ρ⁴=β⁻¹`. `T⁺={s∈[1,H]: cent(s)−cent(ρs)>p/2}`, `N=|T⁺|=3·ORB`, `μ₂=(p+1)/4`.

---

## 1. P1 — reduced to ONE lattice lemma by PROVED steps  `[PROVED reduction]`

All steps exact-verified for every `p≡7 mod12` in `[100,3000)`:

1. **`N = μ_ρ − M`**, `μ_ρ = #{s∈[1,H]: ρs mod p > H}` (Gauss-lemma count), `M = #{s∈[1,H]:
   (ρs mod p)−s > H}`. `[VERIFIED exact]`
2. **`μ_ρ` is ODD**: `χ₂(ρ) = ρ^{(p−1)/2} = ρ³ = −1` (since `(p−1)/2 ≡ 3 mod 6` for `p≡7 mod12`), and
   Gauss's lemma `χ₂(ρ)=(−1)^{μ_ρ}`. `[PROVED]`
3. **`M = K`** where `K = #{s∈[1,H]: γs mod p + s ≤ H}` `[VERIFIED exact]`; and the boundary algebra gives
   `N ≡ 1 + K (mod 2)` (`H` odd, `μ_ρ` odd). `[PROVED given step 3]`
4. **`K ≡ W (mod 2)`**, `W = #{s∈[1,H]: ρs mod p < s}` — via the identity `δ := −γ = −β⁻¹ = ρ` (a primitive
   6th root), which turns `K`'s wrap-count into the clean **descent count** `W`. `[PROVED + VERIFIED]`

**⇒ P1 ⟺ the single lemma**
```
  W = #{ s ∈ [1,(p−1)/2] : (ρ·s mod p) < s }  ≡  [p ≡ 7 mod 8]  (mod 2)        (★)
```
(because `N ≡ 1+W` and `μ₂ = (p+1)/4 ≡ [p≡7 mod8]... ` ⇒ `N≡μ₂ ⟺ W≡[p≡7 mod8]`). **Verified exact,
all `p≡7 mod12`, `p<3000`.** This is **sharper than v38** (the flap count collapses to a pure 6th-root
*descent* count). *It holds with NO `n`-prime hypothesis — P1 is pure lattice geometry.*

**The remaining gap (★).** `[VERIFIED, NOT PROVED]`. The natural reflection `s↦H+1−s` does **not** act on
`W`'s set (membership not preserved), so `(★)` is not a one-line pairing. What IS known toward it: the
*full-range* descent count `#{s∈[1,p−1]: ρs mod p<s} = H` exactly (via `s↦p−s`), but that symmetry only
gives `W+W'=H` (opposite parities on the two halves), not `W`'s parity — the `χ₂(2)=p mod 8` content is a
genuine **boundary/second-order effect** (consistent with v38 §2: the Dedekind main term is a fixed CM
value with no `χ₂(2)`). `(★)` needs a Dedekind–Rademacher reciprocity for the 6th root, not executed here.

---

## 2. P2 — easy direction PROVED (given P1); hard direction reduced  `[PARTIAL]`

- **χ₂ is constant on μ₃-orbits:** `χ₂(β)=β^{(p−1)/2}=1` (`(p−1)/2≡0 mod 3`). So on the `ORB=N/3` free
  μ₃-orbits of `T⁺`, `S′ := Σ_{s∈T⁺}χ₂(s) = 3(O₊−O₋)`, `O₊+O₋=ORB`. `[PROVED]`
- **P2 easy direction — PROVED (given P1):** if `χ₂(2)=−1` then by P1 `N` is odd ⇒ `ORB` odd ⇒ `O₊−O₋`
  odd ⇒ `S′≠0`. I.e. **`S′=0 ⇒ χ₂(2)=+1`** is proved (modulo `(★)`). `[PROVED | P1]` (verified exact).
- **P2 hard direction — reduced, NOT proved:** `χ₂(2)=+1 ⇒ O₊=O₋` (exact balance). `[VERIFIED, NOT
  PROVED]`. The candidate multiplicative pairing (×`c`, `c²=2`) does **NOT** preserve `T⁺` (checked) —
  confirming v38's "the balance is non-multiplicative." Remaining as a Jacobi-sum evaluation of `S′` or a
  non-multiplicative involution on the μ₃-orbits. Not executed here.

---

## 3. What is and isn't done

| item | grade |
|---|---|
| P1 reduction `N ≡ 1+W (mod 2)` via Gauss-lemma steps | **`[PROVED reduction]`** (verified exact) |
| P1 ⟺ `(★)` `W≡[p≡7 mod8]` | **`[PROVED equivalence]`**; `(★)` itself **`[VERIFIED, NOT PROVED]`** |
| P2 `χ₂` const on μ₃-orbits; `S′=3(O₊−O₋)` | **`[PROVED]`** |
| P2 easy: `S′=0 ⇒ χ₂(2)=+1` | **`[PROVED given P1]`** |
| P2 hard: `χ₂(2)=+1 ⇒ O₊=O₋` | **`[VERIFIED, NOT PROVED]`** (mult. candidate refuted) |

**Neither P1 nor P2 is a theorem yet.** Both now rest on **two named classical lemmas**: `(★)` the 6th-root
descent-count parity, and the P2-hard μ₃-orbit χ₂-balance. Each is exact-verified and self-contained; each
needs a genuine reciprocity/Jacobi argument that I did not complete. The 35/35 `p≡7 mod 8` conservation
therefore stays **EMPIRICAL** — the reduction is sharper, the door is narrower, but it is not closed.

---

## 4. Reproduction
```
python3 scratchpad/prove_flap_lemmas_v1.py 100 2000   # N=mu_rho-M, N=1+K mod2, all PROVED steps
python3 scratchpad/prove_flap_lemmas_v2.py 100 1600   # (★) W==[p=7mod8]; P2 O+/O-; reflection fails
```
Exact integers; no float. Prior: v38 §3–§4 (the two-lemma reduction this sharpens).
