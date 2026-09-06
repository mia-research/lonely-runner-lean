import LonelyRunner.LRC.SmallN.IntLRC_7_BS.Defs
import LonelyRunner.LRC.SmallN.IntLRC_7_BS.PrimeFiltering

/-!
# n = 7 (Barajas–Serra) — Supporting Lemmas 5–9

Source: `sources_barajas_serra_2008.txt`, lines 364–506.

These lemmas provide the combinatorial tools used by the §6 case analysis
(|A|=5). Lemma 5 is the main pigeonhole for `ℓ(A₁)+ℓ(A₂)+ℓ(A₄) ≤ 5`.

**Not on the path to `intLRC_seven`:** `lemma4_i_half`, `lemma4_i_eq`,
`lemma4_i_le`, `lemma6_330`, `lemma6_402`, `lemma6_420`, `lemma6_501`,
`lemma6_510`. They are faithful transcriptions of the paper's numbered lemmas and
are proved, but the case analyses ended up going through other routes. Kept for
correspondence with the source; do not assume a change here can break the main
theorem, and do not assume they are exercised by it either.
-/

open Finset

namespace IntLRC7BS

/-- An interval `{a, a+1, ..., a+ℓ-1}` in `ZMod 7` avoids `{0, 6}` under shift `s·k`:
for each `j < ℓ`, `(a + j + s·k) ∉ {0, 6}`. -/
def intervalAvoids (a : ZMod 7) (ℓ : ℕ) (s k : ZMod 7) : Prop :=
  ∀ j : Fin ℓ, (a + (j.val : ZMod 7) + s * k) ∉ ({0, 6} : Finset (ZMod 7))

instance (a : ZMod 7) (ℓ : ℕ) (s k : ZMod 7) : Decidable (intervalAvoids a ℓ s k) :=
  inferInstanceAs (Decidable (∀ j : Fin ℓ, _))

set_option maxHeartbeats 3200000 in
/-- **Lemma 5, safe version (BS L388, sum ≤ 5, excluding 3 exceptional triples).**
Three intervals in ZMod 7 with total length ≤ 5 can be simultaneously shifted
(by `k`, `2k`, `4k`) to avoid `{0,6}`, unless `(ℓ₁,ℓ₂,ℓ₄) ∈ {(3,1,1),(1,3,1),(1,1,3)}`.
The excluded triples are BS's Lemma 5 exception; handled by Lemma 6. -/
theorem lemma5_avoids (a₁ a₂ a₄ : ZMod 7) (ℓ₁ ℓ₂ ℓ₄ : ℕ)
    (h₁ : ℓ₁ ≤ 5) (h₂ : ℓ₂ ≤ 5) (h₄ : ℓ₄ ≤ 5) (hsum : ℓ₁ + ℓ₂ + ℓ₄ ≤ 5)
    (hexc : ¬ (ℓ₁ = 3 ∧ ℓ₂ = 1 ∧ ℓ₄ = 1))
    (hexc2 : ¬ (ℓ₁ = 1 ∧ ℓ₂ = 3 ∧ ℓ₄ = 1))
    (hexc3 : ¬ (ℓ₁ = 1 ∧ ℓ₂ = 1 ∧ ℓ₄ = 3)) :
    ∃ k : ZMod 7,
      intervalAvoids a₁ ℓ₁ 1 k ∧
      intervalAvoids a₂ ℓ₂ 2 k ∧
      intervalAvoids a₄ ℓ₄ 4 k := by
  interval_cases ℓ₁ <;> interval_cases ℓ₂ <;> interval_cases ℓ₄ <;>
    simp_all (config := { decide := true }) [intervalAvoids] <;>
    revert a₁ a₂ a₄ <;> decide

/-- **Lemma 5 exceptional triple (3,1,1).** BS shows the `(ℓ₁,ℓ₂,ℓ₄)=(3,1,1)`
case fails only when `ẽ(d,d') = 2i - j ∈ {2,4}` (where `i = q(A₂)`, `j = q(A₄)`).
With that exception ruled out (`2·a₂ - a₄ ∉ {2,4}`), the avoidance holds. -/
theorem lemma5_avoids_311 (a₁ a₂ a₄ : ZMod 7)
    (hexc : (2 * a₂ - a₄) ∉ ({2, 4} : Finset (ZMod 7))) :
    ∃ k : ZMod 7,
      intervalAvoids a₁ 3 1 k ∧
      intervalAvoids a₂ 1 2 k ∧
      intervalAvoids a₄ 1 4 k := by
  revert hexc; revert a₁ a₂ a₄; decide

/-- **Lemma 5 (BS L388), faithful form.** `A₁` is the most popular class, so
`ℓ₂ ≤ ℓ₁` and `ℓ₄ ≤ ℓ₁`; this rules out the spurious `(1,3,1)`/`(1,1,3)` triples,
leaving `(3,1,1)` as the only exception. Folding in its `ẽ ∉ {2,4}` carve-out
(`lemma5_avoids_311`) gives the unconditional avoidance BS states. -/
theorem lemma5 (a₁ a₂ a₄ : ZMod 7) (ℓ₁ ℓ₂ ℓ₄ : ℕ)
    (h₁ : ℓ₁ ≤ 5) (hsum : ℓ₁ + ℓ₂ + ℓ₄ ≤ 5)
    (h21 : ℓ₂ ≤ ℓ₁) (h41 : ℓ₄ ≤ ℓ₁)
    (hexc : ℓ₁ = 3 ∧ ℓ₂ = 1 ∧ ℓ₄ = 1 → (2 * a₂ - a₄) ∉ ({2, 4} : Finset (ZMod 7))) :
    ∃ k : ZMod 7,
      intervalAvoids a₁ ℓ₁ 1 k ∧
      intervalAvoids a₂ ℓ₂ 2 k ∧
      intervalAvoids a₄ ℓ₄ 4 k := by
  by_cases h311 : ℓ₁ = 3 ∧ ℓ₂ = 1 ∧ ℓ₄ = 1
  · obtain ⟨e₁, e₂, e₄⟩ := h311
    subst e₁; subst e₂; subst e₄
    exact lemma5_avoids_311 a₁ a₂ a₄ (hexc ⟨rfl, rfl, rfl⟩)
  · exact lemma5_avoids a₁ a₂ a₄ ℓ₁ ℓ₂ ℓ₄ h₁ (by omega) (by omega) hsum
      (by tauto) (by rintro ⟨rfl, rfl, rfl⟩; omega) (by rintro ⟨rfl, rfl, rfl⟩; omega)

/-- **Lemma 6 (iii) (BS L429).** `(ℓ₁,ℓ₂,ℓ₄)=(3,3,0)`: with `A₁` normalized to
`q(A₁)={1,2,3}`, some `λ_k∈Λ₀` (`k∈{0,1,2}`) makes both `A₁` and the length-3
`A₂` avoid `{0,6}`. No `ẽ` condition needed. -/
theorem lemma6_330 (a₂ : ZMod 7) :
    ∃ k : ZMod 7, intervalAvoids 1 3 1 k ∧ intervalAvoids a₂ 3 2 k := by
  revert a₂; decide

/-- **Lemma 6 (ii), (4,0,2) (BS L426).** `A₁` length 4 at `{1,2,3,4}`, `A₄`
length 2. Unconditional: one of `{i,i+1}`, `{i+4,i+5}` avoids `{0,6}`. -/
theorem lemma6_402 (a₄ : ZMod 7) :
    ∃ k : ZMod 7, intervalAvoids 1 4 1 k ∧ intervalAvoids a₄ 2 4 k := by
  revert a₄; decide

/-- **Lemma 6 (ii), (4,2,0) (BS L426).** `A₁` length 4, `A₂` length 2 at
`{a₂,a₂+1}`. Needs `ẽ(d,d')≠4`, i.e. `2−a₂ ≠ 4` ⟺ `a₂ ≠ 5` (`d∈A₁`, `q(d)=1`;
`d'∈A₂∩q⁻¹(a₂)`). -/
theorem lemma6_420 (a₂ : ZMod 7) (he : (2 - a₂) ≠ 4) :
    ∃ k : ZMod 7, intervalAvoids 1 4 1 k ∧ intervalAvoids a₂ 2 2 k := by
  revert he; revert a₂; decide

/-- **Lemma 6 (i), (5,0,1) (BS L422).** `A₁` length 5 at `{1,..,5}`, `A₄`
length 1. Needs `ẽ(d,d')∉{4,6}`, i.e. `2·a₄−1 ∉ {4,6}` ⟺ `a₄ ∉ {0,6}`. -/
theorem lemma6_501 (a₄ : ZMod 7) (he : (2 * a₄ - 1) ∉ ({4, 6} : Finset (ZMod 7))) :
    ∃ k : ZMod 7, intervalAvoids 1 5 1 k ∧ intervalAvoids a₄ 1 4 k := by
  revert he; revert a₄; decide

/-- **Lemma 6 (i), (5,0,1) general start (BS L422).** Like `lemma6_501` but with
arbitrary `A₁` window start `a_m` (after r⁻¹ normalization). Needs
`ẽ(d_ref,d')∉{4,6}`, i.e. `2·a₄−a_m ∉ {4,6}`. -/
theorem lemma6_501_gen (a_m a₄ : ZMod 7)
    (he : (2 * a₄ - a_m) ∉ ({4, 6} : Finset (ZMod 7))) :
    ∃ k : ZMod 7, intervalAvoids a_m 5 1 k ∧ intervalAvoids a₄ 1 4 k := by
  revert he; revert a_m a₄; decide

/-- **Lemma 6 (i), (5,1,0) (BS L422).** `A₁` length 5, `A₂` length 1. Needs
`ẽ(d,d')∉{2,3}`, i.e. `2−a₂ ∉ {2,3}` ⟺ `a₂ ∉ {0,6}`. -/
theorem lemma6_510 (a₂ : ZMod 7) (he : (2 - a₂) ∉ ({2, 3} : Finset (ZMod 7))) :
    ∃ k : ZMod 7, intervalAvoids 1 5 1 k ∧ intervalAvoids a₂ 1 2 k := by
  revert he; revert a₂; decide

/-- `S ⊆ {a, a+1, ..., a+L-1}` in `ZMod 7` — represents `ℓ(S) ≤ L`, i.e. `q(S)`
fits in a difference-1 arithmetic progression of length `L`. -/
def fitsInterval (S : Finset (ZMod 7)) (a : ZMod 7) (L : ℕ) : Prop :=
  ∀ x ∈ S, ∃ j : Fin L, x = a + (j.val : ZMod 7)

instance (S : Finset (ZMod 7)) (a : ZMod 7) (L : ℕ) : Decidable (fitsInterval S a L) :=
  inferInstanceAs (Decidable (∀ x ∈ S, _))

/-- `ℓ(S) ≤ L` is monotone in `L`: a length-`L` AP fit is also a length-`L'` fit
for `L ≤ L'`. Lets the differing length bounds (Lemma 9(i): `ℓ≤2`, 9(ii): `ℓ≤3`)
be combined uniformly. -/
theorem fitsInterval_mono {S : Finset (ZMod 7)} {a : ZMod 7} {L L' : ℕ}
    (hLL' : L ≤ L') (h : fitsInterval S a L) : fitsInterval S a L' :=
  fun x hx => let ⟨j, hj⟩ := h x hx; ⟨⟨j.val, lt_of_lt_of_le j.isLt hLL'⟩, hj⟩

set_option maxRecDepth 4000 in
/-- **Remark 8 (ii) combinatorial core (BS L478).** Three values in `ZMod 7` whose
pairwise differences all lie in `{0,1,2,5,6} = {−2,…,2}` fit in a length-3 AP.
(Max clique in the `{±1,±2}` Cayley graph on `ZMod 7` is a 3-term interval.)
Stated for 3 explicit elements — matches `B = {b₁,b₂,b₃}` in Lemma 9. -/
theorem remark8_ii_core3 (v₁ v₂ v₃ : ZMod 7)
    (h₁₂ : v₁ - v₂ ∈ ({0, 1, 2, 5, 6} : Finset (ZMod 7)))
    (h₁₃ : v₁ - v₃ ∈ ({0, 1, 2, 5, 6} : Finset (ZMod 7)))
    (h₂₃ : v₂ - v₃ ∈ ({0, 1, 2, 5, 6} : Finset (ZMod 7))) :
    ∃ a : ZMod 7, fitsInterval ({v₁, v₂, v₃} : Finset (ZMod 7)) a 3 := by
  revert h₁₂ h₁₃ h₂₃; revert v₁ v₂ v₃; decide

set_option maxRecDepth 4000 in
/-- **Remark 8 (i) combinatorial core, `k = 1` (BS L476).** Three `ZMod 7` values
whose pairwise differences all lie in `{0,1,6} = {−1,0,1}` fit in a length-2 AP.
(Used via `qz_subxy_carry`: `q(X−X)⊂{0,6}` ⇒ pairwise `qz`-diffs ∈ `{−1,0,1}`.) -/
theorem remark8_i_core3 (v₁ v₂ v₃ : ZMod 7)
    (h₁₂ : v₁ - v₂ ∈ ({0, 1, 6} : Finset (ZMod 7)))
    (h₁₃ : v₁ - v₃ ∈ ({0, 1, 6} : Finset (ZMod 7)))
    (h₂₃ : v₂ - v₃ ∈ ({0, 1, 6} : Finset (ZMod 7))) :
    ∃ a : ZMod 7, fitsInterval ({v₁, v₂, v₃} : Finset (ZMod 7)) a 2 := by
  revert h₁₂ h₁₃ h₂₃; revert v₁ v₂ v₃; decide

/-- Carry bridge: if `q(u−v) ∈ {0,6}` then `q(u) − q(v) ∈ {0,1,6}` (= `{−1,0,1}`).
From `qz_subxy_carry` (`q(u−v) = q(u) − q(v) + c`, `c ∈ {0,6}`). -/
theorem qz_diff_mem_06 (m : ℕ) (u v : ℤ) (h : qz m (u - v) ∈ ({0, 6} : Finset (ZMod 7))) :
    qz m u - qz m v ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
  obtain ⟨c, hc, hcq⟩ := qz_subxy_carry m u v
  have hd : qz m u - qz m v = qz m (u - v) - c := by linear_combination -hcq
  rw [hd]
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h <;> rw [h] <;> rcases hc with rfl | rfl <;> decide

/-- Carry bridge: if `q(u−v) ∈ {0,1,5,6}` then `q(u) − q(v) ∈ {0,1,2,5,6}` (`= {−2,…,2}`). -/
theorem qz_diff_mem_0156 (m : ℕ) (u v : ℤ)
    (h : qz m (u - v) ∈ ({0, 1, 5, 6} : Finset (ZMod 7))) :
    qz m u - qz m v ∈ ({0, 1, 2, 5, 6} : Finset (ZMod 7)) := by
  obtain ⟨c, hc, hcq⟩ := qz_subxy_carry m u v
  have hd : qz m u - qz m v = qz m (u - v) - c := by linear_combination -hcq
  rw [hd]
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h | h | h <;> rw [h] <;> rcases hc with rfl | rfl <;> decide

/-- **Remark 8 (i) on integers (`k=1`).** If `q(bᵢ−bⱼ) ⊂ {0,6}` for the three
pairwise differences, then `ℓ({q(b₁),q(b₂),q(b₃)}) ≤ 2`. The integer-difference
form actually used by the §6 cases (after a multiplier sends `q(B−B) ⊂ {0,6}`). -/
theorem remark8_i_int (m : ℕ) (b₁ b₂ b₃ : ℤ)
    (h12 : qz m (b₁ - b₂) ∈ ({0, 6} : Finset (ZMod 7)))
    (h13 : qz m (b₁ - b₃) ∈ ({0, 6} : Finset (ZMod 7)))
    (h23 : qz m (b₂ - b₃) ∈ ({0, 6} : Finset (ZMod 7))) :
    ∃ a : ZMod 7, fitsInterval ({qz m b₁, qz m b₂, qz m b₃} : Finset (ZMod 7)) a 2 :=
  remark8_i_core3 _ _ _ (qz_diff_mem_06 m _ _ h12) (qz_diff_mem_06 m _ _ h13)
    (qz_diff_mem_06 m _ _ h23)

/-- **Remark 8 (ii) on integers.** If `q(bᵢ−bⱼ) ⊂ {0,1,5,6}` for the three pairwise
differences, then `ℓ({q(b₁),q(b₂),q(b₃)}) ≤ 3`. -/
theorem remark8_ii_int (m : ℕ) (b₁ b₂ b₃ : ℤ)
    (h12 : qz m (b₁ - b₂) ∈ ({0, 1, 5, 6} : Finset (ZMod 7)))
    (h13 : qz m (b₁ - b₃) ∈ ({0, 1, 5, 6} : Finset (ZMod 7)))
    (h23 : qz m (b₂ - b₃) ∈ ({0, 1, 5, 6} : Finset (ZMod 7))) :
    ∃ a : ZMod 7, fitsInterval ({qz m b₁, qz m b₂, qz m b₃} : Finset (ZMod 7)) a 3 :=
  remark8_ii_core3 _ _ _ (qz_diff_mem_0156 m _ _ h12) (qz_diff_mem_0156 m _ _ h13)
    (qz_diff_mem_0156 m _ _ h23)

/-- **Lemma 4 (i) (BS L366), `r(y)=2r(x)` case.** The quantity `ẽ(x,y)=2q(x)−q(y)`
is invariant under a level-`h` multiplier `1+k·7^{m-h}`, provided `x,y` share level
`h` with `r(y)=2r(x)` (here as `(y/7^h) = 2·(x/7^h)` in `ZMod 7`). Immediate from
`qz_lambda`: the two shifts `k·r(x)`, `k·r(y)=2k·r(x)` cancel in `2q(λx)−q(λy)`. -/
theorem lemma4_i (m h : ℕ) (hhm : h ≤ m) (k x y : ℤ)
    (hx : (7 : ℤ) ^ h ∣ x) (hy : (7 : ℤ) ^ h ∣ y)
    (hr : ((y / 7 ^ h : ℤ) : ZMod 7) = 2 * ((x / 7 ^ h : ℤ) : ZMod 7)) :
    2 * qz m ((1 + k * 7 ^ (m - h)) * x) - qz m ((1 + k * 7 ^ (m - h)) * y)
      = 2 * qz m x - qz m y := by
  have := qz_lin_invariant m h hhm k x y 2 (-1) hx hy (by rw [hr]; ring)
  linear_combination this

/-- **Lemma 4 (i), `r(x)=2r(y)` case.** `ẽ(x,y)=2q(y)−q(x)` invariant under `Λ_h`. -/
theorem lemma4_i_half (m h : ℕ) (hhm : h ≤ m) (k x y : ℤ)
    (hx : (7 : ℤ) ^ h ∣ x) (hy : (7 : ℤ) ^ h ∣ y)
    (hr : ((x / 7 ^ h : ℤ) : ZMod 7) = 2 * ((y / 7 ^ h : ℤ) : ZMod 7)) :
    2 * qz m ((1 + k * 7 ^ (m - h)) * y) - qz m ((1 + k * 7 ^ (m - h)) * x)
      = 2 * qz m y - qz m x := by
  have := qz_lin_invariant m h hhm k x y (-1) 2 hx hy (by rw [hr]; ring)
  linear_combination this

/-- **Lemma 4 (i), `r(y)=r(x)` case.** `ẽ(x,y)=q(x)−q(y)` invariant under `Λ_h`. -/
theorem lemma4_i_eq (m h : ℕ) (hhm : h ≤ m) (k x y : ℤ)
    (hx : (7 : ℤ) ^ h ∣ x) (hy : (7 : ℤ) ^ h ∣ y)
    (hr : ((y / 7 ^ h : ℤ) : ZMod 7) = ((x / 7 ^ h : ℤ) : ZMod 7)) :
    qz m ((1 + k * 7 ^ (m - h)) * x) - qz m ((1 + k * 7 ^ (m - h)) * y)
      = qz m x - qz m y := by
  have := qz_lin_invariant m h hhm k x y 1 (-1) hx hy (by rw [hr]; ring)
  linear_combination this

/-- **BS Lemma 4 (i), full form (all levels `i ≤ j`).** `qz_lin_invariant` only
covers a multiplier at the *exact* level `j = ν(x) = ν(y)`; BS's Lemma 4 (i)
asserts invariance for every `λ ∈ Λ_i` with `i ≤ j`. This folds in the `i < j`
case via `qz_higher_inert` (both `x, y` sit at level `≥ i+1`, so a `Λ_i`
multiplier leaves their arcs — hence any linear combination — unchanged). The
linear-combination hypothesis `a·r_j(x) + b·r_j(y) = 0` is only consumed at the
boundary `i = j`; it is vacuously respected below. Choosing `(a,b) = (2,-1)`,
`(-1,2)`, `(1,-1)` recovers the three `ẽ` branches of (13). -/
theorem lemma4_i_le (m i j : ℕ) (hij : i ≤ j) (hjm : j ≤ m) (k x y : ℤ) (a b : ZMod 7)
    (hx : (7 : ℤ) ^ j ∣ x) (hy : (7 : ℤ) ^ j ∣ y)
    (hab : a * ((x / 7 ^ j : ℤ) : ZMod 7) + b * ((y / 7 ^ j : ℤ) : ZMod 7) = 0) :
    a * qz m ((1 + k * 7 ^ (m - i)) * x) + b * qz m ((1 + k * 7 ^ (m - i)) * y)
      = a * qz m x + b * qz m y := by
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact qz_lin_invariant m i hjm k x y a b hx hy hab
  · have him : i ≤ m := le_trans (le_of_lt hlt) hjm
    rw [qz_higher_inert m i him k x (dvd_trans (pow_dvd_pow 7 (by omega)) hx),
        qz_higher_inert m i him k y (dvd_trans (pow_dvd_pow 7 (by omega)) hy)]

/-- **Lemma 9 (i) (BS L482), `h < m` form.** Three integers `b₁,b₂,b₃` whose
differences `b₁−b₃`, `b₂−b₃` have DISTINCT valuations `< m`: there is a unit
multiplier `lam` compressing `q(lam·B)` into a length-2 arithmetic progression
(`ℓ(lam·B) ≤ 2`). Proof: `qz_retarget_two` sends both `q(lam(b₁−b₃))` and
`q(lam(b₂−b₃))` to `0`; the three carry bridges (`qz_subxy_carry`) then force all
pairwise `q`-differences into `{−1,0,1}`, and `remark8_i_core3` concludes.

(BS's `ν(B)={0}` / equal-residue context is not needed for this conclusion — only
the difference valuations matter. The `ν=m` edge case of BS's 9(i) is separate.) -/
theorem lemma9_i (m hx hy : ℕ) (b₁ b₂ b₃ : ℤ)
    (hxm : hx < m) (hym : hy < m) (hne : hx ≠ hy)
    (hxd : (7 : ℤ) ^ hx ∣ (b₁ - b₃)) (hxd' : ¬ (7 : ℤ) ^ (hx + 1) ∣ (b₁ - b₃))
    (hyd : (7 : ℤ) ^ hy ∣ (b₂ - b₃)) (hyd' : ¬ (7 : ℤ) ^ (hy + 1) ∣ (b₂ - b₃)) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∃ a : ZMod 7,
      fitsInterval ({qz m (lam * b₁), qz m (lam * b₂), qz m (lam * b₃)}
        : Finset (ZMod 7)) a 2 := by
  -- retarget both differences to q = 0
  obtain ⟨lam, hlam, hq1, hq2⟩ : ∃ lam, ¬ (7 : ℤ) ∣ lam ∧
      qz m (lam * (b₁ - b₃)) = 0 ∧ qz m (lam * (b₂ - b₃)) = 0 := by
    rcases lt_or_gt_of_ne hne with h | h
    · obtain ⟨lam, hu, hqy, hqx⟩ :=
        qz_retarget_two m hy hx hym h (b₂ - b₃) (b₁ - b₃) hyd hyd' hxd hxd' 0 0
      exact ⟨lam, hu, hqx, hqy⟩
    · obtain ⟨lam, hu, hqx, hqy⟩ :=
        qz_retarget_two m hx hy hxm h (b₁ - b₃) (b₂ - b₃) hxd hxd' hyd hyd' 0 0
      exact ⟨lam, hu, hqx, hqy⟩
  refine ⟨lam, hlam, remark8_i_int m (lam * b₁) (lam * b₂) (lam * b₃) ?_ ?_ ?_⟩
  · -- q(lam·b₁ − lam·b₂) ∈ {0,6}: carry of the two retargeted zeros
    obtain ⟨c, hc, hcq⟩ := qz_subxy_carry m (lam * (b₁ - b₃)) (lam * (b₂ - b₃))
    rw [hq1, hq2, show lam * (b₁ - b₃) - lam * (b₂ - b₃) = lam * b₁ - lam * b₂ from by ring] at hcq
    rw [hcq]; rcases hc with rfl | rfl <;> decide
  · rw [show lam * b₁ - lam * b₃ = lam * (b₁ - b₃) from by ring, hq1]; decide
  · rw [show lam * b₂ - lam * b₃ = lam * (b₂ - b₃) from by ring, hq2]; decide

/-- **Lemma 9 (i), ν=m edge (BS L487).** When one difference is at the TOP level
`m`, the standard two-target retarget (`qz_retarget_two`) is unavailable (it needs
both levels `< m`). Instead: retarget the level-`m` difference `x = b₁−b₃` to
`q = 1` and the level-`hy` difference `y = b₂−b₃` to `q = 0` via
`qz_retarget_two_top`. Then:
- `qz(λ·b₁) = qz(λ·b₃) + 1` (EXACT — `λ·x` is a multiple of `7^m`, so
  `qz_add_mul_pow` applies with no carry ambiguity);
- `qz(λ·b₂) ∈ {qz(λ·b₃), qz(λ·b₃)+1}` (standard `qz_add_carry`).
So `q(λ·B) ⊂ {c, c+1}` and `ℓ(λ·B) ≤ 2`. -/
theorem lemma9_i_top (m hy : ℕ) (hym : hy < m) (b₁ b₂ b₃ : ℤ)
    (hxd : (7 : ℤ) ^ m ∣ (b₁ - b₃)) (hxd' : ¬ (7 : ℤ) ^ (m + 1) ∣ (b₁ - b₃))
    (hyd : (7 : ℤ) ^ hy ∣ (b₂ - b₃)) (hyd' : ¬ (7 : ℤ) ^ (hy + 1) ∣ (b₂ - b₃)) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∃ a : ZMod 7,
      fitsInterval ({qz m (lam * b₁), qz m (lam * b₂), qz m (lam * b₃)}
        : Finset (ZMod 7)) a 2 := by
  obtain ⟨lam, hlam, hqx, hqy⟩ :=
    qz_retarget_two_top m hy hym (b₁ - b₃) (b₂ - b₃) hxd hxd' hyd hyd' 1 0 (by decide)
  refine ⟨lam, hlam, qz m (lam * b₃), fun v hv => ?_⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with rfl | rfl | rfl
  · -- v = qz m (lam * b₁): exact shift by 1 via qz_sub_mul_pow (with negation)
    obtain ⟨u, hu⟩ := hxd
    have hPne : (7 : ℤ) ^ m ≠ 0 := pow_ne_zero m (by norm_num)
    have hlin : lam * b₁ = lam * b₃ - (7 : ℤ) ^ m * (-(lam * u)) := by
      have : b₁ = b₃ + 7 ^ m * u := by linarith
      rw [this]; ring
    have hcu : (↑(lam * u) : ZMod 7) = (1 : ZMod 7) := by
      have hqu := hqx
      rw [hu, show lam * (7 ^ m * u) = (lam * u) * 7 ^ m from by ring] at hqu
      unfold qz at hqu
      rwa [Int.mul_ediv_cancel _ hPne] at hqu
    rw [hlin, qz_sub_mul_pow]
    exact ⟨⟨1, by omega⟩, by simp only [Fin.val_mk, Nat.cast_one, Int.cast_neg, sub_neg_eq_add,
      hcu]⟩
  · -- v = qz m (lam * b₂): carry ∈ {0, 1} via qz_add_carry
    have hlin : lam * b₂ = lam * b₃ + lam * (b₂ - b₃) := by ring
    rw [hlin]
    rcases qz_add_carry m (lam * b₃) (lam * (b₂ - b₃)) with h | h
    · rw [h, hqy, add_zero]; exact ⟨⟨0, by omega⟩, by simp only [Fin.val_mk, Nat.cast_zero,
        add_zero]⟩
    · rw [h, hqy, add_zero]; exact ⟨⟨1, by omega⟩, by simp only [Fin.val_mk, Nat.cast_one]⟩
  · -- v = qz m (lam * b₃)
    exact ⟨⟨0, by omega⟩, by simp only [Fin.val_mk, Nat.cast_zero, add_zero]⟩

/-- **Lemma 9 (i) full dispatch.** Three elements `b₁, b₂, b₃` whose pairwise
differences `x = b₁−b₃`, `y = b₂−b₃` have DISTINCT valuations: there exists a
unit multiplier compressing `ℓ(λ·B) ≤ 2`. Dispatches over all valuation
configurations:
- both `< m` → `lemma9_i` (two-target retarget, Remark 8)
- one `= m`, other `< m` → `lemma9_i_top` (exact 7^m shift + carry)
- one `> m` → q-equivalence (`qz_eq_of_high_dvd`) reduces to ≤ 2 elements -/
theorem lemma9_i_dispatch (m h₁ h₂ : ℕ) (b₁ b₂ b₃ : ℤ) (hne : h₁ ≠ h₂)
    (hxd : (7 : ℤ) ^ h₁ ∣ (b₁ - b₃)) (hxd' : ¬ (7 : ℤ) ^ (h₁ + 1) ∣ (b₁ - b₃))
    (hyd : (7 : ℤ) ^ h₂ ∣ (b₂ - b₃)) (hyd' : ¬ (7 : ℤ) ^ (h₂ + 1) ∣ (b₂ - b₃)) :
    ∃ lam : ℤ, ¬ (7 : ℤ) ∣ lam ∧ ∃ a : ZMod 7,
      fitsInterval ({qz m (lam * b₁), qz m (lam * b₂), qz m (lam * b₃)}
        : Finset (ZMod 7)) a 2 := by
  -- Helper: element with 7^(m+1)-divisible difference is q-equivalent to b₃
  have qeq_b1 : (7 : ℤ) ^ (m + 1) ∣ (b₁ - b₃) → ∀ l : ℤ,
      qz m (l * b₁) = qz m (l * b₃) := fun h l => qz_eq_of_high_dvd m b₁ b₃ l h
  have qeq_b2 : (7 : ℤ) ^ (m + 1) ∣ (b₂ - b₃) → ∀ l : ℤ,
      qz m (l * b₂) = qz m (l * b₃) := fun h l => qz_eq_of_high_dvd m b₂ b₃ l h
  -- Helper: level-m retarget gives exact shift → fitsInterval at j=1
  have shift1 : ∀ j x : ℤ, (7 : ℤ) ^ m ∣ x → qz m (j * x) = 1 →
      ∃ jj : Fin 2, qz m (j * b₃ + j * x) = qz m (j * b₃) + (jj.val : ZMod 7) := by
    intro j x hdvd hqj
    obtain ⟨u, hu⟩ := hdvd
    have hPne : (7 : ℤ) ^ m ≠ 0 := pow_ne_zero m (by norm_num)
    have hcu : (↑(j * u) : ZMod 7) = (1 : ZMod 7) := by
      rw [hu, show j * (7 ^ m * u) = (j * u) * 7 ^ m from by ring] at hqj
      unfold qz at hqj; rwa [Int.mul_ediv_cancel _ hPne] at hqj
    have hlin : j * b₃ + j * x = j * b₃ - (7 : ℤ) ^ m * (-(j * u)) := by
      rw [hu]; ring
    rw [hlin, qz_sub_mul_pow]
    exact ⟨⟨1, by omega⟩, by simp only [Fin.val_mk, Nat.cast_one, Int.cast_neg,
      sub_neg_eq_add, hcu]⟩
  rcases lt_or_ge h₁ m with h1m | h1m <;> rcases lt_or_ge h₂ m with h2m | h2m
  · -- Both < m
    exact lemma9_i m h₁ h₂ b₁ b₂ b₃ h1m h2m hne hxd hxd' hyd hyd'
  · -- h₁ < m, h₂ ≥ m
    rcases h2m.eq_or_lt with heq | h2gt
    · -- h₂ = m: swap roles
      subst heq
      obtain ⟨lam, hlam, a, ha⟩ := lemma9_i_top m h₁ h1m b₂ b₁ b₃ hyd hyd' hxd hxd'
      exact ⟨lam, hlam, a, by rwa [show ({qz m (lam * b₁), qz m (lam * b₂), qz m (lam * b₃)}
        : Finset (ZMod 7)) = {qz m (lam * b₂), qz m (lam * b₁), qz m (lam * b₃)} from by
          ext x; simp [or_comm, or_left_comm]]⟩
    · -- h₂ > m: b₂ q-equiv to b₃
      have hhi := dvd_trans (pow_dvd_pow 7 (by omega : m + 1 ≤ h₂)) hyd
      obtain ⟨k, hk, hku⟩ := qz_retarget m h₁ h1m (b₁ - b₃) hxd hxd' 0
      set l := 1 + k * 7 ^ (m - h₁) with hl_def
      refine ⟨l, hku, qz m (l * b₃), fun v hv => ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl
      · rw [show l * b₁ = l * b₃ + l * (b₁ - b₃) from by ring]
        rcases qz_add_carry m (l * b₃) (l * (b₁ - b₃)) with h | h
        · rw [h, hk, add_zero]; exact ⟨⟨0, by omega⟩, by simp [Fin.val]⟩
        · rw [h, hk, add_zero]; exact ⟨⟨1, by omega⟩, by simp [Fin.val]⟩
      · rw [qeq_b2 hhi]; exact ⟨⟨0, by omega⟩, by simp [Fin.val]⟩
      · exact ⟨⟨0, by omega⟩, by simp [Fin.val]⟩
  · -- h₁ ≥ m, h₂ < m
    rcases h1m.eq_or_lt with heq | h1gt
    · subst heq; exact lemma9_i_top m h₂ h2m b₁ b₂ b₃ hxd hxd' hyd hyd'
    · -- h₁ > m: b₁ q-equiv to b₃
      have hhi := dvd_trans (pow_dvd_pow 7 (by omega : m + 1 ≤ h₁)) hxd
      obtain ⟨k, hk, hku⟩ := qz_retarget m h₂ h2m (b₂ - b₃) hyd hyd' 0
      set l := 1 + k * 7 ^ (m - h₂) with hl_def
      refine ⟨l, hku, qz m (l * b₃), fun v hv => ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl
      · rw [qeq_b1 hhi]; exact ⟨⟨0, by omega⟩, by simp [Fin.val]⟩
      · rw [show l * b₂ = l * b₃ + l * (b₂ - b₃) from by ring]
        rcases qz_add_carry m (l * b₃) (l * (b₂ - b₃)) with h | h
        · rw [h, hk, add_zero]; exact ⟨⟨0, by omega⟩, by simp [Fin.val]⟩
        · rw [h, hk, add_zero]; exact ⟨⟨1, by omega⟩, by simp [Fin.val]⟩
      · exact ⟨⟨0, by omega⟩, by simp [Fin.val]⟩
  · -- Both ≥ m
    rcases h1m.eq_or_lt with heq | h1gt
    · -- h₁ = m, h₂ > m
      subst heq
      have h2gt : m < h₂ := lt_of_le_of_ne h2m hne
      have hhi := dvd_trans (pow_dvd_pow 7 (by omega : m + 1 ≤ h₂)) hyd
      obtain ⟨j, hju, hjx⟩ := qz_retarget_top m (b₁ - b₃) hxd hxd' 1 (by decide)
      refine ⟨j, hju, qz m (j * b₃), fun v hv => ?_⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl
      · rw [show j * b₁ = j * b₃ + j * (b₁ - b₃) from by ring]
        exact (shift1 j _ hxd hjx).elim fun jj hj => ⟨jj, hj⟩
      · rw [qeq_b2 hhi]; exact ⟨⟨0, by omega⟩, by simp [Fin.val]⟩
      · exact ⟨⟨0, by omega⟩, by simp [Fin.val]⟩
    · rcases h2m.eq_or_lt with heq | h2gt
      · -- h₂ = m, h₁ > m
        subst heq
        have hhi := dvd_trans (pow_dvd_pow 7 (by omega : m + 1 ≤ h₁)) hxd
        obtain ⟨j, hju, hjy⟩ := qz_retarget_top m (b₂ - b₃) hyd hyd' 1 (by decide)
        refine ⟨j, hju, qz m (j * b₃), fun v hv => ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl | rfl
        · rw [qeq_b1 hhi]; exact ⟨⟨0, by omega⟩, by simp [Fin.val]⟩
        · rw [show j * b₂ = j * b₃ + j * (b₂ - b₃) from by ring]
          exact (shift1 j _ hyd hjy).elim fun jj hj => ⟨jj, hj⟩
        · exact ⟨⟨0, by omega⟩, by simp [Fin.val]⟩
      · -- Both > m: all q-equivalent
        have hhi1 := dvd_trans (pow_dvd_pow 7 (by omega : m + 1 ≤ h₁)) hxd
        have hhi2 := dvd_trans (pow_dvd_pow 7 (by omega : m + 1 ≤ h₂)) hyd
        refine ⟨1, by decide, qz m (1 * b₃), fun v hv => ?_⟩
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl | rfl
        · rw [qeq_b1 hhi1]; exact ⟨⟨0, by omega⟩, by simp [Fin.val]⟩
        · rw [qeq_b2 hhi2]; exact ⟨⟨0, by omega⟩, by simp [Fin.val]⟩
        · exact ⟨⟨0, by omega⟩, by simp [Fin.val]⟩

end IntLRC7BS
