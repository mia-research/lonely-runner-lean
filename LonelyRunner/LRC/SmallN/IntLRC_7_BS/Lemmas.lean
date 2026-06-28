import LonelyRunner.LRC.SmallN.IntLRC_7_BS.Defs
import LonelyRunner.LRC.SmallN.IntLRC_7_BS.PrimeFiltering

/-!
# n = 7 (Barajas–Serra) — Supporting Lemmas 5–9

Source: `sources_barajas_serra_2008.txt`, lines 364–506.

These lemmas provide the combinatorial tools used by the §6 case analysis
(|A|=5). Lemma 5 is the main pigeonhole for `ℓ(A₁)+ℓ(A₂)+ℓ(A₄) ≤ 5`.
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

/-- **Remark 8 (ii) combinatorial core (BS L478).** Three values in `ZMod 7` whose
pairwise differences all lie in `{0,1,2,5,6} = {−2,…,2}` fit in a length-3 AP.
(Max clique in the `{±1,±2}` Cayley graph on `ZMod 7` is a 3-term interval.)
Stated for 3 explicit elements — matches `B = {b₁,b₂,b₃}` in Lemma 9. -/
set_option maxRecDepth 4000 in
theorem remark8_ii_core3 (v₁ v₂ v₃ : ZMod 7)
    (h₁₂ : v₁ - v₂ ∈ ({0, 1, 2, 5, 6} : Finset (ZMod 7)))
    (h₁₃ : v₁ - v₃ ∈ ({0, 1, 2, 5, 6} : Finset (ZMod 7)))
    (h₂₃ : v₂ - v₃ ∈ ({0, 1, 2, 5, 6} : Finset (ZMod 7))) :
    ∃ a : ZMod 7, fitsInterval ({v₁, v₂, v₃} : Finset (ZMod 7)) a 3 := by
  revert h₁₂ h₁₃ h₂₃; revert v₁ v₂ v₃; decide

/-- **Remark 8 (i) combinatorial core, `k = 1` (BS L476).** Three `ZMod 7` values
whose pairwise differences all lie in `{0,1,6} = {−1,0,1}` fit in a length-2 AP.
(Used via `qz_subxy_carry`: `q(X−X)⊂{0,6}` ⇒ pairwise `qz`-diffs ∈ `{−1,0,1}`.) -/
set_option maxRecDepth 4000 in
theorem remark8_i_core3 (v₁ v₂ v₃ : ZMod 7)
    (h₁₂ : v₁ - v₂ ∈ ({0, 1, 6} : Finset (ZMod 7)))
    (h₁₃ : v₁ - v₃ ∈ ({0, 1, 6} : Finset (ZMod 7)))
    (h₂₃ : v₂ - v₃ ∈ ({0, 1, 6} : Finset (ZMod 7))) :
    ∃ a : ZMod 7, fitsInterval ({v₁, v₂, v₃} : Finset (ZMod 7)) a 2 := by
  revert h₁₂ h₁₃ h₂₃; revert v₁ v₂ v₃; decide

/-- **Lemma 4 (i) (BS L366), `r(y)=2r(x)` case.** The quantity `ẽ(x,y)=2q(x)−q(y)`
is invariant under a level-`h` multiplier `1+k·7^{m-h}`, provided `x,y` share level
`h` with `r(y)=2r(x)` (here as `(y/7^h) = 2·(x/7^h)` in `ZMod 7`). Immediate from
`qz_lambda`: the two shifts `k·r(x)`, `k·r(y)=2k·r(x)` cancel in `2q(λx)−q(λy)`. -/
theorem lemma4_i (m h : ℕ) (hhm : h ≤ m) (k x y : ℤ)
    (hx : (7 : ℤ) ^ h ∣ x) (hy : (7 : ℤ) ^ h ∣ y)
    (hr : ((y / 7 ^ h : ℤ) : ZMod 7) = 2 * ((x / 7 ^ h : ℤ) : ZMod 7)) :
    2 * qz m ((1 + k * 7 ^ (m - h)) * x) - qz m ((1 + k * 7 ^ (m - h)) * y)
      = 2 * qz m x - qz m y := by
  rw [qz_lambda m h hhm k x hx, qz_lambda m h hhm k y hy, hr]; ring

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
  refine ⟨lam, hlam, ?_⟩
  set v₁ := qz m (lam * b₁) with hv₁
  set v₂ := qz m (lam * b₂) with hv₂
  set v₃ := qz m (lam * b₃) with hv₃
  -- v₁ − v₃ = −c with c ∈ {0,6}, so ∈ {0,1}
  have e13 : v₁ - v₃ ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
    obtain ⟨c, hc, hcq⟩ := qz_subxy_carry m (lam * b₁) (lam * b₃)
    rw [show lam * b₁ - lam * b₃ = lam * (b₁ - b₃) from by ring, hq1] at hcq
    have hv : v₁ - v₃ = -c := by linear_combination -hcq
    rw [hv]; rcases hc with rfl | rfl <;> decide
  have e23 : v₂ - v₃ ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
    obtain ⟨c, hc, hcq⟩ := qz_subxy_carry m (lam * b₂) (lam * b₃)
    rw [show lam * b₂ - lam * b₃ = lam * (b₂ - b₃) from by ring, hq2] at hcq
    have hv : v₂ - v₃ = -c := by linear_combination -hcq
    rw [hv]; rcases hc with rfl | rfl <;> decide
  have e12 : v₁ - v₂ ∈ ({0, 1, 6} : Finset (ZMod 7)) := by
    obtain ⟨c', hc', hcq'⟩ := qz_subxy_carry m (lam * (b₁ - b₃)) (lam * (b₂ - b₃))
    rw [hq1, hq2, show lam * (b₁ - b₃) - lam * (b₂ - b₃) = lam * (b₁ - b₂) from by ring] at hcq'
    obtain ⟨c'', hc'', hcq''⟩ := qz_subxy_carry m (lam * b₁) (lam * b₂)
    rw [show lam * b₁ - lam * b₂ = lam * (b₁ - b₂) from by ring] at hcq''
    have hv : v₁ - v₂ = c' - c'' := by linear_combination hcq' - hcq''
    rw [hv]; rcases hc' with rfl | rfl <;> rcases hc'' with rfl | rfl <;> decide
  obtain ⟨a, ha⟩ := remark8_i_core3 v₁ v₂ v₃ e12 e13 e23
  exact ⟨a, ha⟩

end IntLRC7BS
