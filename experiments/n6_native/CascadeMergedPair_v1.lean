import Mathlib

/-!
# The merged pair inside the first meeting window (observation formalised)

§5 of BHK at order six: `v₂ = v₃ − D`. At an opening with multiplier `m` of a flank `x` (residues mod `6x`),
inside the first meeting window (`0 ≤ D·m ≤ x`, i.e. `D·T ≤ 1/6`), runners 2 and 3 are both in the band
`[x, 5x]` exactly when runner 3's residue lies in the shifted band `[x + D·m, 5x]`.
Observed exactly at 4,708 in-window openings (`six_s5_window_residues_v1.out`).
-/

namespace CascadeMergedPair

theorem merged_pair_iff {x D v3 m : ℤ} (hx : 0 < x) (hD : 0 ≤ D * m) (hwin : D * m ≤ x) :
    ((x ≤ (v3 - D) * m % (6 * x) ∧ (v3 - D) * m % (6 * x) ≤ 5 * x) ∧
      (x ≤ v3 * m % (6 * x) ∧ v3 * m % (6 * x) ≤ 5 * x)) ↔
    (x + D * m ≤ v3 * m % (6 * x) ∧ v3 * m % (6 * x) ≤ 5 * x) := by
  have hM : 0 < 6 * x := by positivity
  set r := v3 * m % (6 * x) with hr
  have hr0 : 0 ≤ r := Int.emod_nonneg _ (by omega)
  have hrM : r < 6 * x := Int.emod_lt_of_pos _ hM
  -- runner 2's residue is (r − D m) mod 6x
  have h2 : (v3 - D) * m % (6 * x) = (r - D * m) % (6 * x) := by
    rw [hr, sub_mul]
    conv_rhs => rw [Int.sub_emod, Int.emod_emod_of_dvd _ (dvd_refl _), ← Int.sub_emod]
  rw [h2]
  constructor
  · rintro ⟨⟨h2lo, h2hi⟩, ⟨h3lo, h3hi⟩⟩
    -- r − D m ∈ [x − D m, 5x] ⊆ [0, 6x), so the residue is r − D m itself
    have e : (r - D * m) % (6 * x) = r - D * m := Int.emod_eq_of_lt (by omega) (by omega)
    rw [e] at h2lo
    exact ⟨by omega, h3hi⟩
  · rintro ⟨hlo, hhi⟩
    have e : (r - D * m) % (6 * x) = r - D * m := Int.emod_eq_of_lt (by omega) (by omega)
    rw [e]
    exact ⟨⟨by omega, by omega⟩, ⟨by omega, hhi⟩⟩

end CascadeMergedPair

#print axioms CascadeMergedPair.merged_pair_iff
