import Mathlib

/-! Generic lemma used by the ported order-eight case files; statement and proof as `LRC.OrderSevenN.quotient_card_sum`
(`Nv_OrderSevenN`), restated so that the Barajas-Serra module is not imported.  Written 2026-10-29.  Grade [L]. -/

namespace Fresh.FreeHelpers

theorem quotient_card_sum {S : Finset ℕ} {g : ℕ} (hg : 2 ≤ g) (hpos : ∀ d ∈ S, 0 < d)
    (hgd : ∀ d ∈ S, g ∣ d) (hne : S.Nonempty) :
    (S.image (fun d => d / g)).card = S.card ∧
      ∑ d ∈ S.image (fun d => d / g), d < ∑ d ∈ S, d ∧
      ∀ x ∈ S.image (fun d => d / g), 0 < x := by
  have hinj : Set.InjOn (fun d => d / g) (S : Set ℕ) := by
    intro x hx y hy hxy
    simp only at hxy
    rw [← Nat.div_mul_cancel (hgd x hx), ← Nat.div_mul_cancel (hgd y hy), hxy]
  refine ⟨Finset.card_image_of_injOn hinj, ?_, ?_⟩
  · rw [Finset.sum_image hinj]
    exact Finset.sum_lt_sum_of_nonempty hne fun d hd => Nat.div_lt_self (hpos d hd) (by omega)
  · intro x hx
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
    exact Nat.div_pos (Nat.le_of_dvd (hpos d hd) (hgd d hd)) (by omega)

#print axioms quotient_card_sum

end Fresh.FreeHelpers
