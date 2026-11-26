import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.Admissible
import Fresh.EightResidualLink
import Fresh.FastPairReal
import Fresh.AdmissibleFlank
import Fresh.AdmissibleMore
import Fresh.AdmissibleMoreLink

/-!
# The fast-pair class and the old fast-pair fields, both directions

Written 2026-10-25.  New file.  `SixClear5` is order six on real speeds in `distInt` form: at most five positive reals have an instant at which each is `1/6`-clear.
It is proved in `Fresh.NativeOrders.sixClear5_proved` (2026-10-25, after the ported order-six files compiled; this file was first written with the statement as a hypothesis); it is the statement of `LRC.OrderSixN.existenceAtN_six` (nested repo `LonelyRunner`, `Spec/RealSixN.lean`, axioms
`[propext, Classical.choice, Quot.sound]`, checked 2026-10-25), whose `Lonely 6` unfolds to `1/6 ≤ circDist (d * s)` with `circDist x = min (fract x) (1 - fract x)`;
the identification of `circDist` with `distInt` is by reading, not proved here.  Owner ruling 2026-09-25: lower orders 3 to 7 are native and may be used.
`fastPair_iff_old`: given `SixClear5`, the class is exactly the old fast-pair fields (a pair `a < b`, a nonempty core, `9c ≤ a` for every core `c`).
Grade [L] (the hypothesis `SixClear5` is discharged by `NativeOrders`).
-/

namespace Fresh.AdmissibleMoreLink

open Fresh Fresh.Admissible Fresh.EightResidualLink Fresh.AdmissibleMore Fresh.FastPairReal Fresh.AdmissibleFlank

/-- Order six on real speeds: at most five positive reals have an instant at which each is `1/6`-clear. -/
-- STANDING: PROVED (`Fresh.NativeOrders.sixClear5_proved`, from the ported `LRC.OrderSixN.existenceAtN_six`; tag changed from IMPORTED 2026-10-25)
def SixClear5 : Prop :=
  ∀ ds : Finset ℝ, (∀ d ∈ ds, 0 < d) → ds.card ≤ 5 → ∃ τ : ℝ, 0 < τ ∧ ∀ d ∈ ds, (1 / 6 : ℝ) ≤ distInt (d * τ)

theorem old_fastPair_imp_class (hSix : SixClear5) {v : Fin 8 → ℝ} (hinj : Function.Injective v) {k : Fin 8} {S : Finset ℕ}
    (hS : HasDisp v k S) {a b : ℕ} (ha : a ∈ S) (hb : b ∈ S) (hab : a < b) (hc : ∃ c ∈ S, c ≠ a ∧ c ≠ b)
    (h9 : ∀ c ∈ S, c ≠ a → c ≠ b → 9 * c ≤ a) : FastPairClass v k := by
  set C : Finset ℝ := ((disparitySet v k).erase (a : ℝ)).erase (b : ℝ) with hC
  have hCsub : ∀ x ∈ C, x ∈ disparitySet v k ∧ x ≠ (a : ℝ) ∧ x ≠ (b : ℝ) := by
    intro x hx
    simp only [hC, Finset.mem_erase] at hx
    exact ⟨hx.2.2, hx.2.1, hx.1⟩
  have hcard : C.card ≤ 5 := by
    have h7 : (disparitySet v k).card ≤ 7 := by
      unfold disparitySet
      calc _ ≤ (Finset.univ.erase k).card := Finset.card_image_le
        _ = 7 := by simp
    have h1 : ((disparitySet v k).erase (a : ℝ)).card ≤ (disparitySet v k).card := Finset.card_erase_le
    have h2 : C.card ≤ ((disparitySet v k).erase (a : ℝ)).card := Finset.card_erase_le
    have hmemA : (a : ℝ) ∈ disparitySet v k := (hS _).2 ⟨a, ha, rfl⟩
    have hmemB : (b : ℝ) ∈ ((disparitySet v k).erase (a : ℝ)) :=
      Finset.mem_erase.2 ⟨by exact_mod_cast hab.ne', (hS _).2 ⟨b, hb, rfl⟩⟩
    have h3 := Finset.card_erase_of_mem hmemA
    have h4 := Finset.card_erase_of_mem hmemB
    simp only [hC]
    omega
  obtain ⟨τ, hτ, hclear⟩ := hSix C (fun x hx => disp_pos hinj (hCsub x hx).1) hcard
  obtain ⟨c0, hc0S, hc0a, hc0b⟩ := hc
  refine ⟨(a : ℝ), (hS _).2 ⟨a, ha, rfl⟩, (b : ℝ), (hS _).2 ⟨b, hb, rfl⟩, by exact_mod_cast hab,
    ⟨(c0 : ℝ), (hS _).2 ⟨c0, hc0S, rfl⟩, by exact_mod_cast hc0a, by exact_mod_cast hc0b⟩, τ, hτ, fun x hx hxa hxb => ?_⟩
  obtain ⟨d, hd, rfl⟩ := (hS x).1 hx
  have hda : d ≠ a := fun h => hxa (by rw [h])
  have hdb : d ≠ b := fun h => hxb (by rw [h])
  refine ⟨hclear _ (by simp only [hC, Finset.mem_erase]; exact ⟨hxb, hxa, hx⟩), ?_⟩
  exact_mod_cast h9 d hd hda hdb

theorem fastPair_iff_old (hSix : SixClear5) {v : Fin 8 → ℝ} (hinj : Function.Injective v) {k : Fin 8} {S : Finset ℕ}
    (hS : HasDisp v k S) :
    FastPairClass v k ↔ ∃ a ∈ S, ∃ b ∈ S, a < b ∧ (∃ c ∈ S, c ≠ a ∧ c ≠ b) ∧ ∀ c ∈ S, c ≠ a → c ≠ b → 9 * c ≤ a := by
  constructor
  · intro h
    obtain ⟨x, hx, y, hy, hxy, ⟨z, hz, hzx, hzy⟩, τ, hτ, hcore⟩ := h
    obtain ⟨a, ha, rfl⟩ := (hS x).1 hx
    obtain ⟨b, hb, rfl⟩ := (hS y).1 hy
    obtain ⟨c, hc, rfl⟩ := (hS z).1 hz
    refine ⟨a, ha, b, hb, by exact_mod_cast hxy, ⟨c, hc, fun h => hzx (by rw [h]), fun h => hzy (by rw [h])⟩,
      fun e he hea heb => ?_⟩
    have := (hcore (e : ℝ) ((hS _).2 ⟨e, he, rfl⟩) (fun h => hea (by exact_mod_cast h))
      (fun h => heb (by exact_mod_cast h))).2
    exact_mod_cast this
  · rintro ⟨a, ha, b, hb, hab, hc, h9⟩
    exact old_fastPair_imp_class hSix hinj hS ha hb hab hc h9

#print axioms old_fastPair_imp_class
#print axioms fastPair_iff_old

end Fresh.AdmissibleMoreLink
