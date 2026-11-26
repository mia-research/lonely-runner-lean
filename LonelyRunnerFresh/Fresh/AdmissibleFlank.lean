import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.Admissible
import Fresh.AdmissiblePlus
import Fresh.EightResidualLink
import Fresh.ResolutionReal

/-!
# First-lap clearance on real speeds: a native reproof of an old rule, and the smaller remainder

Written 2026-10-25 (owner: look at the old repo for things to re-prove natively and reduce the admissible remainder).  New file.  The old rule `lonely_eight_of_firstLap` (`OrderEightCasesN.lean:320`; Theorems 15.40 to 15.43) is for an integer
set `S`: at a flank `e ∈ S` and an index `k`, if `e ≤ d (8k + 1) ≤ 7e` for every other disparity `d`, the opening `(8k + 1)/(8e)` is lonely.  Re-proved here for real speeds, with no integer set and no cap:
`FirstLapClass v k := ∃ e` among the subject's disparities, `∃ n : ℕ`, `e ≤ d (8n + 1) ≤ 7e` for every other disparity `d`.
* `firstLap_isolation`: it gives an isolation of the subject, at `(8n + 1)/(8e)`, by `clear_of_window` with no wraparound.
* `ratio_imp_firstLap`: the ratio class is the case `e = d_min`, `n = 0`.
* Scale and translation invariance (`FirstLapClass_smul`, `FirstLapClass_add`).
* `firstLap_iff_not_old_field`: for an integer disparity set it is exactly the failure of the old field `no_first_lap`.
`FlankProved := ProvedPlus ∨ FirstLapClass`, `AdmissibleFlank := IsOrderedArrangement ∧ ¬ FlankProved`; `flankProved_isolation`, `flankProved_or_admissible` (partition), `admissibleFlank_iff`.
Grades: [L].  Not claimed: finiteness of the remainder; the other old rules (the `-7` opening, rational openings, thirds, fifths, sixths, the descent, the fast runner, the largest multiple, fast pair, block split) are integer-set statements whose real forms are not yet found.
-/

open Classical

namespace Fresh.AdmissibleFlank

open Fresh Fresh.Admissible Fresh.AdmissiblePlus Fresh.EightResidualLink

-- STANDING: DEFINITION
def FirstLapClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ e ∈ disparitySet v k, ∃ n : ℕ, ∀ d ∈ disparitySet v k, d ≠ e → e ≤ d * (8 * (n : ℝ) + 1) ∧ d * (8 * (n : ℝ) + 1) ≤ 7 * e

theorem disp_pos {v : Fin 8 → ℝ} (hinj : Function.Injective v) {k : Fin 8} {d : ℝ} (hd : d ∈ disparitySet v k) : 0 < d := by
  obtain ⟨i, hik, rfl⟩ := Fresh.Localisation.mem_disparitySet.1 hd
  exact abs_pos.2 (sub_ne_zero.2 (fun h => hik (hinj h)))

theorem firstLap_isolation {v : Fin 8 → ℝ} (hinj : Function.Injective v) {k : Fin 8} (h : FirstLapClass v k) : Isolation v k := by
  obtain ⟨e, he, n, hn⟩ := h
  have hepos := disp_pos hinj he
  have hn1 : (0 : ℝ) < 8 * (n : ℝ) + 1 := by positivity
  refine ⟨(8 * (n : ℝ) + 1) / (8 * e), by positivity, ?_⟩
  rw [Fresh.Localisation.isolatedAt_iff]
  intro d hd
  have hdpos := disp_pos hinj hd
  by_cases hde : d = e
  · subst hde
    have : d * ((8 * (n : ℝ) + 1) / (8 * d)) = ((n : ℤ) : ℝ) + 1 / 8 := by push_cast; field_simp
    rw [this, add_comm]
    exact (Cascade.distInt_eighth_add_int (n : ℤ)).ge
  · obtain ⟨h1, h2⟩ := hn d hd hde
    have e1 : d * ((8 * (n : ℝ) + 1) / (8 * e)) = d * (8 * (n : ℝ) + 1) / (8 * e) := by ring
    rw [e1]
    apply Fresh.Localisation.clear_of_window 0
    · simp only [Int.cast_zero, zero_add]; rw [le_div_iff₀ (by positivity)]; linarith
    · simp only [Int.cast_zero, zero_add]; rw [div_le_iff₀ (by positivity)]; linarith

theorem ratio_imp_firstLap {v : Fin 8 → ℝ} (hinj : Function.Injective v) {k : Fin 8} (h : RatioClass v k) : FirstLapClass v k := by
  obtain ⟨m, hm, h7⟩ := h
  obtain ⟨hpos, ⟨i, hik, hie⟩, hle⟩ := dmin_facts hm hinj
  refine ⟨m, Fresh.Localisation.mem_disparitySet.2 ⟨i, hik, hie⟩, 0, fun d hd _ => ?_⟩
  obtain ⟨j, hjk, rfl⟩ := Fresh.Localisation.mem_disparitySet.1 hd
  simp only [Nat.cast_zero, mul_zero, zero_add, mul_one]
  exact ⟨hle j hjk, h7 j hjk⟩

-- STANDING: DEFINITION
def FlankProved (v : Fin 8 → ℝ) (k : Fin 8) : Prop := ProvedPlus v k ∨ FirstLapClass v k

-- STANDING: DEFINITION
def AdmissibleFlank (v : Fin 8 → ℝ) (k : Fin 8) : Prop := IsOrderedArrangement v ∧ ¬ FlankProved v k

theorem flankProved_isolation {v : Fin 8 → ℝ} (hv : IsOrderedArrangement v) {k : Fin 8} (h : FlankProved v k) : Isolation v k := by
  rcases h with h | h
  · exact provedPlus_isolation hv h
  · exact firstLap_isolation hv.2.injective h

theorem flankProved_or_admissible {v : Fin 8 → ℝ} (hv : IsOrderedArrangement v) (k : Fin 8) :
    FlankProved v k ∨ AdmissibleFlank v k := by
  by_cases h : FlankProved v k
  · exact Or.inl h
  · exact Or.inr ⟨hv, h⟩

theorem admissibleFlank_iff {v : Fin 8 → ℝ} (k : Fin 8) :
    AdmissibleFlank v k ↔ AdmissiblePlus v k ∧ ¬ FirstLapClass v k := by
  unfold AdmissibleFlank AdmissiblePlus FlankProved
  constructor
  · rintro ⟨ho, hn⟩
    push Not at hn
    exact ⟨⟨ho, hn.1⟩, hn.2⟩
  · rintro ⟨⟨ho, hn⟩, hf⟩
    exact ⟨ho, by push Not; exact ⟨hn, hf⟩⟩

theorem mem_disp_smul {c : ℝ} (hc : 0 < c) (v : Fin 8 → ℝ) (k : Fin 8) (e : ℝ) :
    e ∈ disparitySet (fun j => c * v j) k ↔ ∃ d ∈ disparitySet v k, e = c * d := by
  constructor
  · intro h
    obtain ⟨i, hik, rfl⟩ := Fresh.Localisation.mem_disparitySet.1 h
    exact ⟨|v i - v k|, Fresh.Localisation.mem_disparitySet.2 ⟨i, hik, rfl⟩, habs_smul hc v i k⟩
  · rintro ⟨d, hd, rfl⟩
    obtain ⟨i, hik, rfl⟩ := Fresh.Localisation.mem_disparitySet.1 hd
    exact Fresh.Localisation.mem_disparitySet.2 ⟨i, hik, habs_smul hc v i k⟩

theorem FirstLapClass_smul {c : ℝ} (hc : 0 < c) (v : Fin 8 → ℝ) (k : Fin 8) :
    FirstLapClass (fun j => c * v j) k ↔ FirstLapClass v k := by
  unfold FirstLapClass
  constructor
  · rintro ⟨e', he', n, hn⟩
    obtain ⟨e, he, rfl⟩ := (mem_disp_smul hc v k e').1 he'
    refine ⟨e, he, n, fun d hd hde => ?_⟩
    have h := hn (c * d) ((mem_disp_smul hc v k _).2 ⟨d, hd, rfl⟩) (fun h => hde (mul_left_cancel₀ hc.ne' h))
    obtain ⟨h1, h2⟩ := h
    constructor <;> nlinarith
  · rintro ⟨e, he, n, hn⟩
    refine ⟨c * e, (mem_disp_smul hc v k _).2 ⟨e, he, rfl⟩, n, fun d' hd' hde => ?_⟩
    obtain ⟨d, hd, rfl⟩ := (mem_disp_smul hc v k d').1 hd'
    have h := hn d hd (fun h => hde (by rw [h]))
    obtain ⟨h1, h2⟩ := h
    constructor <;> nlinarith

theorem FirstLapClass_add (s : ℝ) (v : Fin 8 → ℝ) (k : Fin 8) : FirstLapClass (fun j => v j + s) k ↔ FirstLapClass v k := by
  have hset : disparitySet (fun j => v j + s) k = disparitySet v k := by
    ext e
    rw [Fresh.Localisation.mem_disparitySet, Fresh.Localisation.mem_disparitySet]
    simp only [habs_add]
  unfold FirstLapClass
  rw [hset]

theorem firstLap_iff_not_old_field {v : Fin 8 → ℝ} {k : Fin 8} {S : Finset ℕ} (hS : HasDisp v k S) :
    FirstLapClass v k ↔ ∃ e ∈ S, ∃ n : ℕ, ∀ d ∈ S, d ≠ e → e ≤ d * (8 * n + 1) ∧ d * (8 * n + 1) ≤ 7 * e := by
  unfold FirstLapClass
  constructor
  · rintro ⟨x, hx, n, hn⟩
    obtain ⟨e, he, rfl⟩ := (hS x).1 hx
    refine ⟨e, he, n, fun d hd hde => ?_⟩
    have := hn (d : ℝ) ((hS _).2 ⟨d, hd, rfl⟩) (fun h => hde (by exact_mod_cast h))
    obtain ⟨h1, h2⟩ := this
    constructor
    · have : (e : ℝ) ≤ d * (8 * n + 1) := h1
      exact_mod_cast this
    · have : (d : ℝ) * (8 * n + 1) ≤ 7 * e := h2
      exact_mod_cast this
  · rintro ⟨e, he, n, hn⟩
    refine ⟨(e : ℝ), (hS _).2 ⟨e, he, rfl⟩, n, fun x hx hxe => ?_⟩
    obtain ⟨d, hd, rfl⟩ := (hS x).1 hx
    have := hn d hd (fun h => hxe (by rw [h]))
    obtain ⟨h1, h2⟩ := this
    constructor
    · exact_mod_cast h1
    · exact_mod_cast h2

#print axioms firstLap_isolation
#print axioms ratio_imp_firstLap
#print axioms flankProved_or_admissible
#print axioms FirstLapClass_smul
#print axioms firstLap_iff_not_old_field

end Fresh.AdmissibleFlank
