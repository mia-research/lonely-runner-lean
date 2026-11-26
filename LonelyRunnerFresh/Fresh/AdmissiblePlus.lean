import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.Admissible
import Fresh.APLawR3_All8
import Fresh.OneMoverS1Self

/-!
# Admissible arrangements, with the AP-neighbourhood and one-mover classes added

Written 2026-10-25 (owner: "Add classes and then link eightresidual").  New file.  Two further proved classes, real speeds, scale invariant:
* `APNbhdClass v`: speeds within `d/16` of an arithmetic progression `c + i d` (`ap_nbhd_firstIso_8`, relative radius `1/16`; for the interior subjects this is `ap_interior_firstIso_max`):
  every subject has a first isolation.
* `OneMoverClass v`: an arithmetic progression `c + i` with one runner `m` moved to any positive speed `x`, scaled by `d > 0` (`s1_all`): every subject is isolated.
`ProvedPlus := Proved ∨ APNbhdClass ∨ OneMoverClass`, `AdmissiblePlus := IsOrderedArrangement ∧ ¬ProvedPlus`.
`provedPlus_isolation`, `provedPlus_or_admissiblePlus` (partition), `APNbhdClass_smul`, `OneMoverClass_smul`, `APNbhdClass_add`, `admissiblePlus_iff`: `AdmissiblePlus` is `Admissible` minus the two classes.
Grades: [L].  Not claimed: finiteness of the remainder; the two-mover classes of E557 to E573 (they carry hypotheses on the disparities and are not added).
-/

open Classical

namespace Fresh.AdmissiblePlus

open Fresh Fresh.OneMover Fresh.Admissible

theorem isolatedAt_smul {d : ℝ} (hd : 0 < d) (u : Fin 8 → ℝ) (k : Fin 8) (t : ℝ) :
    IsolatedAt (fun j => d * u j) k t ↔ IsolatedAt u k (d * t) := by
  unfold IsolatedAt
  refine forall₂_congr fun i _ => ?_
  have : (d * u i - d * u k) * t = (u i - u k) * (d * t) := by ring
  show (1 / 8 : ℝ) ≤ distInt ((d * u i - d * u k) * t) ↔ _
  rw [this]

theorem isolation_smul {d : ℝ} (hd : 0 < d) (u : Fin 8 → ℝ) (k : Fin 8) (h : Isolation u k) :
    Isolation (fun j => d * u j) k := by
  obtain ⟨t, ht, hiso⟩ := h
  refine ⟨t / d, by positivity, ?_⟩
  rw [isolatedAt_smul hd]
  have : d * (t / d) = t := by field_simp
  rw [this]; exact hiso

-- STANDING: DEFINITION
def APNbhdClass (v : Fin 8 → ℝ) : Prop := ∃ d c : ℝ, 0 < d ∧ ∀ i : Fin 8, |v i - (c + ((i : ℕ) : ℝ) * d)| ≤ d / 16

-- STANDING: DEFINITION
def OneMoverClass (v : Fin 8 → ℝ) : Prop :=
  ∃ (d c x : ℝ) (m : Fin 8), 0 < d ∧ 0 < c ∧ 0 < x ∧ (∀ p : Fin 8, p ≠ m → x ≠ c + ((p : ℕ) : ℝ)) ∧
    ∀ j, v j = d * oneMover c x m j

-- STANDING: DEFINITION
def ProvedPlus (v : Fin 8 → ℝ) (k : Fin 8) : Prop := Proved v k ∨ APNbhdClass v ∨ OneMoverClass v

-- STANDING: DEFINITION
def AdmissiblePlus (v : Fin 8 → ℝ) (k : Fin 8) : Prop := IsOrderedArrangement v ∧ ¬ ProvedPlus v k

theorem apNbhd_isolation {v : Fin 8 → ℝ} (h : APNbhdClass v) (k : Fin 8) : Isolation v k := by
  obtain ⟨d, c, hd, hv⟩ := h
  have hu : ∀ i : Fin 8, |(fun j => v j / d) i - (c / d + ((i : ℕ) : ℝ))| ≤ 1 / 16 := by
    intro i
    have h1 := hv i
    show |v i / d - (c / d + ((i : ℕ) : ℝ))| ≤ 1 / 16
    have : v i / d - (c / d + ((i : ℕ) : ℝ)) = (v i - (c + ((i : ℕ) : ℝ) * d)) / d := by field_simp
    rw [this, abs_div, abs_of_pos hd, div_le_iff₀ hd]
    linarith
  obtain ⟨T, hT, hF⟩ := ap_nbhd_firstIso_8 (c / d) (fun j => v j / d) hu k
  have hiso : Isolation (fun j => v j / d) k := ⟨T, hT, hF.1⟩
  have := isolation_smul hd _ k hiso
  have e : (fun j => d * (v j / d)) = v := by funext j; field_simp
  rwa [e] at this

theorem oneMover_isolation {v : Fin 8 → ℝ} (h : OneMoverClass v) (k : Fin 8) : Isolation v k := by
  obtain ⟨d, c, x, m, hd, hc, hx0, hx, hv⟩ := h
  have := isolation_smul hd _ k ((s1_all c x m hc hx0 hx).2 k)
  have e : v = (fun j => d * oneMover c x m j) := funext hv
  rwa [← e] at this

theorem provedPlus_isolation {v : Fin 8 → ℝ} (hv : IsOrderedArrangement v) {k : Fin 8} (h : ProvedPlus v k) : Isolation v k := by
  rcases h with h | h | h
  · exact proved_isolation hv h
  · exact apNbhd_isolation h k
  · exact oneMover_isolation h k

theorem provedPlus_or_admissiblePlus {v : Fin 8 → ℝ} (hv : IsOrderedArrangement v) (k : Fin 8) :
    ProvedPlus v k ∨ AdmissiblePlus v k := by
  by_cases h : ProvedPlus v k
  · exact Or.inl h
  · exact Or.inr ⟨hv, h⟩

theorem APNbhdClass_smul {c : ℝ} (hc : 0 < c) (v : Fin 8 → ℝ) : APNbhdClass (fun j => c * v j) ↔ APNbhdClass v := by
  unfold APNbhdClass
  constructor
  · rintro ⟨d, c0, hd, h⟩
    refine ⟨d / c, c0 / c, by positivity, fun i => ?_⟩
    have h1 := h i
    show |v i - (c0 / c + ((i : ℕ) : ℝ) * (d / c))| ≤ d / c / 16
    have : v i - (c0 / c + ((i : ℕ) : ℝ) * (d / c)) = (c * v i - (c0 + ((i : ℕ) : ℝ) * d)) / c := by field_simp
    rw [this, abs_div, abs_of_pos hc]
    have h2 : |c * v i - (c0 + ((i : ℕ) : ℝ) * d)| ≤ d / 16 := h1
    have h3 : d / c / 16 = (d / 16) / c := by ring
    rw [h3]
    exact div_le_div_of_nonneg_right h2 hc.le
  · rintro ⟨d, c0, hd, h⟩
    refine ⟨c * d, c * c0, by positivity, fun i => ?_⟩
    have h1 := h i
    show |c * v i - (c * c0 + ((i : ℕ) : ℝ) * (c * d))| ≤ c * d / 16
    have : c * v i - (c * c0 + ((i : ℕ) : ℝ) * (c * d)) = c * (v i - (c0 + ((i : ℕ) : ℝ) * d)) := by ring
    rw [this, abs_mul, abs_of_pos hc]
    nlinarith

theorem APNbhdClass_add (s : ℝ) (v : Fin 8 → ℝ) : APNbhdClass (fun j => v j + s) ↔ APNbhdClass v := by
  unfold APNbhdClass
  constructor
  · rintro ⟨d, c0, hd, h⟩
    exact ⟨d, c0 - s, hd, fun i => by
      have h1 : |v i + s - (c0 + ((i : ℕ) : ℝ) * d)| ≤ d / 16 := h i
      have : v i - (c0 - s + ((i : ℕ) : ℝ) * d) = v i + s - (c0 + ((i : ℕ) : ℝ) * d) := by ring
      rw [this]; exact h1⟩
  · rintro ⟨d, c0, hd, h⟩
    exact ⟨d, c0 + s, hd, fun i => by
      have h1 := h i
      have : v i + s - (c0 + s + ((i : ℕ) : ℝ) * d) = v i - (c0 + ((i : ℕ) : ℝ) * d) := by ring
      show |v i + s - (c0 + s + ((i : ℕ) : ℝ) * d)| ≤ d / 16
      rw [this]; exact h1⟩

theorem OneMoverClass_smul {c : ℝ} (hc : 0 < c) (v : Fin 8 → ℝ) : OneMoverClass (fun j => c * v j) ↔ OneMoverClass v := by
  unfold OneMoverClass
  constructor
  · rintro ⟨d, c0, x, m, hd, hc0, hx0, hx, hv⟩
    refine ⟨d / c, c0, x, m, by positivity, hc0, hx0, hx, fun j => ?_⟩
    have h := hv j
    have h' : c * v j = d * oneMover c0 x m j := h
    field_simp
    linarith
  · rintro ⟨d, c0, x, m, hd, hc0, hx0, hx, hv⟩
    exact ⟨c * d, c0, x, m, by positivity, hc0, hx0, hx, fun j => by show c * v j = _; rw [hv j]; ring⟩

theorem admissiblePlus_iff {v : Fin 8 → ℝ} (k : Fin 8) :
    AdmissiblePlus v k ↔ Admissible v k ∧ ¬ APNbhdClass v ∧ ¬ OneMoverClass v := by
  unfold AdmissiblePlus Admissible ProvedPlus
  constructor
  · rintro ⟨ho, hn⟩
    push Not at hn
    exact ⟨⟨ho, hn.1⟩, hn.2.1, hn.2.2⟩
  · rintro ⟨⟨ho, hn⟩, ha, hb⟩
    exact ⟨ho, by push Not; exact ⟨hn, ha, hb⟩⟩

theorem admissiblePlus_imp_admissible {v : Fin 8 → ℝ} {k : Fin 8} (h : AdmissiblePlus v k) : Admissible v k :=
  ((admissiblePlus_iff k).1 h).1

#print axioms provedPlus_isolation
#print axioms provedPlus_or_admissiblePlus
#print axioms APNbhdClass_smul
#print axioms OneMoverClass_smul
#print axioms admissiblePlus_iff

end Fresh.AdmissiblePlus
