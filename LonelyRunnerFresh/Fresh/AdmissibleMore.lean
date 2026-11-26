import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.Admissible
import Fresh.AdmissiblePlus
import Fresh.AdmissibleFlank
import Fresh.FastPairReal
import Fresh.EightResidualLink

/-!
# Two more old rules on real speeds, and the admissible remainder after them

Written 2026-10-25 (owner: "try real forms and then fast pair first").  New file.
* `NoMultipleClass v k` (old R6, `lonely_eight_of_no_multiple_of`): the subject's disparities are integer multiples `n u` of a common real unit `u > 0` and, for some `q ∈ {2, …, 8}`, no multiplier `n` is divisible by `q`.  Then the instant `1/(q u)`
  reads `n/q`, whose circle distance is at least `1/q ≥ 1/8`.  This is a COMMENSURABLE class (readings with a common unit); the unit is part of the class, not an integer reduction of the arrangement.
* `FastPairClass` (`FastPairReal.lean`): the separation-of-scale pair with a `1/6`-clear core instant.
`AdmissibleMore := AdmissibleFlank ∧ ¬ FastPairClass ∧ ¬ NoMultipleClass`; `moreProved_isolation`, `moreProved_or_admissible` (partition), `admissibleMore_iff`.
Links to the old structure for integer disparity sets: `noMultiple_one_iff` (unit 1: exactly the failure of the fields "a multiple of each of 2, …, 8"); `fastPair_imp_old` (the class gives the old `FastPair8` fields).
Grades: [L].  Not claimed: finiteness of the remainder; the thirds, fifths, sixths, free-flank, largest-multiple, descent and block-split rules.
-/

open Classical

namespace Fresh.AdmissibleMore

open Fresh Fresh.Admissible Fresh.AdmissiblePlus Fresh.AdmissibleFlank Fresh.FastPairReal Fresh.EightResidualLink

-- STANDING: DEFINITION
def NoMultipleClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ u : ℝ, 0 < u ∧ ∃ q : ℕ, 2 ≤ q ∧ q ≤ 8 ∧ ∀ d ∈ disparitySet v k, ∃ n : ℕ, d = (n : ℝ) * u ∧ ¬ q ∣ n

theorem frac_clear {n q : ℕ} (hq2 : 2 ≤ q) (hq8 : q ≤ 8) (hn : ¬ q ∣ n) : (1 / 8 : ℝ) ≤ distInt ((n : ℝ) / q) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hq8' : (q : ℝ) ≤ 8 := by exact_mod_cast hq8
  have hr0 : 0 < n % q := by
    rcases Nat.eq_zero_or_pos (n % q) with h | h
    · exact absurd (Nat.dvd_of_mod_eq_zero h) hn
    · exact h
  have hrlt : n % q < q := Nat.mod_lt _ (by omega)
  have hdm := Nat.div_add_mod n q
  have hn' : (n : ℝ) = q * (n / q : ℕ) + (n % q : ℕ) := by exact_mod_cast hdm.symm
  have hy : (n : ℝ) / q = ((n % q : ℕ) : ℝ) / q + ((n / q : ℕ) : ℤ) := by
    rw [Int.cast_natCast, hn']; field_simp; ring
  rw [hy, Fresh.Localisation.distInt_add_int]
  have hr1 : (1 : ℝ) ≤ ((n % q : ℕ) : ℝ) := by exact_mod_cast hr0
  have hr2 : ((n % q : ℕ) : ℝ) ≤ q - 1 := by
    have : n % q + 1 ≤ q := hrlt
    have : ((n % q : ℕ) : ℝ) + 1 ≤ q := by exact_mod_cast this
    linarith
  apply Fresh.Localisation.clear_of_window 0
  · simp only [Int.cast_zero, zero_add]
    rw [le_div_iff₀ hq0]; linarith
  · simp only [Int.cast_zero, zero_add]
    rw [div_le_iff₀ hq0]; nlinarith

theorem noMultiple_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : NoMultipleClass v k) : Isolation v k := by
  obtain ⟨u, hu, q, hq2, hq8, hd⟩ := h
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  refine ⟨1 / (q * u), by positivity, ?_⟩
  rw [Fresh.Localisation.isolatedAt_iff]
  intro d hdm
  obtain ⟨n, hn, hnq⟩ := hd d hdm
  have : d * (1 / ((q : ℝ) * u)) = (n : ℝ) / q := by rw [hn]; field_simp
  rw [this]
  exact frac_clear hq2 hq8 hnq

theorem NoMultipleClass_smul {c : ℝ} (hc : 0 < c) (v : Fin 8 → ℝ) (k : Fin 8) :
    NoMultipleClass (fun j => c * v j) k ↔ NoMultipleClass v k := by
  unfold NoMultipleClass
  constructor
  · rintro ⟨u, hu, q, hq2, hq8, h⟩
    refine ⟨u / c, by positivity, q, hq2, hq8, fun d hd => ?_⟩
    obtain ⟨n, hn, hnq⟩ := h (c * d) ((mem_disp_smul hc v k _).2 ⟨d, hd, rfl⟩)
    exact ⟨n, by rw [show (n : ℝ) * (u / c) = ((n : ℝ) * u) / c by ring, ← hn]; field_simp, hnq⟩
  · rintro ⟨u, hu, q, hq2, hq8, h⟩
    refine ⟨c * u, by positivity, q, hq2, hq8, fun d' hd' => ?_⟩
    obtain ⟨d, hd, rfl⟩ := (mem_disp_smul hc v k d').1 hd'
    obtain ⟨n, hn, hnq⟩ := h d hd
    exact ⟨n, by rw [hn]; ring, hnq⟩

theorem NoMultipleClass_add (s : ℝ) (v : Fin 8 → ℝ) (k : Fin 8) : NoMultipleClass (fun j => v j + s) k ↔ NoMultipleClass v k := by
  have hset : disparitySet (fun j => v j + s) k = disparitySet v k := by
    ext e
    rw [Fresh.Localisation.mem_disparitySet, Fresh.Localisation.mem_disparitySet]
    simp only [habs_add]
  unfold NoMultipleClass
  rw [hset]

theorem FastPairClass_add (s : ℝ) (v : Fin 8 → ℝ) (k : Fin 8) : FastPairClass (fun j => v j + s) k ↔ FastPairClass v k := by
  have hset : disparitySet (fun j => v j + s) k = disparitySet v k := by
    ext e
    rw [Fresh.Localisation.mem_disparitySet, Fresh.Localisation.mem_disparitySet]
    simp only [habs_add]
  unfold FastPairClass
  rw [hset]

-- STANDING: DEFINITION
def MoreProved (v : Fin 8 → ℝ) (k : Fin 8) : Prop := FlankProved v k ∨ FastPairClass v k ∨ NoMultipleClass v k

-- STANDING: DEFINITION
def AdmissibleMore (v : Fin 8 → ℝ) (k : Fin 8) : Prop := IsOrderedArrangement v ∧ ¬ MoreProved v k

theorem moreProved_isolation {v : Fin 8 → ℝ} (hv : IsOrderedArrangement v) {k : Fin 8} (h : MoreProved v k) : Isolation v k := by
  rcases h with h | h | h
  · exact flankProved_isolation hv h
  · exact fastPair_isolation hv.2.injective h
  · exact noMultiple_isolation h

theorem moreProved_or_admissible {v : Fin 8 → ℝ} (hv : IsOrderedArrangement v) (k : Fin 8) :
    MoreProved v k ∨ AdmissibleMore v k := by
  by_cases h : MoreProved v k
  · exact Or.inl h
  · exact Or.inr ⟨hv, h⟩

theorem admissibleMore_iff {v : Fin 8 → ℝ} (k : Fin 8) :
    AdmissibleMore v k ↔ AdmissibleFlank v k ∧ ¬ FastPairClass v k ∧ ¬ NoMultipleClass v k := by
  unfold AdmissibleMore AdmissibleFlank MoreProved
  constructor
  · rintro ⟨ho, hn⟩
    push Not at hn
    exact ⟨⟨ho, hn.1⟩, hn.2.1, hn.2.2⟩
  · rintro ⟨⟨ho, hn⟩, ha, hb⟩
    exact ⟨ho, by push Not; exact ⟨hn, ha, hb⟩⟩

#print axioms frac_clear
#print axioms noMultiple_isolation
#print axioms NoMultipleClass_smul
#print axioms moreProved_isolation
#print axioms admissibleMore_iff

end Fresh.AdmissibleMore
