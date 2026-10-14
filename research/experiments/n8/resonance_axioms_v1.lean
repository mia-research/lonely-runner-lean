import LonelyRunner.LRC.Spec.ResonanceN
open LRC.Resonance
instance : Fact (2 ≤ 5) := ⟨by norm_num⟩
instance : Fact (2 ≤ 7) := ⟨by norm_num⟩
instance : Fact (2 ≤ 8) := ⟨by norm_num⟩

theorem res_five  {m : ℕ} : Resonant 5 m ↔ 5 ∣ m := resonant_iff_dvd_of_prime (by decide)
theorem res_seven {m : ℕ} : Resonant 7 m ↔ 7 ∣ m := resonant_iff_dvd_of_prime (by decide)
example : Resonant 8 2 ∧ ¬ (8 ∣ 2) := ⟨by decide, by decide⟩
example : Resonant 8 4 ∧ ¬ (8 ∣ 4) := ⟨by decide, by decide⟩
example : Resonant 9 3 ∧ ¬ (9 ∣ 3) := ⟨by decide, by decide⟩

-- the order-7 theorem, instantiated
theorem seven_flank {S : Finset ℕ} {e : ℕ} (he : 0 < e) (hen : ¬ (7 ∣ e))
    (hS : ∀ d ∈ S, ¬ (7 ∣ d)) :
    ∃ j : ℕ, MomentIterationN.Lonely 7 (Finset.image (fun d : ℕ => (d : ℝ)) S)
      (Flanks.flankOpening 7 (e : ℝ) j) :=
  lonely_flank_of_prime_image (by decide) he hen hS

#print axioms LRC.Resonance.resonant_iff_dvd_of_prime
#print axioms LRC.Resonance.lonelyForSubject_of_no_resonance
#print axioms LRC.Resonance.doors_of_no_resonance
#print axioms LRC.Resonance.flankWorks_of_prime
#print axioms LRC.Resonance.lonely_flank_of_prime
#print axioms LRC.Resonance.lonely_flank_of_prime_image
#print axioms res_seven
#print axioms seven_flank
