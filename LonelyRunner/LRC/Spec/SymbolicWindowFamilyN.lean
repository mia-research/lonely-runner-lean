import LonelyRunner.LRC.Spec.SymbolicWindowTransportN

/-!
# A six-parameter family transported from the AP through four lap windows

The six target speeds vary independently around (1,50,105,106,136,189),
with endpoints 0 and 199. All real deformation parameters are covered.
The lap assignments were discovered experimentally; this theorem checks a
continuous family, but does not select labels for arbitrary arrangements.
-/

namespace LRC.SymbolicWindowFamily

noncomputable def target (y : Fin 6 → ℝ) : Fin 7 → ℝ :=
  ![y 0, y 1, y 2, y 3, y 4, y 5, 199]

def laps : Fin 4 → Fin 7 → ℕ :=
  ![![0,0,1,1,1,2,2], ![0,1,2,2,3,4,5],
    ![0,4,9,9,12,17,18], ![0,6,13,13,17,23,25]]

noncomputable def knots : Fin 5 → ℝ := ![0, 2/3, 6/7, 49/50, 1]

set_option maxHeartbeats 2400000 in
-- The eight endpoints have 49 linear constraints each; all are kernel checked.
/-- Eight endpoint checks establish four whole parameter intervals.
There is no cascade run, floating point, or assumed clearance in this proof. -/
theorem endpoint_inequalities (y : Fin 6 → ℝ)
    (hy : ∀ i, |y i - (![1,50,105,106,136,189] : Fin 6 → ℝ) i| ≤ 1/192)
    (w : Fin 4) (e : Fin 2) (i j : Fin 7) :
    let s := knots ⟨w.val + e.val, by omega⟩
    (8 * (laps w i : ℝ)+1) * ((1-s)*(j.val+1)+s*(7/199*target y j)) ≤
      (8 * (laps w j : ℝ)+7) * ((1-s)*(i.val+1)+s*(7/199*target y i)) := by
  have h0 := abs_le.mp (hy 0)
  have h1 := abs_le.mp (hy 1)
  have h2 := abs_le.mp (hy 2)
  have h3 := abs_le.mp (hy 3)
  have h4 := abs_le.mp (hy 4)
  have h5 := abs_le.mp (hy 5)
  change -(1/192 : ℝ) ≤ y 0 - 1 ∧ y 0 - 1 ≤ 1/192 at h0
  change -(1/192 : ℝ) ≤ y 1 - 50 ∧ y 1 - 50 ≤ 1/192 at h1
  change -(1/192 : ℝ) ≤ y 2 - 105 ∧ y 2 - 105 ≤ 1/192 at h2
  change -(1/192 : ℝ) ≤ y 3 - 106 ∧ y 3 - 106 ≤ 1/192 at h3
  change -(1/192 : ℝ) ≤ y 4 - 136 ∧ y 4 - 136 ≤ 1/192 at h4
  change -(1/192 : ℝ) ≤ y 5 - 189 ∧ y 5 - 189 ≤ 1/192 at h5
  fin_cases w <;> fin_cases e <;> fin_cases i <;> fin_cases j <;>
    norm_num [knots, laps, target] <;> linarith

/-- For every point in the six-dimensional target box and every intermediate
real deformation, the seven disparities admit a positive isolation time. -/
theorem family_clear (y : Fin 6 → ℝ)
    (hy : ∀ i, |y i - (![1,50,105,106,136,189] : Fin 6 → ℝ) i| ≤ 1/192)
    (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    ∃ t : ℝ, 0 < t ∧ ∀ i : Fin 7,
      1/8 ≤ circDist
        (((1-s)*(i.val+1)+s*(7/199*target y i))*t) := by
  have ha : ∀ i ∈ (Finset.univ : Finset (Fin 7)), 0 < ((i.val : ℝ)+1) := by
    intro i _
    positivity
  have hd : ∀ i ∈ (Finset.univ : Finset (Fin 7)), 0 < 7/199*target y i := by
    have h0 := (abs_le.mp (hy 0)).1
    have h1 := (abs_le.mp (hy 1)).1
    have h2 := (abs_le.mp (hy 2)).1
    have h3 := (abs_le.mp (hy 3)).1
    have h4 := (abs_le.mp (hy 4)).1
    have h5 := (abs_le.mp (hy 5)).1
    change -(1/192 : ℝ) ≤ y 0 - 1 at h0
    change -(1/192 : ℝ) ≤ y 1 - 50 at h1
    change -(1/192 : ℝ) ≤ y 2 - 105 at h2
    change -(1/192 : ℝ) ≤ y 3 - 106 at h3
    change -(1/192 : ℝ) ≤ y 4 - 136 at h4
    change -(1/192 : ℝ) ≤ y 5 - 189 at h5
    intro i _
    fin_cases i <;> norm_num [target] <;> linarith
  have local_cover (w : Fin 4)
      (hl : knots ⟨w.val, by omega⟩ ≤ s)
      (hr : s ≤ knots ⟨w.val+1, by omega⟩) :
      ∃ t : ℝ, 0 < t ∧ ∀ i : Fin 7,
        1/8 ≤ circDist
          (((1-s)*(i.val+1)+s*(7/199*target y i))*t) := by
    obtain ⟨t, ht, hb⟩ := SymbolicWindowTransport.positive_windows_between
      Finset.univ (Finset.univ_nonempty) (fun i : Fin 7 => (i.val : ℝ)+1)
      (fun i => 7/199*target y i) (laps w) ha hd hs hs1 hl hr
      (fun i _ j _ => by simpa using endpoint_inequalities y hy w 0 i j)
      (fun i _ j _ => by simpa using endpoint_inequalities y hy w 1 i j)
    refine ⟨t, ht, fun i => ?_⟩
    have h := hb i (Finset.mem_univ i)
    simpa using TwoPinner.clear_of_band (N := (laps w i : ℤ))
      (by simpa using h.1) (by simpa using h.2)
  by_cases h0 : s ≤ 2/3
  · exact local_cover 0 (by simpa [knots] using hs) (by simpa [knots] using h0)
  by_cases h1 : s ≤ 6/7
  · exact local_cover 1 (by simp [knots]; linarith) (by simpa [knots] using h1)
  by_cases h2 : s ≤ 49/50
  · exact local_cover 2 (by simp [knots]; linarith) (by simpa [knots] using h2)
  · exact local_cover 3 (by simp [knots]; linarith) (by simpa [knots] using hs1)

/-- The family result implies the existing arrangement-level loneliness
predicate for the endpoint subject, not just an auxiliary band predicate. -/
theorem family_lonely (y : Fin 6 → ℝ)
    (hy : ∀ i, |y i - (![1,50,105,106,136,189] : Fin 6 → ℝ) i| ≤ 1/192)
    (s : ℝ) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    ∃ t : ℝ, 0 < t ∧ Arrangement.LonelyAt
      (Fin.cases 0 (fun i : Fin 7 => (1-s)*(i.val+1)+s*(7/199*target y i))) 0 t := by
  obtain ⟨t, ht, hc⟩ := family_clear y hy s hs hs1
  refine ⟨t, ht, ?_⟩
  intro i hi
  cases i using Fin.cases with
  | zero => exact False.elim (hi rfl)
  | succ j => simpa [Arrangement.sep] using hc j

end LRC.SymbolicWindowFamily
