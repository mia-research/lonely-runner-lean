import Fresh.HarmonicFrontier
import Fresh.HarmonicFrontierChecked
import Fresh.HarmonicSlow

set_option maxRecDepth 4096

namespace Fresh.Harmonic

theorem mem_vectors {n lo top : ℕ} {p : Vector ℕ n}
    (hp : ∀ i : Fin n, lo ≤ p[i.val] ∧ p[i.val] ≤ top)
    (hs : Monotone (fun i : Fin n => p[i.val])) : p ∈ vectors n top lo := by
  induction n generalizing lo with
  | zero =>
    have he : p = #v[] := by
      apply Vector.ext
      intro i hi
      omega
    simp [he,vectors]
  | succ n ih =>
    let a := p[0]
    let tail : Vector ℕ n := Vector.ofFn (fun i => p[i.succ.val])
    have htail : tail ∈ vectors n top a := by
      apply ih
      · intro i
        simp only [tail,Vector.getElem_ofFn]
        exact ⟨hs (Fin.zero_le i.succ), (hp i.succ).2⟩
      · intro i j hij
        simp only [tail,Vector.getElem_ofFn]
        exact hs (Fin.succ_le_succ_iff.mpr hij)
    have hm : a ∈ List.range' lo (top+1-lo) := by
      have h := hp (0 : Fin (n+1))
      change lo ≤ a ∧ a ≤ top at h
      apply List.mem_range'_1.mpr
      exact ⟨h.1, by omega⟩
    apply List.mem_flatMap.mpr
    refine ⟨a,hm,List.mem_map.mpr ⟨tail,htail,?_⟩⟩
    apply Vector.ext
    intro i hi
    obtain ⟨i, rfl⟩ : ∃ j : Fin (n+1), j.val=i := ⟨⟨i,hi⟩,rfl⟩
    cases i using Fin.cases <;> simp [a,tail]

theorem four_catalogue_phase {p : Vector ℕ 4} (hm : p ∈ fourCatalogue)
    (hp : ∀ i : Fin 4, 0 < p[i.val]) (hs : Monotone (fun i : Fin 4 => p[i.val])) :
    ClearsTwice p (13/100) := by
  have hc := (Bool.and_eq_true_iff.mp four_catalogue_checked).2
  exact clears_twice_of_replay hp hs (List.all_eq_true.mp hc p hm)

theorem five_frontier_phase {p : Vector ℕ 5} (hm : p ∈ fiveFrontier)
    (hp : ∀ i : Fin 5, 0 < p[i.val]) (hs : Monotone (fun i : Fin 5 => p[i.val])) :
    ClearsTwice p (13/100) := by
  have hc := (Bool.and_eq_true_iff.mp five_frontier_checked).2
  exact clears_twice_of_replay hp hs (List.all_eq_true.mp hc p hm)


#print axioms four_catalogue_phase
#print axioms five_frontier_phase


/-- The full sorted mixed five-reading range from 11 through 18. -/
theorem five_range_phase {p : Vector ℕ 5}
    (hp : ∀ i : Fin 5, 0 < p[i.val] ∧ p[i.val] ≤ 18)
    (hmax : 10 < p[4]) (hs : Monotone (fun i : Fin 5 => p[i.val]))
    (hm : mixed p = true) : ClearsTwice p (13/100) := by
  have hmem : p ∈ fiveFrontier := by
    apply List.mem_filter.mpr
    exact ⟨mem_vectors hp hs, by simp [hmax,hm]⟩
  exact five_frontier_phase hmem (fun i => (hp i).1) hs

private theorem core_facts {p : Vector ℕ 4} (hp : p ∈ cores) :
    p ∈ fourCatalogue ∧ (∀ i : Fin 4, 0 < p[i.val] ∧ p[i.val] ≤ p[3]) ∧
      Monotone (fun i : Fin 4 => p[i.val]) ∧ p[3] ≤ 3 := by
  simp only [cores,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl
  all_goals
    refine ⟨by decide,?_,?_,by decide⟩
    · intro i
      fin_cases i <;> decide
    · apply Fin.monotone_iff_le_succ.2
      intro i
      fin_cases i <;> decide

/-- All appended maxima from 11 onward for the three four-reading cores.
The replay is used only below the threshold of the phase-window lemma. -/
theorem all_appended_maxima {p : Vector ℕ 4} (hp : p ∈ cores) {n : ℕ} (hn : 11 ≤ n) :
    ClearsTwice (appendSlope p n) (1251/10000) := by
  obtain ⟨hmem,hp',hs,hmax⟩ := core_facts hp
  by_cases hlarge : 26*p[3] ≤ n
  · exact separated_append (fun i => (hp' i).2) (hp' 3).1 hlarge
      (four_catalogue_phase hmem (fun i => (hp' i).1) hs)
  · have hc := List.all_eq_true.mp append_slopes_checked p hp
    have hnm : n ∈ List.range' 11 (26*p[3]-11) := by
      apply List.mem_range'_1.mpr
      omega
    have hchecked := List.all_eq_true.mp hc n hnm
    have hpos (i : Fin 5) : 0 < (appendSlope p n)[i.val] := by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa [appendSlope,Vector.getElem_push] using (show 0 < n by omega)
      · simpa [appendSlope,Vector.getElem_push,j.isLt] using (hp' j).1
    have hs' : Monotone (fun i : Fin 5 => (appendSlope p n)[i.val]) := by
      apply Fin.monotone_iff_le_succ.2
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa [appendSlope,Vector.getElem_push] using (show p[3] ≤ n by omega)
      · have hj : j.val+1 < 4 := j.succ.isLt
        change (appendSlope p n)[j.val] ≤ (appendSlope p n)[j.val+1]
        have hj0 : j.val < 4 := by omega
        simp only [appendSlope,Vector.getElem_push,dif_pos hj0,dif_pos hj]
        exact hs (show j.castSucc ≤ j.succ from Fin.castSucc_le_succ j)
    intro x
    obtain ⟨m,hm,φ,hφ⟩ := clears_twice_of_replay hpos hs' hchecked x
    exact ⟨m,hm,φ,fun i => (by norm_num : (1251/10000:ℝ) ≤ 13/100).trans (hφ i)⟩

#print axioms five_range_phase
#print axioms all_appended_maxima



/-- Transfer a two-dilation phase certificate to the actual fast rates
and the two slow readings. The margin controls the permitted drift. -/
theorem five_rates_of_twice (p : Vector ℕ 5) (b : Fin 5 → ℝ)
    {a B frequency margin : ℝ} (ha : 1 ≤ a) (hslow : 40*a ≤ frequency)
    (hfast : B/(2*frequency) ≤ margin) (hb : ∀ i, |b i| ≤ B)
    (phase : ClearsTwice p (1/8+margin)) :
    ∃ s, InWindows s ∧ (1/8 : ℝ) ≤ distInt s ∧ (1/8 : ℝ) ≤ distInt (a*s) ∧
      ∀ i, (1/8 : ℝ) ≤ distInt (((p.get i : ℝ)*frequency+b i)*s) := by
  classical
  obtain ⟨t,ht⟩ := slow125 a ha
  obtain ⟨m,hm,φ,hφ⟩ := phase (fun i => b i*t)
  have hm' : m ∈ ([1,2,5] : List ℕ) := by
    simp at hm ⊢
    omega
  obtain ⟨hw,hclear⟩ := ht m hm'
  have hpos : 0 < frequency := by linarith
  obtain ⟨s,hs,_,slow,fast⟩ := lift_with_margin (t := (m:ℝ)*t) (φ := φ) ({1,a} : Finset ℝ)
    (e := 1/80) (B := B) (fun i : Fin 5 => p.get i) b hpos ha
    ((div_le_iff₀ (by positivity)).2 (by linarith)) hfast hw
    (by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact ⟨by simpa using ha, by simpa using pinned_buffer hw⟩
      · exact ⟨by rw [abs_of_nonneg (by linarith)], by linarith⟩)
    hb (fun i => by convert hφ i using 2; ring)
  exact ⟨s,hs,by simpa using slow 1 (by simp),slow a (by simp),fast⟩

/-- The three unbounded appended-slope families, for actual rates. -/
theorem appended_rates {p : Vector ℕ 4} (hp : p ∈ cores) {n : ℕ} (hn : 11 ≤ n)
    (b : Fin 5 → ℝ) {a B frequency : ℝ} (ha : 1 ≤ a) (hslow : 40*a ≤ frequency)
    (hfast : 5000*B ≤ frequency) (hb : ∀ i, |b i| ≤ B) :
    ∃ s, InWindows s ∧ (1/8 : ℝ) ≤ distInt s ∧ (1/8 : ℝ) ≤ distInt (a*s) ∧
      ∀ i, (1/8 : ℝ) ≤ distInt ((((appendSlope p n).get i : ℝ)*frequency+b i)*s) := by
  have hpos : 0 < frequency := by linarith
  refine five_rates_of_twice _ b (margin := 1/10000) ha hslow ?_ hb ?_
  · exact (div_le_iff₀ (by positivity)).2 (by linarith)
  · rw [show (1/8+1/10000:ℝ) = 1251/10000 by norm_num]
    exact all_appended_maxima hp hn

theorem five_range_rates (p : Vector ℕ 5) (b : Fin 5 → ℝ)
    (hp : ∀ i : Fin 5, 0 < p[i.val] ∧ p[i.val] ≤ 18)
    (hmax : 10 < p[4]) (hs : Monotone (fun i : Fin 5 => p[i.val]))
    (hm : mixed p = true) {a B frequency : ℝ} (ha : 1 ≤ a)
    (hslow : 40*a ≤ frequency) (hfast : 100*B ≤ frequency)
    (hb : ∀ i, |b i| ≤ B) :
    ∃ s, InWindows s ∧ (1/8 : ℝ) ≤ distInt s ∧ (1/8 : ℝ) ≤ distInt (a*s) ∧
      ∀ i, (1/8 : ℝ) ≤ distInt (((p.get i : ℝ)*frequency+b i)*s) := by
  have hpos : 0 < frequency := by linarith
  refine five_rates_of_twice p b (margin := 1/200) ha hslow ?_ hb ?_
  · exact (div_le_iff₀ (by positivity)).2 (by linarith)
  · rw [show (1/8+1/200:ℝ) = 13/100 by norm_num]
    exact five_range_phase hp hmax hs hm

#print axioms five_range_rates
#print axioms five_rates_of_twice
#print axioms appended_rates

end Fresh.Harmonic
