import Fresh.WordExtract

namespace Fresh.WordExtract

open Fresh Fresh.WordCoverSide

/-- A sorted first-reading-pinned instance that admits no strictly
level-increasing word covering the second window. -/
noncomputable def pinnedCounterexample : Fin 7 → ℝ :=
  ![1,16/15,32/27,4/3,16/11,8/5,16/9]

private theorem pinnedBounds (i : Fin 7) :
    1 ≤ pinnedCounterexample i ∧ pinnedCounterexample i ≤ 16/9 := by
  fin_cases i <;> norm_num [pinnedCounterexample]

theorem pinnedWord_noClearPoint :
    ¬ ∃ s, 9 ≤ s ∧ s ≤ 15 ∧
      ∀ i, (1/8 : ℝ) ≤ distInt (pinnedCounterexample i*(s/8)) := by
  rintro ⟨s,hl,hu,clear⟩
  have covered : ∃ i : Fin 7, inZone pinnedCounterexample i 2 s := by
    rcases le_or_gt s (19/2) with h | h
    · exact ⟨6, by
      change ((2 : ℕ) : ℝ) * 8 - 1 < (16/9) * s ∧ (16/9) * s < ((2 : ℕ) : ℝ) * 8 + 1
      norm_num
      constructor <;> linarith⟩
    rcases le_or_gt s (21/2) with h' | h'
    · exact ⟨5, by
      change ((2 : ℕ) : ℝ) * 8 - 1 < (8/5) * s ∧ (8/5) * s < ((2 : ℕ) : ℝ) * 8 + 1
      norm_num
      constructor <;> linarith⟩
    rcases le_or_gt s (23/2) with h'' | h''
    · exact ⟨4, by
      change ((2 : ℕ) : ℝ) * 8 - 1 < (16/11) * s ∧ (16/11) * s < ((2 : ℕ) : ℝ) * 8 + 1
      norm_num
      constructor <;> linarith⟩
    rcases le_or_gt s (127/10) with h₃ | h₃
    · exact ⟨3, by
      change ((2 : ℕ) : ℝ) * 8 - 1 < (4/3) * s ∧ (4/3) * s < ((2 : ℕ) : ℝ) * 8 + 1
      norm_num
      constructor <;> linarith⟩
    rcases le_or_gt s (57/4) with h₄ | h₄
    · exact ⟨2, by
      change ((2 : ℕ) : ℝ) * 8 - 1 < (32/27) * s ∧ (32/27) * s < ((2 : ℕ) : ℝ) * 8 + 1
      norm_num
      constructor <;> linarith⟩
    exact ⟨1, by
      change ((2 : ℕ) : ℝ) * 8 - 1 < (16/15) * s ∧ (16/15) * s < ((2 : ℕ) : ℝ) * 8 + 1
      norm_num
      constructor <;> linarith⟩
  obtain ⟨i,hi⟩ := covered
  exact (not_lt_of_ge (clear i)) (distInt_lt_of_zone hi)

theorem pinnedWord_noWord (w : List (Fin 7 × ℕ)) :
    ¬ WordRealized pinnedCounterexample w := by
  rintro ⟨_,cover,adj⟩
  obtain ⟨p,hp,hzone⟩ := cover 9 (by norm_num) (by norm_num)
  have lo := (pinnedBounds p.1).1
  have hi := (pinnedBounds p.1).2
  have pLev : p.2 = 2 := by
    have l : (1 : ℝ) < p.2 := by linarith [hzone.2]
    have u : (p.2 : ℝ) < 3 := by linarith [hzone.1]
    have l' : 1 < p.2 := by exact_mod_cast l
    have u' : p.2 < 3 := by exact_mod_cast u
    omega
  have pRow : p.1 = 6 := by
    have h := hzone.1
    rw [pLev] at h
    revert h
    generalize p.1 = i
    fin_cases i <;> (norm_num [pinnedCounterexample] <;> try rfl)
  obtain ⟨pre,post,split⟩ := List.mem_iff_append.mp hp
  have post_nil : post = [] := by
    cases post with
    | nil => rfl
    | cons q rest =>
      obtain ⟨j,s,hs,_,hm,hn⟩ := adj p q ⟨pre,rest,split⟩
      have qLev : (3 : ℝ) ≤ q.2 := by exact_mod_cast (show 3 ≤ q.2 by omega)
      have upper : s < 153/16 := by
        have h := hm.2
        rw [pRow,pLev] at h
        change (16/9 : ℝ) * s < ((2 : ℕ) : ℝ) * 8 + 1 at h
        linarith
      have hprod : pinnedCounterexample q.1*s < 17 :=
        (mul_le_mul_of_nonneg_right (pinnedBounds q.1).2 (by linarith)).trans_lt
          (by linarith)
      linarith [hn.1]
  have pre_nil : pre = [] := by
    induction pre using List.reverseRecOn with
    | nil => rfl
    | append_singleton rest q _ =>
      obtain ⟨j,s,hs,_,hm,_⟩ := adj q p ⟨rest,post,by simpa [List.append_assoc] using split⟩
      have qLev : (q.2 : ℝ) ≤ 1 := by exact_mod_cast (show q.2 ≤ 1 by omega)
      have hprod : 9 ≤ pinnedCounterexample q.1*s := by
        have h := mul_le_mul_of_nonneg_right (pinnedBounds q.1).1 (show 0 ≤ s by linarith)
        linarith
      linarith [hm.2]
  have only : w = [p] := by simpa [pre_nil,post_nil] using split
  obtain ⟨q,hq,hz⟩ := cover 15 (by norm_num) (by norm_num)
  rw [only,List.mem_singleton] at hq
  subst q
  have h := hz.2
  rw [pRow,pLev] at h
  change (16/9 : ℝ) * 15 < ((2 : ℕ) : ℝ) * 8 + 1 at h
  norm_num at h

theorem no_universal_pinned_monotone_word :
    ¬ (∀ g : Fin 7 → ℝ, g 0 = 1 → StrictMono g → NoClearPointWordRealized g) := by
  intro h
  have hm : StrictMono pinnedCounterexample := by
    intro i j ij
    fin_cases i <;> fin_cases j <;> norm_num [pinnedCounterexample] at *
  obtain ⟨w,hw⟩ := h pinnedCounterexample (by rfl) hm pinnedWord_noClearPoint
  exact pinnedWord_noWord w hw

#print axioms no_universal_pinned_monotone_word

end Fresh.WordExtract
