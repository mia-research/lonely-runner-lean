import Fresh.NativeRecoveredPacketBands
import Fresh.Admissible

/-! A native packet resumption chart found in the continuing reset inputs.
The integer label is unbounded, four deviations are independent, and all
seven terminal windows are derived. No endpoint-clearance premise is used.
The physical subject remains moving and arbitrary positive scale is kept. -/
open Classical
namespace Fresh.NativeRebasedPacketChart
open Fresh Fresh.Cascade Fresh.Localisation Fresh.NativeEntryLabels Fresh.NativeReturnSurvivors
  Fresh.NativeReturnHandoff Fresh.NativeOneReaderDeformation Fresh.NativeOpeningReversal
  Fresh.NativeThirdReaderRetention Fresh.NativeFixedPrefixArrangement

noncomputable def coeff (N : ℕ) (e h z w : ℝ) : Fin 7 → ℝ :=
  ![12*(N : ℝ)+3/8,15*(N : ℝ)+3/8,24*(N : ℝ)+3/8,30*(N : ℝ)+z,
    36*(N : ℝ)+w,40*(N : ℝ)-5/24+h,120*(N : ℝ)-1/8+e]

noncomputable def terminalLabel (N : ℕ) : Fin 7 → ℤ :=
  ![12*(N : ℤ)+1,15*(N : ℤ)+1,24*(N : ℤ)+1,30*(N : ℤ)+2,
    36*(N : ℤ)+2,40*(N : ℤ)+2,120*(N : ℤ)+7]

noncomputable def resumption (N : ℕ) : ℝ := (12*(N : ℝ)+9/8)/(12*(N : ℝ)+3/8)
noncomputable def priorOpening (N : ℕ) : ℝ := (15*(N : ℝ)+9/8)/(15*(N : ℝ)+3/8)

-- STANDING: DEFINITION
noncomputable def Parameters (N : ℕ) (e h z w : ℝ) : Prop :=
  1 ≤ N ∧ 0 ≤ e ∧ e ≤ 1/8 ∧ 0 ≤ h ∧ h ≤ 1/8 ∧ 3/8 ≤ z ∧ z ≤ 3/4 ∧ 3/8 ≤ w ∧ w ≤ 1/2

theorem opening_times_positive (N : ℕ) (hN : 1 ≤ N) : 0<priorOpening N ∧ 0<resumption N := by
  have hn : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  dsimp [priorOpening,resumption]
  constructor <;> apply div_pos <;> nlinarith only [hn]

theorem terminal_windows (N : ℕ) (e h z w : ℝ) (hp : Parameters N e h z w) (i : Fin 7) :
    (terminalLabel N i : ℝ)+1/8 ≤ coeff N e h z w i*resumption N ∧
      coeff N e h z w i*resumption N ≤ (terminalLabel N i : ℝ)+7/8 := by
  obtain ⟨hN,he0,he1,hh0,hh1,hz0,hz1,hw0,hw1⟩ := hp
  have hn : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hden : 0<12*(N : ℝ)+3/8 := by nlinarith only [hn]
  have hnum : 0 ≤ 12*(N : ℝ)+9/8 := by nlinarith only [hn]
  have helo := mul_nonneg he0 hnum
  have hehi := mul_nonneg (sub_nonneg.mpr he1) hnum
  have hhlo := mul_nonneg hh0 hnum
  have hhhi := mul_nonneg (sub_nonneg.mpr hh1) hnum
  have hzlo := mul_nonneg (sub_nonneg.mpr hz0) hnum
  have hzhi := mul_nonneg (sub_nonneg.mpr hz1) hnum
  have hwlo := mul_nonneg (sub_nonneg.mpr hw0) hnum
  have hwhi := mul_nonneg (sub_nonneg.mpr hw1) hnum
  fin_cases i <;> dsimp [coeff,terminalLabel,resumption] <;> push_cast <;> constructor
  all_goals rw [←mul_div_assoc]
  all_goals first | rw [le_div_iff₀ hden] | rw [div_le_iff₀ hden]
  all_goals nlinarith only [hn,helo,hehi,hhlo,hhhi,hzlo,hzhi,hwlo,hwhi]

theorem coeff_clear (N : ℕ) (e h z w : ℝ) (hp : Parameters N e h z w) (i : Fin 7) :
    (1/8 : ℝ) ≤ distInt (coeff N e h z w i*resumption N) := by
  have hh := terminal_windows N e h z w hp i
  exact clear_of_window (terminalLabel N i) hh.1 hh.2

theorem coeff_positive (N : ℕ) (e h z w : ℝ) (hp : Parameters N e h z w) (i : Fin 7) : 0<coeff N e h z w i := by
  have hn : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hp.1
  obtain ⟨hN,he0,he1,hh0,hh1,hz0,hz1,hw0,hw1⟩ := hp
  fin_cases i <;> dsimp [coeff] <;> nlinarith only [hn,he0,hh0,hz0,hw0]

-- The preceding eighth opening forces the tenth reader's next opening.
theorem resumption_gate (N : ℕ) (hN : 1 ≤ N) :
    |(12*(N : ℝ)+3/8)*priorOpening N-((12*(N : ℤ)+1 : ℤ) : ℝ)|<1/8 ∧
      nextOpening (12*(N : ℝ)+3/8) (priorOpening N)=resumption N := by
  have hn : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hden : 0<15*(N : ℝ)+3/8 := by nlinarith only [hn]
  have hab : |(12*(N : ℝ)+3/8)*priorOpening N-((12*(N : ℤ)+1 : ℤ) : ℝ)|<1/8 := by
    rw [abs_lt]
    push_cast
    dsimp [priorOpening]
    constructor
    · have hh : 12*(N : ℝ)+7/8 < (12*(N : ℝ)+3/8)*((15*(N : ℝ)+9/8)/(15*(N : ℝ)+3/8)) := by
        rw [←mul_div_assoc,lt_div_iff₀ hden]
        nlinarith only [hn]
      linarith only [hh]
    · have hh : (12*(N : ℝ)+3/8)*((15*(N : ℝ)+9/8)/(15*(N : ℝ)+3/8)) < 12*(N : ℝ)+9/8 := by
        rw [←mul_div_assoc,div_lt_iff₀ hden]
        nlinarith only [hn]
      linarith only [hh]
  refine ⟨hab,?_⟩
  rw [nextOpening_eq hab]
  dsimp [resumption]
  push_cast
  congr 1 <;> ring

noncomputable def physical (N : ℕ) (e h z w : ℝ) : Fin 8 → ℝ :=
  ![1,1+(12*(N : ℝ)+3/8),1+(15*(N : ℝ)+3/8),1+(24*(N : ℝ)+3/8),
    1+(30*(N : ℝ)+z),1+(36*(N : ℝ)+w),1+(40*(N : ℝ)-5/24+h),1+(120*(N : ℝ)-1/8+e)]

theorem physical_admissible (N : ℕ) (e h z w : ℝ) (hp : Parameters N e h z w) : IsArrangement (physical N e h z w) := by
  have hn : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hp.1
  obtain ⟨hN,he0,he1,hh0,hh1,hz0,hz1,hw0,hw1⟩ := hp
  have hmono : StrictMono (physical N e h z w) := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i
    · change (1 : ℝ)<1+(12*(N : ℝ)+3/8)
      nlinarith only [hn]
    · change 1+(12*(N : ℝ)+3/8)<1+(15*(N : ℝ)+3/8)
      nlinarith only [hn]
    · change 1+(15*(N : ℝ)+3/8)<1+(24*(N : ℝ)+3/8)
      nlinarith only [hn]
    · change 1+(24*(N : ℝ)+3/8)<1+(30*(N : ℝ)+z)
      nlinarith only [hn,hz0]
    · change 1+(30*(N : ℝ)+z)<1+(36*(N : ℝ)+w)
      nlinarith only [hn,hz1,hw0]
    · change 1+(36*(N : ℝ)+w)<1+(40*(N : ℝ)-5/24+h)
      nlinarith only [hn,hh0,hw1]
    · change 1+(40*(N : ℝ)-5/24+h)<1+(120*(N : ℝ)-1/8+e)
      nlinarith only [hn,hh1,he0]
  refine ⟨?_,hmono.injective⟩
  intro i
  have hh := hmono.monotone (Fin.zero_le i)
  have hz : physical N e h z w 0=1 := rfl
  rw [hz] at hh
  exact lt_of_lt_of_le (by norm_num) hh

theorem physical_isolation (N : ℕ) (e h z w : ℝ) (hp : Parameters N e h z w) : Isolation (physical N e h z w) 0 := by
  refine ⟨resumption N,(opening_times_positive N hp.1).2,?_⟩
  intro i hi
  fin_cases i
  · exact (hi rfl).elim
  all_goals norm_num [physical]
  · simpa only [coeff,Matrix.cons_val_zero] using coeff_clear N e h z w hp 0
  · simpa [coeff] using coeff_clear N e h z w hp 1
  · simpa [coeff] using coeff_clear N e h z w hp 2
  · simpa [coeff] using coeff_clear N e h z w hp 3
  · simpa [coeff] using coeff_clear N e h z w hp 4
  · simpa [coeff] using coeff_clear N e h z w hp 5
  · simpa [coeff] using coeff_clear N e h z w hp 6

-- STANDING: DEFINITION
noncomputable def ChartClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  IsArrangement v ∧ ∃ (N : ℕ) (e h z w scale : ℝ), Parameters N e h z w ∧ 0<scale ∧
    disparitySet v k=Finset.univ.image (fun i : Fin 7=>scale*coeff N e h z w i)

theorem chart_named_isolation {v : Fin 8 → ℝ} {k : Fin 8} (hv : IsArrangement v)
    (N : ℕ) (e h z w scale : ℝ) (hp : Parameters N e h z w) (hs : 0<scale)
    (hshape : disparitySet v k=Finset.univ.image (fun i : Fin 7=>scale*coeff N e h z w i)) :
    IsolatedAt v k (resumption N/scale) := by
  apply (isolatedAt_iff_lonelyAt v k _).2
  intro d hd
  rw [hshape] at hd
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hd
  have he : scale*coeff N e h z w i*(resumption N/scale)=coeff N e h z w i*resumption N := by field_simp
  rw [he]
  exact coeff_clear N e h z w hp i

theorem chart_into_canonical {v : Fin 8 → ℝ} {k : Fin 8} (h : ChartClass v k) :
    Fresh.NativeCanonicalReturn.CanonicalReturnClass v k := by
  obtain ⟨hv,N,e,h,z,w,scale,hp,hs,hshape⟩ := h
  have hpoint := chart_named_isolation hv N e h z w scale hp hs hshape
  have hpos := opening_times_positive N hp.1
  have hn : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hp.1
  have hA : 0<12*(N : ℝ)+3/8 := by nlinarith only [hn]
  have hgate := resumption_gate N hp.1
  have hprod : scale*(12*(N : ℝ)+3/8)*(priorOpening N/scale)=(12*(N : ℝ)+3/8)*priorOpening N := by field_simp
  have hcap : InWay (scale*(12*(N : ℝ)+3/8)) (priorOpening N/scale) := by
    apply lt_of_le_of_lt (Fresh.Cascade.distInt_le _ (12*(N : ℤ)+1))
    rw [hprod]
    exact hgate.1
  have hnext : nextOpening (scale*(12*(N : ℝ)+3/8)) (priorOpening N/scale)=resumption N/scale := by
    have hh : |scale*(12*(N : ℝ)+3/8)*(priorOpening N/scale)-((12*(N : ℤ)+1 : ℤ) : ℝ)|<1/8 := by rw [hprod]; exact hgate.1
    rw [nextOpening_eq hh]
    dsimp [resumption]
    push_cast
    field_simp
    <;> ring
  have hstrict := lt_nextOpening (mul_pos hs hA) hcap
  rw [hnext] at hstrict
  have hmem : scale*(12*(N : ℝ)+3/8)∈disparitySet v k := by
    rw [hshape]
    exact Finset.mem_image.mpr ⟨0,Finset.mem_univ _,by simp [coeff]⟩
  have hmove : IsMove (disparitySet v k) (priorOpening N/scale) (resumption N/scale) := by
    refine Or.inr ⟨_,hmem,hcap,hnext.symm,?_⟩
    intro d hd hw
    exact nextOpening_le_of_lonely (disparitySet_pos hv k) ((isolatedAt_iff_lonelyAt v k _).1 hpoint) hstrict.le hd hw
  exact canonical_of_isolating_move hv k _ _ (div_pos hpos.1 hs) hstrict hmove hpoint

theorem chart_isolation {v : Fin 8 → ℝ} {k : Fin 8} (h : ChartClass v k) : Isolation v k :=
  Fresh.NativeCanonicalReturn.canonical_isolation (chart_into_canonical h)

noncomputable def initialTime (N : ℕ) : ℝ := 1/(8*(12*(N : ℝ)+3/8))
noncomputable def initialLabel : Fin 7 → ℤ := ![0,0,0,0,0,0,1]

theorem initial_windows (N : ℕ) (e h z w : ℝ) (hp : Parameters N e h z w) (i : Fin 7) :
    (initialLabel i : ℝ)+1/8 ≤ coeff N e h z w i*initialTime N ∧
      coeff N e h z w i*initialTime N ≤ (initialLabel i : ℝ)+7/8 := by
  obtain ⟨hN,he0,he1,hh0,hh1,hz0,hz1,hw0,hw1⟩ := hp
  have hn : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hden : 0<8*(12*(N : ℝ)+3/8) := by nlinarith only [hn]
  fin_cases i <;> dsimp [coeff,initialLabel,initialTime] <;> push_cast <;> constructor
  all_goals rw [←mul_div_assoc,mul_one]
  all_goals first | rw [le_div_iff₀ hden] | rw [div_le_iff₀ hden]
  all_goals nlinarith only [hn,he0,he1,hh0,hh1,hz0,hz1,hw0,hw1]

theorem initial_coeff_clear (N : ℕ) (e h z w : ℝ) (hp : Parameters N e h z w) (i : Fin 7) :
    (1/8 : ℝ) ≤ distInt (coeff N e h z w i*initialTime N) := by
  have hh := initial_windows N e h z w hp i
  exact clear_of_window (initialLabel i) hh.1 hh.2

theorem coeff_minimum (N : ℕ) (e h z w : ℝ) (hp : Parameters N e h z w) (i : Fin 7) :
    12*(N : ℝ)+3/8 ≤ coeff N e h z w i := by
  obtain ⟨hN,he0,he1,hh0,hh1,hz0,hz1,hw0,hw1⟩ := hp
  have hn : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  fin_cases i <;> dsimp [coeff] <;> nlinarith only [hn,he0,hh0,hz0,hw0]

-- This late resumption chart lies in the already-proved initial family.
theorem chart_into_unblocked {v : Fin 8 → ℝ} {k : Fin 8} (h : ChartClass v k) : Fresh.Admissible.Unblocked v k := by
  obtain ⟨hv,N,e,h,z,w,scale,hp,hs,hshape⟩ := h
  have hm : scale*(12*(N : ℝ)+3/8)∈disparitySet v k := by
    rw [hshape]
    exact Finset.mem_image.mpr ⟨0,Finset.mem_univ _,by simp [coeff]⟩
  refine ⟨scale*(12*(N : ℝ)+3/8),⟨hm,?_⟩,?_⟩
  · intro d hd
    change d∈disparitySet v k at hd
    rw [hshape] at hd
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hd
    exact mul_le_mul_of_nonneg_left (coeff_minimum N e h z w hp i) hs.le
  · intro j hj
    have hd : reading v k j∈disparitySet v k := mem_disparitySet.mpr ⟨j,hj,rfl⟩
    rw [hshape] at hd
    obtain ⟨i,hi,heq⟩ := Finset.mem_image.mp hd
    change (1/8 : ℝ) ≤ distInt (reading v k j*(1/(8*(scale*(12*(N : ℝ)+3/8)))))
    rw [←heq]
    have he : scale*coeff N e h z w i*(1/(8*(scale*(12*(N : ℝ)+3/8))))=coeff N e h z w i*initialTime N := by
      dsimp [initialTime]
      field_simp
    rw [he]
    exact initial_coeff_clear N e h z w hp i

#print axioms initial_windows
#print axioms initial_coeff_clear
#print axioms coeff_minimum
#print axioms chart_into_unblocked

#print axioms opening_times_positive
#print axioms terminal_windows
#print axioms coeff_clear
#print axioms coeff_positive
#print axioms resumption_gate
#print axioms physical_admissible
#print axioms physical_isolation
#print axioms chart_named_isolation
#print axioms chart_into_canonical
#print axioms chart_isolation
end Fresh.NativeRebasedPacketChart
