import Fresh.OpeningClump

/-!
Rules1–4,8–18. Two-plus-six packet refinement, actual-cascade tested first
(two_six_phase_v1.py). The middle anchor h=3 joins all b∈[1,2] to the
base-anchor common-cycle law b≥2; low packet separation x≥9b suffices.
[PROVISIONAL: counting tool] each ceiling locates a named opening;
[PROVISIONAL: covering] supports only the two STEP-PARAMETER branches.
The outside x=6,b=1 control refutes the selected opening, not isolation.
-/
namespace Fresh.TwoSixPhase
open Fresh Fresh.Localisation Fresh.OpeningClump

theorem two_six_middle {x b : ℝ} (hb : (8/21 : ℝ)≤b) (hb2 : b≤2) (hx : 9*b≤x) :
    ∃T : ℝ, 0<T ∧ (1/8 : ℝ)≤distInt T ∧
      ∀j : ℕ, j≤5 → (1/8 : ℝ)≤distInt ((x+(j : ℝ)*b)*T) := by
  have hbpos : 0<b := by linarith
  have hX : 0<x+3*b := by linarith
  obtain ⟨h1,h2,hopen⟩ := openingAfter_spec (lo:=1/(4*b)) hX
  have htlo : (1/8 : ℝ)≤openingAfter (x+3*b) (1/(4*b)) := by
    have hh : (1/8 : ℝ)≤1/(4*b) := by rw [le_div_iff₀ (by positivity : 0<4*b)]; nlinarith
    exact hh.trans h1
  have ht : 0<openingAfter (x+3*b) (1/(4*b)) := by linarith
  have he : b*(1/(4*b))=(1/4 : ℝ) := by field_simp
  have hp1 : (1/4 : ℝ)≤b*openingAfter (x+3*b) (1/(4*b)) := by
    have hh := mul_le_mul_of_nonneg_left h1 hbpos.le
    rwa [he] at hh
  have hp2 : b*openingAfter (x+3*b) (1/(4*b))≤1/3 := by
    have hh := mul_le_mul_of_nonneg_left h2.le hbpos.le
    have hf : b/(x+3*b)≤1/12 := by rw [div_le_iff₀ hX]; nlinarith
    have he' : b*(1/(4*b)+1/(x+3*b))=1/4+b/(x+3*b) := by field_simp
    rw [he'] at hh
    linarith
  have htupper : openingAfter (x+3*b) (1/(4*b))≤7/8 := by
    have hh := mul_le_mul_of_nonneg_right hb ht.le
    nlinarith
  refine ⟨_,ht,?_,?_⟩
  · apply clear_of_window 0
    · simpa only [Int.cast_zero,zero_add] using htlo
    · simpa only [Int.cast_zero,zero_add] using htupper
  · intro j hj
    interval_cases j
    · apply clear_of_window (⌈(x+3*b)*(1/(4*b))-1/8⌉-1) <;> push_cast <;> nlinarith
    · apply clear_of_window (⌈(x+3*b)*(1/(4*b))-1/8⌉-1) <;> push_cast <;> nlinarith
    · apply clear_of_window (⌈(x+3*b)*(1/(4*b))-1/8⌉-1) <;> push_cast <;> nlinarith
    · apply clear_of_window ⌈(x+3*b)*(1/(4*b))-1/8⌉ <;> push_cast <;> nlinarith
    · apply clear_of_window ⌈(x+3*b)*(1/(4*b))-1/8⌉ <;> push_cast <;> nlinarith
    · apply clear_of_window ⌈(x+3*b)*(1/(4*b))-1/8⌉ <;> push_cast <;> nlinarith

theorem two_six_large {x b : ℝ} (hb : 2≤b) (hx : 9*b≤x) :
    ∃T : ℝ, 0<T ∧ (1/8 : ℝ)≤distInt T ∧
      ∀j : ℕ, j≤5 → (1/8 : ℝ)≤distInt ((x+(j : ℝ)*b)*T) := by
  have hbpos : 0<b := by linarith
  have hxpos : 0<x := by linarith
  let q : ℤ := ⌈b/8⌉
  have hq1 : b/8≤(q : ℝ) := Int.le_ceil _
  have hq2 : (q : ℝ)<b/8+1 := Int.ceil_lt_add_one _
  obtain ⟨h1,h2,hopen⟩ := openingAfter_spec (lo:=(q : ℝ)/b) hxpos
  have htlo : (1/8 : ℝ)≤openingAfter x ((q : ℝ)/b) := by
    have hh : (1/8 : ℝ)≤(q : ℝ)/b := by rw [le_div_iff₀ hbpos]; linarith
    exact hh.trans h1
  have ht : 0<openingAfter x ((q : ℝ)/b) := by linarith
  have hp1 : (q : ℝ)≤b*openingAfter x ((q : ℝ)/b) := by
    have := (div_le_iff₀ hbpos).mp h1
    nlinarith
  have hp2 : b*openingAfter x ((q : ℝ)/b)≤(q : ℝ)+1/9 := by
    have hh := mul_le_mul_of_nonneg_left h2.le hbpos.le
    have hf : b/x≤1/9 := by rw [div_le_iff₀ hxpos]; nlinarith
    have he : b*((q : ℝ)/b+1/x)=(q : ℝ)+b/x := by field_simp
    rw [he] at hh
    linarith
  have htupper : openingAfter x ((q : ℝ)/b)≤7/8 := by
    have hh : b*openingAfter x ((q : ℝ)/b)≤b*(7/8) := by nlinarith
    exact le_of_mul_le_mul_left hh hbpos
  refine ⟨_,ht,?_,fun j hj=>?_⟩
  · apply clear_of_window 0
    · simpa only [Int.cast_zero,zero_add] using htlo
    · simpa only [Int.cast_zero,zero_add] using htupper
  have hj0 : (0 : ℝ)≤j := Nat.cast_nonneg _
  have hj5 : (j : ℝ)≤5 := by exact_mod_cast hj
  have hd0 : 0≤b*openingAfter x ((q : ℝ)/b)-(q : ℝ) := by linarith
  have hdhi : b*openingAfter x ((q : ℝ)/b)-(q : ℝ)≤1/9 := by linarith
  have hlo := mul_nonneg hj0 hd0
  have hhi1 := mul_le_mul_of_nonneg_left hdhi (by norm_num : (0 : ℝ)≤5)
  have hhi2 := mul_le_mul_of_nonneg_right hj5 hd0
  have he : (x+(j : ℝ)*b)*openingAfter x ((q : ℝ)/b)=
      (⌈x*((q : ℝ)/b)-1/8⌉ : ℤ)+1/8+((j : ℤ)*q : ℤ)+(j : ℝ)*(b*openingAfter x ((q : ℝ)/b)-(q : ℝ)) := by
    push_cast
    calc (x+(j : ℝ)*b)*openingAfter x ((q : ℝ)/b)=x*openingAfter x ((q : ℝ)/b)+(j : ℝ)*(q : ℝ)+(j : ℝ)*(b*openingAfter x ((q : ℝ)/b)-(q : ℝ)) := by ring
         _=(_ : ℝ) := by rw [hopen]
  apply clear_of_window (⌈x*((q : ℝ)/b)-1/8⌉+(j : ℤ)*q)
  · push_cast; rw [he]; push_cast; nlinarith
  · push_cast; rw [he]; push_cast; nlinarith

theorem two_six_all {x b : ℝ} (hb : 1≤b) (hx : 9*b≤x) :
    ∃T : ℝ, 0<T ∧ (1/8 : ℝ)≤distInt T ∧
      ∀j : ℕ, j≤5 → (1/8 : ℝ)≤distInt ((x+(j : ℝ)*b)*T) := by
  by_cases h2 : b≤2
  · exact two_six_middle (by linarith) h2 hx
  · exact two_six_large (by linarith) hx

/-- Every positive packet step under the original physical gap bound.
Small steps use the established one-band opening; the two other regimes
use middle-anchor or independent-cycle displacement. -/
theorem two_six_any {x b : ℝ} (hb : 0<b) (hx : 20*max 1 b≤x) :
    ∃T : ℝ, 0<T ∧ (1/8 : ℝ)≤distInt T ∧
      ∀j : ℕ, j≤5 → (1/8 : ℝ)≤distInt ((x+(j : ℝ)*b)*T) := by
  have hx20 : (20 : ℝ)≤x := by have := le_max_left (1 : ℝ) b; nlinarith
  have hx20b : 20*b≤x := by have := le_max_right (1 : ℝ) b; nlinarith
  by_cases hsmall : b≤8/21
  · let C : Finset ℝ := (Finset.range 6).image (fun j : ℕ=>x+(j : ℝ)*b)
    have hC : ∀d∈C, x≤d ∧ d≤x+5*b := by
      intro d hd
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hd
      have hj0 : (0 : ℝ)≤j := Nat.cast_nonneg _
      have hj5 : (j : ℝ)≤5 := by exact_mod_cast (show j≤5 by have := Finset.mem_range.mp hj; omega)
      constructor <;> nlinarith
    have hrecip : 1/x≤(1/20 : ℝ) :=
      one_div_le_one_div_of_le (by norm_num) hx20
    have hdev : (5*b)*(1/(8*1)+1/x)≤(3/4 : ℝ) := by
      have hh := mul_le_mul_of_nonneg_left hrecip (by positivity : 0≤5*b)
      nlinarith
    obtain ⟨ht,hcore,hpacket⟩ := single_slow_opening (s:=(1 : ℝ))
      (by norm_num) (by linarith : 0<x) (by positivity : 0≤5*b) hC (by nlinarith) hdev
    refine ⟨_,ht,?_,fun j hj=>?_⟩
    · simpa only [one_mul] using hcore
    · exact hpacket _ (Finset.mem_image.mpr ⟨j,Finset.mem_range.mpr (by omega),rfl⟩)
  · by_cases h2 : b≤2
    · exact two_six_middle (by linarith) h2 (by nlinarith)
    · exact two_six_large (by linarith) (by nlinarith)

#print axioms two_six_any

#print axioms two_six_middle
#print axioms two_six_large
#print axioms two_six_all
end Fresh.TwoSixPhase
