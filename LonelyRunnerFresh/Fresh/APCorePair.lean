import Fresh.FastPairReal

/-! An unchanged AP core and two arbitrary fast readings.
The core's native first bands retain the pair's exact boundary construction.
[PROVISIONAL: counting tool] inherited quarter-band/band boundary selection.
[PROVISIONAL: covering] the explicit separation inequality places that
constructed pair point inside the core's closed first-band interval.
-/
namespace Fresh.APCorePair
open Fresh Fresh.Localisation Fresh.FastPairReal

theorem ap_core_pair (r : ℕ) (hr1 : 1≤r) (hr6 : r≤6)
    {u a b : ℝ} (hu : 0<u) (ha : 0<a) (hab : a≤b)
    (hsep : 6*(r : ℝ)*u≤a*(7-(r : ℝ))) :
    ∃ T : ℝ, 0<T ∧
      (∀ j : ℕ, 1≤j → j≤r → (1/8 : ℝ)≤distInt (((j : ℝ)*u)*T)) ∧
      (1/8 : ℝ)≤distInt (a*T) ∧ (1/8 : ℝ)≤distInt (b*T) := by
  have hr : (0 : ℝ)<r := by exact_mod_cast (show 0<r by omega)
  obtain ⟨T,hlo,hhi,hA,hB⟩ := pair_window ha hab (1/(8*u))
  have ht : 0<T := lt_of_lt_of_le (by positivity) hlo
  have hfit : 1/(8*u)+3/(4*a)≤7/(8*(r : ℝ)*u) := by
    apply (le_div_iff₀ (by positivity : 0<8*(r : ℝ)*u)).2
    have he : (1/(8*u)+3/(4*a))*(8*(r : ℝ)*u)=((r : ℝ)*a+6*(r : ℝ)*u)/a := by field_simp <;> ring
    rw [he,div_le_iff₀ ha]
    nlinarith
  have hbound := hhi.trans hfit
  refine ⟨T,ht,?_,hA,hB⟩
  intro j hj1 hjr
  have hjlo : (1 : ℝ)≤j := by exact_mod_cast hj1
  have hjhi : (j : ℝ)≤r := by exact_mod_cast hjr
  have hju : 0≤(j : ℝ)*u := by positivity
  apply clear_of_window 0 <;> push_cast
  · have hh := mul_le_mul_of_nonneg_left hlo hju
    have he : ((j : ℝ)*u)*(1/(8*u))=(j : ℝ)/8 := by field_simp
    rw [he] at hh
    linarith
  · have h1 := (le_div_iff₀ (by positivity : 0<8*(r : ℝ)*u)).mp hbound
    have h2 := mul_le_mul_of_nonneg_right hjhi ht.le
    nlinarith [mul_le_mul_of_nonneg_right h2 hu.le]

-- STANDING: DEFINITION
def APCorePairClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ (r : ℕ) (u a b : ℝ), 1≤r ∧ r≤6 ∧ 0<u ∧ 0<a ∧ a≤b ∧
    6*(r : ℝ)*u≤a*(7-(r : ℝ)) ∧
    ∀ d∈disparitySet v k, (∃ j : ℕ, 1≤j ∧ j≤r ∧ d=(j : ℝ)*u) ∨ d=a ∨ d=b

theorem apCorePair_isolation {v : Fin 8 → ℝ} {k : Fin 8}
    (h : APCorePairClass v k) : Isolation v k := by
  obtain ⟨r,u,a,b,hr1,hr6,hu,ha,hab,hsep,hmem⟩ := h
  obtain ⟨T,hT,hcore,hA,hB⟩ := ap_core_pair r hr1 hr6 hu ha hab hsep
  refine ⟨T,hT,?_⟩
  rw [isolatedAt_iff]
  intro d hd
  rcases hmem d hd with ⟨j,hj1,hjr,rfl⟩ | rfl | rfl
  · exact hcore j hj1 hjr
  · exact hA
  · exact hB

#print axioms ap_core_pair
#print axioms apCorePair_isolation
end Fresh.APCorePair
