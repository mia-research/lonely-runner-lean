import Fresh.OpeningClump

/-! Worklist A01/A04, G04–G08/G12: an AP core retains its first bands
while a compact real packet is carried to its reference opening. The packet
width is absolute; it need not share the core step or any rational relation.
[PROVISIONAL: counting tool] inherited openingAfter selects the exact boundary.
-/
namespace Fresh.APCoreOpening
open Fresh Fresh.Localisation Fresh.OpeningClump

theorem ap_core_clump_opening (r : ℕ) (hr1 : 1 ≤ r) (hr6 : r ≤ 6)
    {u x w : ℝ} {C : Finset ℝ} (hu : 0<u) (hx : 0<x) (hw : 0≤w)
    (hC : ∀ d∈C, x≤d ∧ d≤x+w)
    (hsep : 8*(r : ℝ)*u ≤ x*(7-(r : ℝ)))
    (hwidth : w*(1/(8*u)+1/x)≤3/4) :
    0<openingAfter x (1/(8*u)) ∧
    (∀ j : ℕ, 1≤j → j≤r → (1/8 : ℝ)≤distInt (((j : ℝ)*u)*openingAfter x (1/(8*u)))) ∧
    ∀ d∈C, (1/8 : ℝ)≤distInt (d*openingAfter x (1/(8*u))) := by
  have hr : (0 : ℝ)<r := by exact_mod_cast (show 0<r by omega)
  obtain ⟨hlo,hhi,hopen⟩ := openingAfter_spec (lo:=1/(8*u)) hx
  have ht : 0<openingAfter x (1/(8*u)) := lt_of_lt_of_le (by positivity) hlo
  have hfit : 1/(8*u)+1/x≤7/(8*(r : ℝ)*u) := by
    apply (le_div_iff₀ (by positivity : 0<8*(r : ℝ)*u)).2
    have he : (1/(8*u)+1/x)*(8*(r : ℝ)*u)=((r : ℝ)*x+8*(r : ℝ)*u)/x := by field_simp
    rw [he,div_le_iff₀ hx]
    nlinarith
  have hbound := hhi.le.trans hfit
  refine ⟨ht,?_,clump_at_opening ht.le hopen hC ?_⟩
  · intro j hj1 hjr
    have hjlo : (1 : ℝ)≤j := by exact_mod_cast hj1
    have hjhi : (j : ℝ)≤r := by exact_mod_cast hjr
    have hju : 0≤(j : ℝ)*u := by positivity
    apply clear_of_window 0 <;> push_cast
    · have h1 := mul_le_mul_of_nonneg_left hlo hju
      have he : ((j : ℝ)*u)*(1/(8*u))=(j : ℝ)/8 := by field_simp
      rw [he] at h1
      linarith
    · have h1 := (le_div_iff₀ (by positivity : 0<8*(r : ℝ)*u)).mp hbound
      have h2 := mul_le_mul_of_nonneg_right hjhi ht.le
      nlinarith [mul_le_mul_of_nonneg_right h2 hu.le]
  · exact (mul_le_mul_of_nonneg_left hhi.le hw).trans hwidth

-- STANDING: DEFINITION
def APCoreOpeningClass (v : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  ∃ (r : ℕ) (u x w : ℝ) (C : Finset ℝ),
    1≤r ∧ r≤6 ∧ 0<u ∧ 0<x ∧ 0≤w ∧
    (∀ d∈C, x≤d ∧ d≤x+w) ∧
    8*(r : ℝ)*u≤x*(7-(r : ℝ)) ∧ w*(1/(8*u)+1/x)≤3/4 ∧
    ∀ d∈disparitySet v k, (∃ j : ℕ, 1≤j ∧ j≤r ∧ d=(j : ℝ)*u) ∨ d∈C

theorem apCoreOpening_isolation {v : Fin 8 → ℝ} {k : Fin 8}
    (h : APCoreOpeningClass v k) : Isolation v k := by
  obtain ⟨r,u,x,w,C,hr1,hr6,hu,hx,hw,hC,hsep,hwidth,hmem⟩ := h
  obtain ⟨ht,hcore,hpacket⟩ := ap_core_clump_opening r hr1 hr6 hu hx hw hC hsep hwidth
  refine ⟨openingAfter x (1/(8*u)),ht,?_⟩
  rw [isolatedAt_iff]
  intro d hd
  rcases hmem d hd with ⟨j,hj1,hjr,rfl⟩ | hdC
  · exact hcore j hj1 hjr
  · exact hpacket d hdC

#print axioms ap_core_clump_opening
#print axioms apCoreOpening_isolation
end Fresh.APCoreOpening
