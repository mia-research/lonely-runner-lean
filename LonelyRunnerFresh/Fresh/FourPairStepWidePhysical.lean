import Fresh.FourPairStepWideMerge

/-! Rules:1–4,8–18. Original physical four-pair arrangement with one
internal pair-step deformed. Write S=packet m σ,D=moved m κ: original
gaps are g,S−g,4−ρ/q−S and changed internal step u=D−1−S. All are admissible
below. Full original first-free or partner-first native trace is preserved;
far pair readings6−ρ/q,7−ρ/q resume with their actual displaced openings. -/
set_option maxHeartbeats 1200000
open Classical
namespace Fresh.FourPairStepWidePhysical
open Fresh Fresh.OneMover Fresh.Cascade Fresh.Localisation Fresh.FourPairStepBounds Fresh.FourPairStepWideMerge Fresh.FourPairStepPerturbedBounds Fresh.FourPairStepWideCapture Fresh.FourPairStepWideClear

-- STANDING: DEFINITION
noncomputable def speeds (c g : ℝ) (m : ℤ) (κ σ ρ : ℝ) (i : Fin 8) : ℝ :=
  c + if (i : ℕ)<2 then 1+(i : ℝ)
      else if (i : ℕ)<4 then g+(i : ℝ)
      else if (i : ℕ)=4 then 3+packet m σ
      else if (i : ℕ)=5 then 2+moved m κ
      else (i : ℝ)+2-ρ/grid m

theorem original_gaps_admissible (g : ℝ) (m : ℤ) (hm : 1 ≤ m) (hg : 0 < g)
    (he1 : 1 < (8*(m : ℝ)+1)*g) (he2 : (8*(m : ℝ)-1)*g < 1)
    (κ σ ρ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hρ0 : 0 ≤ ρ) (hρκ : ρ ≤ κ) :
    0 < packet m σ-g ∧ 0 < slow m ρ-2-packet m σ ∧
    0 < moved m κ-1-packet m σ ∧
    moved m κ-1-packet m σ < 1+(slow m ρ-2-packet m σ) := by
  obtain ⟨hspos,hs1,hst⟩ := packet_spec m hm σ hσ0 hσ1
  obtain ⟨hd2,hd3,hdt⟩ := moved_wide_spec m hm κ hκ0 hκ1
  obtain ⟨ha5,ha6,hf6,hf7,hfa,hat,hft⟩ := pair_wide_spec m hm κ ρ hκ1 hρ0 hρκ
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hgmax : g < 1/7 := by nlinarith
  have hq : 0 < 8*(m : ℝ)+1 := by linarith
  have hprod : (8*(m : ℝ)+1)*(packet m σ-g) > 0 := by
    dsimp [T] at hst
    nlinarith
  constructor
  · nlinarith
  constructor
  · linarith
  constructor <;> linarith

theorem original_disparity_eq (c g : ℝ) (m : ℤ) (hm : 1 ≤ m) (hg : 0 < g)
    (κ σ ρ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hρ0 : 0 ≤ ρ) (hρκ : ρ ≤ κ) :
    disparitySet (speeds c g m κ σ ρ) (1 : Fin 8)=readingsP g m κ σ ρ := by
  obtain ⟨hspos,hs1,hst⟩ := packet_spec m hm σ hσ0 hσ1
  obtain ⟨hd2,hd3,hdt⟩ := moved_wide_spec m hm κ hκ0 hκ1
  obtain ⟨ha5,ha6,hf6,hf7,hfa,hat,hft⟩ := pair_wide_spec m hm κ ρ hκ1 hρ0 hρκ
  ext d
  rw [mem_disparitySet]
  constructor
  · rintro ⟨i,hne,rfl⟩
    fin_cases i
    · change |speeds c g m κ σ ρ (0 : Fin 8)-speeds c g m κ σ ρ (1 : Fin 8)| ∈ readingsP g m κ σ ρ
      have he : speeds c g m κ σ ρ (0 : Fin 8)-speeds c g m κ σ ρ (1 : Fin 8)=(-1 : ℝ) := by norm_num [speeds,slow,fast] <;> ring
      rw [he]
      norm_num [readingsP,core]
    · exact (hne rfl).elim
    · change |speeds c g m κ σ ρ (2 : Fin 8)-speeds c g m κ σ ρ (1 : Fin 8)| ∈ readingsP g m κ σ ρ
      have he : speeds c g m κ σ ρ (2 : Fin 8)-speeds c g m κ σ ρ (1 : Fin 8)=g := by norm_num [speeds,slow,fast] <;> ring
      rw [he]
      rw [abs_of_nonneg (by linarith)]
      simp [readingsP,core]
    · change |speeds c g m κ σ ρ (3 : Fin 8)-speeds c g m κ σ ρ (1 : Fin 8)| ∈ readingsP g m κ σ ρ
      have he : speeds c g m κ σ ρ (3 : Fin 8)-speeds c g m κ σ ρ (1 : Fin 8)=1+g := by norm_num [speeds,slow,fast] <;> ring
      rw [he]
      rw [abs_of_nonneg (by linarith)]
      simp [readingsP,core]
    · change |speeds c g m κ σ ρ (4 : Fin 8)-speeds c g m κ σ ρ (1 : Fin 8)| ∈ readingsP g m κ σ ρ
      have he : speeds c g m κ σ ρ (4 : Fin 8)-speeds c g m κ σ ρ (1 : Fin 8)=1+packet m σ := by norm_num [speeds,slow,fast] <;> ring
      rw [he]
      rw [abs_of_nonneg (by linarith)]
      simp [readingsP,core]
    · change |speeds c g m κ σ ρ (5 : Fin 8)-speeds c g m κ σ ρ (1 : Fin 8)| ∈ readingsP g m κ σ ρ
      have he : speeds c g m κ σ ρ (5 : Fin 8)-speeds c g m κ σ ρ (1 : Fin 8)=moved m κ := by norm_num [speeds,slow,fast] <;> ring
      rw [he]
      rw [abs_of_nonneg (by linarith)]
      simp [readingsP,core]
    · change |speeds c g m κ σ ρ (6 : Fin 8)-speeds c g m κ σ ρ (1 : Fin 8)| ∈ readingsP g m κ σ ρ
      have he : speeds c g m κ σ ρ (6 : Fin 8)-speeds c g m κ σ ρ (1 : Fin 8)=slow m ρ := by norm_num [speeds,slow,fast] <;> ring
      rw [he]
      rw [abs_of_nonneg (by linarith)]
      simp [readingsP,core]
    · change |speeds c g m κ σ ρ (7 : Fin 8)-speeds c g m κ σ ρ (1 : Fin 8)| ∈ readingsP g m κ σ ρ
      have he : speeds c g m κ σ ρ (7 : Fin 8)-speeds c g m κ σ ρ (1 : Fin 8)=fast m ρ := by norm_num [speeds,slow,fast] <;> ring
      rw [he]
      rw [abs_of_nonneg (by linarith)]
      simp [readingsP,core]
  · intro hd
    simp only [readingsP,core,Finset.mem_insert,Finset.mem_union,Finset.mem_singleton] at hd
    rcases hd with hd|(hd|hd|hd|hd)|hd|hd
    · subst d
      refine ⟨(5 : Fin 8),by decide,?_⟩
      have he : speeds c g m κ σ ρ (5 : Fin 8)-speeds c g m κ σ ρ (1 : Fin 8)=moved m κ := by norm_num [speeds,slow,fast] <;> ring
      rw [he]
      exact abs_of_nonneg (by linarith)
    · subst d
      refine ⟨(2 : Fin 8),by decide,?_⟩
      have he : speeds c g m κ σ ρ (2 : Fin 8)-speeds c g m κ σ ρ (1 : Fin 8)=g := by norm_num [speeds,slow,fast] <;> ring
      rw [he]
      exact abs_of_nonneg (by linarith)
    · subst d
      refine ⟨(0 : Fin 8),by decide,?_⟩
      have he : speeds c g m κ σ ρ (0 : Fin 8)-speeds c g m κ σ ρ (1 : Fin 8)=(-1 : ℝ) := by norm_num [speeds,slow,fast] <;> ring
      rw [he]
      norm_num
    · subst d
      refine ⟨(3 : Fin 8),by decide,?_⟩
      have he : speeds c g m κ σ ρ (3 : Fin 8)-speeds c g m κ σ ρ (1 : Fin 8)=1+g := by norm_num [speeds,slow,fast] <;> ring
      rw [he]
      exact abs_of_nonneg (by linarith)
    · subst d
      refine ⟨(4 : Fin 8),by decide,?_⟩
      have he : speeds c g m κ σ ρ (4 : Fin 8)-speeds c g m κ σ ρ (1 : Fin 8)=1+packet m σ := by norm_num [speeds,slow,fast] <;> ring
      rw [he]
      exact abs_of_nonneg (by linarith)
    · subst d
      refine ⟨(6 : Fin 8),by decide,?_⟩
      have he : speeds c g m κ σ ρ (6 : Fin 8)-speeds c g m κ σ ρ (1 : Fin 8)=slow m ρ := by norm_num [speeds,slow,fast] <;> ring
      rw [he]
      exact abs_of_nonneg (by linarith)
    · subst d
      refine ⟨(7 : Fin 8),by decide,?_⟩
      have he : speeds c g m κ σ ρ (7 : Fin 8)-speeds c g m κ σ ρ (1 : Fin 8)=fast m ρ := by norm_num [speeds,slow,fast] <;> ring
      rw [he]
      exact abs_of_nonneg (by linarith)

theorem physical_isolation (c g : ℝ) (m : ℤ) (hm : 1 ≤ m) (hg : 0 < g)
    (he1 : 1 < (8*(m : ℝ)+1)*g) (he2 : (8*(m : ℝ)-1)*g < 1)
    (κ σ ρ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) (hρ0 : 0 ≤ ρ) (hρκ : ρ ≤ κ) :
    Isolation (speeds c g m κ σ ρ) (1 : Fin 8) := by
  have hclear := wide_clear g m hm hg he1 he2 κ σ ρ hκ0 hκ1 hσ0 hσ1 hρ0 hρκ
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  refine ⟨WP m ρ,?_,?_⟩
  · exact (wide_wp_bounds m hm κ ρ hκ1 hρ0 hρκ).1
  · apply (isolatedAt_iff _ _ _).2
    rw [original_disparity_eq c g m hm hg κ σ ρ hκ0 hκ1 hσ0 hσ1 hρ0 hρκ]
    exact hclear

-- STANDING: DEFINITION
def FourPairStepWideClass (V : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  (∀i,0<V i) ∧ Function.Injective V ∧
  ∃(c g B z κ σ ρ : ℝ)(m : ℤ)(τ : Equiv.Perm (Fin 8)),
    0<g ∧ 1 ≤ m ∧ 1<(8*(m : ℝ)+1)*g ∧ (8*(m : ℝ)-1)*g<1 ∧
    0<κ ∧ κ ≤ 1 ∧ 0 ≤ σ ∧ σ ≤ 1 ∧ 0 ≤ ρ ∧ ρ ≤ κ ∧ z≠0 ∧ τ k=1 ∧
    V=(fun i => B+z*speeds c g m κ σ ρ (τ i))

theorem fourPairStepWide_isolation {V : Fin 8 → ℝ} {k : Fin 8}
    (h : FourPairStepWideClass V k) : Isolation V k := by
  obtain ⟨hpos,hinj,c,g,B,z,κ,σ,ρ,m,τ,hg,hm,he1,he2,hκ0,hκ1,hσ0,hσ1,hρ0,hρκ,hz,hk,hV⟩ := h
  have hbase : Isolation (speeds c g m κ σ ρ) (τ k) := by
    rw [hk]
    exact physical_isolation c g m hm hg he1 he2 κ σ ρ hκ0 hκ1 hσ0 hσ1 hρ0 hρκ
  rw [hV]
  have hi := subject_isolation_affine B z hz hbase
  exact (Fresh.isolation_comp_perm _ τ k).2 hi

#print axioms original_gaps_admissible
#print axioms original_disparity_eq
#print axioms physical_isolation
#print axioms fourPairStepWide_isolation
end Fresh.FourPairStepWidePhysical
