import Fresh.FourPairStepMerge

/-! Rules:1–4,8–18. Original physical four-pair arrangement with one
internal pair-step deformed. Write S=packet m σ,D=moved m κ: original
gaps are g,S−g,4−S and changed internal step u=D−1−S. All are admissible
below. Full original first-free or partner-first native trace is preserved;
fixed far pair6,7 is a stated λ0 slice, not a claim about all deformations. -/
open Classical
namespace Fresh.FourPairStepPhysical
open Fresh Fresh.OneMover Fresh.Cascade Fresh.Localisation Fresh.FourPairStepBounds Fresh.FourPairStepMerge

-- STANDING: DEFINITION
noncomputable def speeds (c g : ℝ) (m : ℤ) (κ σ : ℝ) (i : Fin 8) : ℝ :=
  c + if (i : ℕ)<2 then 1+(i : ℝ)
      else if (i : ℕ)<4 then g+(i : ℝ)
      else if (i : ℕ)=4 then 3+packet m σ
      else if (i : ℕ)=5 then 2+moved m κ
      else (i : ℝ)+2

theorem original_gaps_admissible (g : ℝ) (m : ℤ) (hm : 1 ≤ m) (hg : 0 < g)
    (he1 : 1 < (8*(m : ℝ)+1)*g) (he2 : (8*(m : ℝ)-1)*g < 1)
    (κ σ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1/4) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    0 < packet m σ-g ∧ 0 < 4-packet m σ ∧
    0 < moved m κ-1-packet m σ ∧
    moved m κ-1-packet m σ < 1+(4-packet m σ) := by
  obtain ⟨hspos,hs1,hst⟩ := packet_spec m hm σ hσ0 hσ1
  obtain ⟨hd2,hd3,hdt⟩ := moved_spec m hm κ hκ0 hκ1
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
    (κ σ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1/4) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    disparitySet (speeds c g m κ σ) (1 : Fin 8)=readings g m κ σ := by
  obtain ⟨hspos,hs1,hst⟩ := packet_spec m hm σ hσ0 hσ1
  obtain ⟨hd2,hd3,hdt⟩ := moved_spec m hm κ hκ0 hκ1
  ext d
  rw [mem_disparitySet]
  constructor
  · rintro ⟨i,hne,rfl⟩
    fin_cases i
    · change |speeds c g m κ σ (0 : Fin 8)-speeds c g m κ σ (1 : Fin 8)| ∈ readings g m κ σ
      have he : speeds c g m κ σ (0 : Fin 8)-speeds c g m κ σ (1 : Fin 8)=(-1 : ℝ) := by norm_num [speeds] <;> ring
      rw [he]
      norm_num [readings,core]
    · exact (hne rfl).elim
    · change |speeds c g m κ σ (2 : Fin 8)-speeds c g m κ σ (1 : Fin 8)| ∈ readings g m κ σ
      have he : speeds c g m κ σ (2 : Fin 8)-speeds c g m κ σ (1 : Fin 8)=g := by norm_num [speeds] <;> ring
      rw [he]
      rw [abs_of_nonneg (by linarith)]
      simp [readings,core]
    · change |speeds c g m κ σ (3 : Fin 8)-speeds c g m κ σ (1 : Fin 8)| ∈ readings g m κ σ
      have he : speeds c g m κ σ (3 : Fin 8)-speeds c g m κ σ (1 : Fin 8)=1+g := by norm_num [speeds] <;> ring
      rw [he]
      rw [abs_of_nonneg (by linarith)]
      simp [readings,core]
    · change |speeds c g m κ σ (4 : Fin 8)-speeds c g m κ σ (1 : Fin 8)| ∈ readings g m κ σ
      have he : speeds c g m κ σ (4 : Fin 8)-speeds c g m κ σ (1 : Fin 8)=1+packet m σ := by norm_num [speeds] <;> ring
      rw [he]
      rw [abs_of_nonneg (by linarith)]
      simp [readings,core]
    · change |speeds c g m κ σ (5 : Fin 8)-speeds c g m κ σ (1 : Fin 8)| ∈ readings g m κ σ
      have he : speeds c g m κ σ (5 : Fin 8)-speeds c g m κ σ (1 : Fin 8)=moved m κ := by norm_num [speeds] <;> ring
      rw [he]
      rw [abs_of_nonneg (by linarith)]
      simp [readings,core]
    · change |speeds c g m κ σ (6 : Fin 8)-speeds c g m κ σ (1 : Fin 8)| ∈ readings g m κ σ
      have he : speeds c g m κ σ (6 : Fin 8)-speeds c g m κ σ (1 : Fin 8)=(6 : ℝ) := by norm_num [speeds] <;> ring
      rw [he]
      norm_num [readings,core]
    · change |speeds c g m κ σ (7 : Fin 8)-speeds c g m κ σ (1 : Fin 8)| ∈ readings g m κ σ
      have he : speeds c g m κ σ (7 : Fin 8)-speeds c g m κ σ (1 : Fin 8)=(7 : ℝ) := by norm_num [speeds] <;> ring
      rw [he]
      norm_num [readings,core]
  · intro hd
    simp only [readings,core,Finset.mem_insert,Finset.mem_union,Finset.mem_singleton] at hd
    rcases hd with hd|(hd|hd|hd|hd)|hd|hd
    · subst d
      refine ⟨(5 : Fin 8),by decide,?_⟩
      have he : speeds c g m κ σ (5 : Fin 8)-speeds c g m κ σ (1 : Fin 8)=moved m κ := by norm_num [speeds] <;> ring
      rw [he]
      exact abs_of_nonneg (by linarith)
    · subst d
      refine ⟨(2 : Fin 8),by decide,?_⟩
      have he : speeds c g m κ σ (2 : Fin 8)-speeds c g m κ σ (1 : Fin 8)=g := by norm_num [speeds] <;> ring
      rw [he]
      exact abs_of_nonneg (by linarith)
    · subst d
      refine ⟨(0 : Fin 8),by decide,?_⟩
      have he : speeds c g m κ σ (0 : Fin 8)-speeds c g m κ σ (1 : Fin 8)=(-1 : ℝ) := by norm_num [speeds] <;> ring
      rw [he]
      norm_num
    · subst d
      refine ⟨(3 : Fin 8),by decide,?_⟩
      have he : speeds c g m κ σ (3 : Fin 8)-speeds c g m κ σ (1 : Fin 8)=1+g := by norm_num [speeds] <;> ring
      rw [he]
      exact abs_of_nonneg (by linarith)
    · subst d
      refine ⟨(4 : Fin 8),by decide,?_⟩
      have he : speeds c g m κ σ (4 : Fin 8)-speeds c g m κ σ (1 : Fin 8)=1+packet m σ := by norm_num [speeds] <;> ring
      rw [he]
      exact abs_of_nonneg (by linarith)
    · subst d
      refine ⟨(6 : Fin 8),by decide,?_⟩
      have he : speeds c g m κ σ (6 : Fin 8)-speeds c g m κ σ (1 : Fin 8)=(6 : ℝ) := by norm_num [speeds] <;> ring
      rw [he]
      norm_num
    · subst d
      refine ⟨(7 : Fin 8),by decide,?_⟩
      have he : speeds c g m κ σ (7 : Fin 8)-speeds c g m κ σ (1 : Fin 8)=(7 : ℝ) := by norm_num [speeds] <;> ring
      rw [he]
      norm_num

theorem physical_isolation (c g : ℝ) (m : ℤ) (hm : 1 ≤ m) (hg : 0 < g)
    (he1 : 1 < (8*(m : ℝ)+1)*g) (he2 : (8*(m : ℝ)-1)*g < 1)
    (κ σ : ℝ) (hκ0 : 0 < κ) (hκ1 : κ ≤ 1/4) (hσ0 : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    Isolation (speeds c g m κ σ) (1 : Fin 8) := by
  have hclear := (native_original_episode g m hm hg he1 he2 κ σ hκ0 hκ1 hσ0 hσ1).2.2.2.2
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  refine ⟨W m,by dsimp [W]; linarith,?_⟩
  apply (isolatedAt_iff _ _ _).2
  rw [original_disparity_eq c g m hm hg κ σ hκ0 hκ1 hσ0 hσ1]
  exact hclear

-- STANDING: DEFINITION
def FourPairStepClass (V : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  (∀i,0<V i) ∧ Function.Injective V ∧
  ∃(c g B z κ σ : ℝ)(m : ℤ)(τ : Equiv.Perm (Fin 8)),
    0<g ∧ 1 ≤ m ∧ 1<(8*(m : ℝ)+1)*g ∧ (8*(m : ℝ)-1)*g<1 ∧
    0<κ ∧ κ ≤ 1/4 ∧ 0 ≤ σ ∧ σ ≤ 1 ∧ z≠0 ∧ τ k=1 ∧
    V=(fun i => B+z*speeds c g m κ σ (τ i))

theorem fourPairStep_isolation {V : Fin 8 → ℝ} {k : Fin 8}
    (h : FourPairStepClass V k) : Isolation V k := by
  obtain ⟨hpos,hinj,c,g,B,z,κ,σ,m,τ,hg,hm,he1,he2,hκ0,hκ1,hσ0,hσ1,hz,hk,hV⟩ := h
  have hbase : Isolation (speeds c g m κ σ) (τ k) := by
    rw [hk]
    exact physical_isolation c g m hm hg he1 he2 κ σ hκ0 hκ1 hσ0 hσ1
  rw [hV]
  have hi := subject_isolation_affine B z hz hbase
  exact (Fresh.isolation_comp_perm _ τ k).2 hi

#print axioms original_gaps_admissible
#print axioms original_disparity_eq
#print axioms physical_isolation
#print axioms fourPairStep_isolation
end Fresh.FourPairStepPhysical
