import Fresh.PhaseNeighbour
import Fresh.ThreeBlockNeighbour
import Fresh.FourAPPairs

/-! Rules:1–4,8–18. Four original unit-step AP blocks, all35positive size
partitions of8, with three independent gap laps. Six internal subjects
share the native neighbour rule; no original gap-sum cap is imposed.
The original full-cascade map precedes the proof. Integer laps are supplied
by explicit input bands, never assumed to exist for arbitrary gaps. -/
namespace Fresh.FourBlockNeighbour
open Fresh Fresh.OneMover

-- STANDING: DEFINITION
noncomputable def speeds (c g h j : ℝ) (p q r : ℕ) (i : Fin 8) : ℝ :=
  c+1+(i : ℝ)+(if p ≤ (i : ℕ) then g-1 else 0)+
    (if p+q ≤ (i : ℕ) then h-1 else 0)+(if p+q+r ≤ (i : ℕ) then j-1 else 0)

def wholeLap (m a b e : ℤ) (p q r : ℕ) (i : Fin 8) : ℤ :=
  (((i : ℕ) : ℤ)+1)*m+(if p ≤ (i : ℕ) then a-m else 0)+
    (if p+q ≤ (i : ℕ) then b-m else 0)+(if p+q+r ≤ (i : ℕ) then e-m else 0)

noncomputable def phase (c g h j : ℝ) (p q r : ℕ) (m a b e : ℤ) (i : Fin 8) : ℝ :=
  c*((m : ℝ)+1/8)+((i : ℝ)+1)/8+
    (if p ≤ (i : ℕ) then g*((m : ℝ)+1/8)-(a : ℝ)-1/8 else 0)+
    (if p+q ≤ (i : ℕ) then h*((m : ℝ)+1/8)-(b : ℝ)-1/8 else 0)+
    (if p+q+r ≤ (i : ℕ) then j*((m : ℝ)+1/8)-(e : ℝ)-1/8 else 0)

theorem phase_identity (c g h j : ℝ) (p q r : ℕ) (m a b e : ℤ) (i : Fin 8) :
    speeds c g h j p q r i*((m : ℝ)+1/8)=
      phase c g h j p q r m a b e i+(wholeLap m a b e p q r i : ℝ) := by
  simp only [speeds,phase,wholeLap]
  split_ifs <;> push_cast <;> ring

theorem cut_increment (b i : ℕ) (x : ℝ) :
    (if b ≤ i+1 then x else 0)-(if b ≤ i then x else 0)=
      if i+1=b then x else 0 := by
  split_ifs <;> simp_all <;> omega

theorem adjacent_phase_gap (c g h j : ℝ) (p q r : ℕ)
    (hq : 1 ≤ q) (hr : 1 ≤ r) (m a b e : ℤ) (i : Fin 7) :
    phase c g h j p q r m a b e i.succ-phase c g h j p q r m a b e i.castSucc =
      if (i : ℕ)+1=p then g*((m : ℝ)+1/8)-(a : ℝ)
      else if (i : ℕ)+1=p+q then h*((m : ℝ)+1/8)-(b : ℝ)
      else if (i : ℕ)+1=p+q+r then j*((m : ℝ)+1/8)-(e : ℝ)
      else 1/8 := by
  have heq : phase c g h j p q r m a b e i.succ-phase c g h j p q r m a b e i.castSucc =
      1/8+ (if (i : ℕ)+1=p then g*((m : ℝ)+1/8)-(a : ℝ)-1/8 else 0)+
      (if (i : ℕ)+1=p+q then h*((m : ℝ)+1/8)-(b : ℝ)-1/8 else 0)+
      (if (i : ℕ)+1=p+q+r then j*((m : ℝ)+1/8)-(e : ℝ)-1/8 else 0) := by
    simp only [phase,Fin.val_succ,Fin.val_castSucc,Nat.cast_add,Nat.cast_one]
    rw [←cut_increment p (i : ℕ),←cut_increment (p+q) (i : ℕ),←cut_increment (p+q+r) (i : ℕ)]
    ring
  rw [heq]
  by_cases hA : (i : ℕ)+1=p
  · have hB : (i : ℕ)+1 ≠ p+q := by omega
    have hC : (i : ℕ)+1 ≠ p+q+r := by omega
    simp only [if_pos hA,if_neg hB,if_neg hC]
    ring
  · by_cases hB : (i : ℕ)+1=p+q
    · have hC : (i : ℕ)+1 ≠ p+q+r := by omega
      simp only [if_neg hA,if_pos hB,if_neg hC]
      ring
    · by_cases hC : (i : ℕ)+1=p+q+r
      · simp only [if_neg hA,if_neg hB,if_pos hC]; ring
      · simp only [if_neg hA,if_neg hB,if_neg hC]; ring

theorem phase_span (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 7) (m a b e : ℤ) :
    phase c g h j p q r m a b e (7 : Fin 8)-phase c g h j p q r m a b e 0 =
      1/2+(g+h+j)*((m : ℝ)+1/8)-((a : ℝ)+(b : ℝ)+(e : ℝ)) := by
  have hp7 : p ≤ 7 := by omega
  have hpq7 : p+q ≤ 7 := by omega
  have hp0 : ¬p ≤ 0 := by omega
  have hpq0 : ¬p+q ≤ 0 := by omega
  have hpqr0 : ¬p+q+r ≤ 0 := by omega
  norm_num [phase,hp7,hpq7,hs,hp0,hpq0,hpqr0]
  ring

theorem internal_at_reference (c g h j : ℝ) (p q r : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : p+q+r ≤ 7) (m a b e : ℤ)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hj : 8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j)
    (hsum : (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4)
    (k : Fin 8) (hk1 : 1 ≤ (k : ℕ)) (hk6 : (k : ℕ) ≤ 6) :
    IsolatedAt (speeds c g h j p q r) k ((m : ℝ)+1/8) := by
  have hu : (1/8 : ℝ) ≤ g*((m : ℝ)+1/8)-(a : ℝ) := by nlinarith
  have hv : (1/8 : ℝ) ≤ h*((m : ℝ)+1/8)-(b : ℝ) := by nlinarith
  have hw : (1/8 : ℝ) ≤ j*((m : ℝ)+1/8)-(e : ℝ) := by nlinarith
  have ht : (g+h+j)*((m : ℝ)+1/8)-((a : ℝ)+(b : ℝ)+(e : ℝ)) ≤ 1/2 := by nlinarith
  apply Fresh.PhaseNeighbour.phase_neighbour (speeds c g h j p q r)
    (phase c g h j p q r m a b e) (wholeLap m a b e p q r) ((m : ℝ)+1/8)
    (phase_identity c g h j p q r m a b e) ?_ ?_ k hk1 hk6
  · intro i
    rw [adjacent_phase_gap c g h j p q r hq hr m a b e i]
    split_ifs <;> linarith
  · rw [phase_span c g h j p q r hp hq hr hs m a b e]
    linarith

-- STANDING: DEFINITION
def FourBlockInternalClass (V : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  (∀i,0<V i)  ∧  Function.Injective V  ∧ 
  ∃(c g h j B z : ℝ)(p q r : ℕ)(m a b e : ℤ)(σ : Equiv.Perm (Fin 8)),
    1 ≤ p  ∧  1 ≤ q  ∧  1 ≤ r  ∧  p+q+r ≤ 7  ∧  0<g  ∧  0<h  ∧  0<j  ∧  1 ≤ m  ∧ 
    8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g  ∧ 
    8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h  ∧ 
    8*(e : ℝ)+1 ≤ (8*(m : ℝ)+1)*j  ∧ 
    (8*(m : ℝ)+1)*(g+h+j) ≤ 8*((a : ℝ)+(b : ℝ)+(e : ℝ))+4  ∧ 
    1 ≤ ((σ k : Fin 8) : ℕ)  ∧  ((σ k : Fin 8) : ℕ) ≤ 6  ∧  z ≠ 0  ∧ 
    V=(fun i=>B+z*speeds c g h j p q r (σ i))

theorem fourBlockInternal_isolation {V : Fin 8 → ℝ} {k : Fin 8}
    (hV : FourBlockInternalClass V k) : Isolation V k := by
  obtain ⟨hpos,hinj,c,g,h,j,B,z,p,q,r,m,a,b,e,σ,hp,hq,hr,hs,hgpos,hhpos,hjpos,hm,hg,hh,hj,hsum,hk1,hk6,hz,hV⟩ := hV
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hi : Isolation (speeds c g h j p q r) (σ k) :=
    ⟨(m : ℝ)+1/8,by linarith,internal_at_reference c g h j p q r hp hq hr hs m a b e hg hh hj hsum (σ k) hk1 hk6⟩
  rw [hV]
  exact (Fresh.isolation_comp_perm _ σ k).2 (subject_isolation_affine B z hz hi)

#print axioms phase_identity
#print axioms cut_increment
#print axioms adjacent_phase_gap
#print axioms phase_span
#print axioms internal_at_reference
#print axioms fourBlockInternal_isolation
end Fresh.FourBlockNeighbour
