import Fresh.ThreeBlockEndpointBounds
import Fresh.PhaseNeighbour
import Fresh.ThreeBlockPartitions

/-! Original three-block gaps give an ordered native phase lift.
The integer laps are explicit; all internal subjects share the reference.
Exact original-cascade replay: phase_neighbour_map_v1.py/json. -/
namespace Fresh.ThreeBlockNeighbour
open Fresh Fresh.OneMover Fresh.ThreeBlockPartitions

def wholeLap (m a b : ℤ) (p q : ℕ) (i : Fin 8) : ℤ :=
  if (i : ℕ)<p then (((i : ℕ) : ℤ)+1)*m
  else if (i : ℕ)<p+q then ((i : ℕ) : ℤ)*m+a
  else (((i : ℕ) : ℤ)-1)*m+a+b

noncomputable def phase (c g h : ℝ) (p q : ℕ) (m a b : ℤ) (i : Fin 8) : ℝ :=
  speeds c g h p q i*((m : ℝ)+1/8)-(wholeLap m a b p q i : ℝ)

theorem adjacent_phase_gap (c g h : ℝ) (p q : ℕ) (hq : 1 ≤ q)
    (m a b : ℤ) (i : Fin 7) :
    phase c g h p q m a b i.succ-phase c g h p q m a b i.castSucc =
      if (i : ℕ)+1=p then g*((m : ℝ)+1/8)-(a : ℝ)
      else if (i : ℕ)+1=p+q then h*((m : ℝ)+1/8)-(b : ℝ)
      else 1/8 := by
  have hq0 : 0 < q := by omega
  have hqne : q ≠ 0 := by omega
  by_cases hA : (i : ℕ)+1=p
  · have hAr : ((i : ℕ) : ℝ)+1=(p : ℝ) := by exact_mod_cast hA
    have hL : (i : ℕ)<p := by omega
    have hR : ¬(i : ℕ)+1<p := by omega
    have hRq : (i : ℕ)+1<p+q := by omega
    simp [phase,wholeLap,speeds,Fin.val_succ,Fin.val_castSucc,hL,hR,hRq,hA,hq0]
    push_cast
    nlinarith [hAr]
  · by_cases hB : (i : ℕ)+1=p+q
    · have hBr : ((i : ℕ) : ℝ)+1=(p : ℝ)+(q : ℝ) := by exact_mod_cast hB
      have hL : ¬(i : ℕ)<p := by omega
      have hLq : (i : ℕ)<p+q := by omega
      have hR : ¬(i : ℕ)+1<p := by omega
      have hRq : ¬(i : ℕ)+1<p+q := by omega
      simp [phase,wholeLap,speeds,Fin.val_succ,Fin.val_castSucc,hL,hLq,hR,hRq,hA,hB,hqne]
      push_cast
      nlinarith [hBr]
    · by_cases hL : (i : ℕ)<p
      · have hR : (i : ℕ)+1<p := by omega
        simp [phase,wholeLap,speeds,Fin.val_succ,Fin.val_castSucc,hL,hR,hA,hB]
        push_cast
        ring
      · by_cases hLq : (i : ℕ)<p+q
        · have hR : ¬(i : ℕ)+1<p := by omega
          have hRq : (i : ℕ)+1<p+q := by omega
          simp [phase,wholeLap,speeds,Fin.val_succ,Fin.val_castSucc,hL,hLq,hR,hRq,hA,hB]
          push_cast
          ring
        · have hR : ¬(i : ℕ)+1<p := by omega
          have hRq : ¬(i : ℕ)+1<p+q := by omega
          simp [phase,wholeLap,speeds,Fin.val_succ,Fin.val_castSucc,hL,hLq,hR,hRq,hA,hB]
          push_cast
          ring

theorem phase_span (c g h : ℝ) (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hpq : p+q ≤ 7) (m a b : ℤ) :
    phase c g h p q m a b (7 : Fin 8)-phase c g h p q m a b 0 =
      5/8+(g+h)*((m : ℝ)+1/8)-((a : ℝ)+(b : ℝ)) := by
  have h0 : (0 : ℕ)<p := by omega
  have h7 : ¬(7 : ℕ)<p := by omega
  have h7q : ¬(7 : ℕ)<p+q := by omega
  norm_num [phase,wholeLap,speeds,h0,h7,h7q]
  ring

#print axioms adjacent_phase_gap
#print axioms phase_span

theorem internal_at_reference (c g h : ℝ) (p q : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hpq : p+q ≤ 7) (m a b : ℤ)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hsum : (8*(m : ℝ)+1)*(g+h) ≤ 8*((a : ℝ)+(b : ℝ))+3)
    (k : Fin 8) (hk1 : 1 ≤ (k : ℕ)) (hk6 : (k : ℕ) ≤ 6) :
    IsolatedAt (speeds c g h p q) k ((m : ℝ)+1/8) := by
  have hu : (1/8 : ℝ) ≤ g*((m : ℝ)+1/8)-(a : ℝ) := by nlinarith
  have hv : (1/8 : ℝ) ≤ h*((m : ℝ)+1/8)-(b : ℝ) := by nlinarith
  have huv : (g+h)*((m : ℝ)+1/8)-((a : ℝ)+(b : ℝ)) ≤ 3/8 := by nlinarith
  apply Fresh.PhaseNeighbour.phase_neighbour (speeds c g h p q)
    (phase c g h p q m a b) (wholeLap m a b p q) ((m : ℝ)+1/8)
    ?_ ?_ ?_ k hk1 hk6
  · intro i
    dsimp [phase]
    ring
  · intro i
    rw [adjacent_phase_gap c g h p q hq m a b i]
    split_ifs <;> linarith
  · rw [phase_span c g h p q hp hq hpq m a b]
    linarith

-- STANDING: DEFINITION
def ThreeBlockInternalClass (V : Fin 8 → ℝ) (k : Fin 8) : Prop :=
  (∀ i, 0 < V i) ∧ Function.Injective V ∧
  ∃ (c g h B z : ℝ) (p q : ℕ) (m a b : ℤ) (σ : Equiv.Perm (Fin 8)),
    1 ≤ p ∧ 1 ≤ q ∧ p+q ≤ 7 ∧ 0 < g ∧ 0 < h ∧ 1 ≤ m ∧
    8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g ∧
    8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h ∧
    (8*(m : ℝ)+1)*(g+h) ≤ 8*((a : ℝ)+(b : ℝ))+3 ∧
    1 ≤ ((σ k : Fin 8) : ℕ) ∧ ((σ k : Fin 8) : ℕ) ≤ 6 ∧ z ≠ 0 ∧
    V=(fun i => B+z*speeds c g h p q (σ i))

theorem threeBlockInternal_isolation {V : Fin 8 → ℝ} {k : Fin 8}
    (h : ThreeBlockInternalClass V k) : Isolation V k := by
  obtain ⟨hpos,hinj,c,g,h,B,z,p,q,m,a,b,σ,hp,hq,hpq,hgpos,hhpos,hm,hg,hh,hsum,hk1,hk6,hz,hV⟩ := h
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hi : Isolation (speeds c g h p q) (σ k) :=
    ⟨(m : ℝ)+1/8,by linarith,internal_at_reference c g h p q hp hq hpq m a b hg hh hsum (σ k) hk1 hk6⟩
  rw [hV]
  exact (Fresh.isolation_comp_perm _ σ k).2 (subject_isolation_affine B z hz hi)

#print axioms internal_at_reference
#print axioms threeBlockInternal_isolation


theorem all_subjects (c g h : ℝ) (p q : ℕ)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hpq : p+q ≤ 7)
    (hgpos : 0 < g) (hhpos : 0 < h) (hsmall : g+h ≤ 2)
    (hleft : p=1 → 1 ≤ g) (hright : p+q=7 → 1 ≤ h)
    (m a b : ℤ) (hm : 1 ≤ m)
    (hg : 8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h)
    (hsum : (8*(m : ℝ)+1)*(g+h) ≤ 8*((a : ℝ)+(b : ℝ))+3) :
    ∀ k : Fin 8, Isolation (speeds c g h p q) k := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  intro k
  by_cases hk0 : k=0
  · subst k
    exact ⟨1/8,by norm_num,Fresh.ThreeBlockEndpointBounds.left_direct c g h p q hp hq hpq hgpos hhpos hsmall hleft⟩
  · by_cases hk7 : k=7
    · subst k
      exact ⟨1/8,by norm_num,Fresh.ThreeBlockEndpointBounds.right_direct c g h p q hp hq hpq hgpos hhpos hsmall hright⟩
    · have hne0 : (k : ℕ) ≠ 0 := by simpa using Fin.val_ne_of_ne hk0
      have hne7 : (k : ℕ) ≠ 7 := by simpa using Fin.val_ne_of_ne hk7
      have hi := k.isLt
      exact ⟨(m : ℝ)+1/8,by linarith,
        internal_at_reference c g h p q hp hq hpq m a b hg hh hsum k (by omega) (by omega)⟩

-- STANDING: DEFINITION
def ThreeBlockNeighbourClass (V : Fin 8 → ℝ) : Prop :=
  (∀ i, 0 < V i) ∧ Function.Injective V ∧
  ∃ (c g h B z : ℝ) (p q : ℕ) (m a b : ℤ) (σ : Equiv.Perm (Fin 8)),
    1 ≤ p ∧ 1 ≤ q ∧ p+q ≤ 7 ∧ 0 < g ∧ 0 < h ∧ g+h ≤ 2 ∧
    (p=1 → 1 ≤ g) ∧ (p+q=7 → 1 ≤ h) ∧ 1 ≤ m ∧
    8*(a : ℝ)+1 ≤ (8*(m : ℝ)+1)*g ∧
    8*(b : ℝ)+1 ≤ (8*(m : ℝ)+1)*h ∧
    (8*(m : ℝ)+1)*(g+h) ≤ 8*((a : ℝ)+(b : ℝ))+3 ∧ z ≠ 0 ∧
    V=(fun i => B+z*speeds c g h p q (σ i))

theorem threeBlockNeighbour_isolation {V : Fin 8 → ℝ}
    (h : ThreeBlockNeighbourClass V) (k : Fin 8) : Isolation V k := by
  obtain ⟨hpos,hinj,c,g,h,B,z,p,q,m,a,b,σ,hp,hq,hpq,hgpos,hhpos,hsmall,hleft,hright,hm,hg,hh,hsum,hz,hV⟩ := h
  have hi := all_subjects c g h p q hp hq hpq hgpos hhpos hsmall hleft hright m a b hm hg hh hsum (σ k)
  rw [hV]
  exact (Fresh.isolation_comp_perm _ σ k).2 (subject_isolation_affine B z hz hi)

#print axioms all_subjects
#print axioms threeBlockNeighbour_isolation

end Fresh.ThreeBlockNeighbour
