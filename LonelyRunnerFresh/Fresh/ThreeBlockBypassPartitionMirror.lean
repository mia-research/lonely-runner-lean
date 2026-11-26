import Fresh.ThreeBlockBypassPartitions

/-! Rules:1–4,8–18. Reflected native bypass for first member of the right
block, with original labels and actual disparity provenance. Leftblock
may be singleton; middle and right blocks have at least2members. Exact
reflection controls preceded this theorem; co-setter ties remain allowed. -/
open Classical
namespace Fresh.ThreeBlockBypassPartitionMirror
open Fresh Fresh.Cascade Fresh.Localisation Fresh.ThreeBlockPartitions
  Fresh.ThreeBlockBypassKernel

theorem reflected_reading_shape (c g h : ℝ) (p q : ℕ)
    (hp : 1 ≤ p) (hq : 2 ≤ q) (hsizes : p+q ≤ 6)
    (hg : 0<g) (hh : 0<h) (k : Fin 8) (hk : (k : ℕ)=p+q) :
    ∀d∈disparitySet (speeds c g h p q) k,
      (∃j : ℕ, 1 ≤ j ∧ j ≤ 4 ∧ d=(j : ℝ)) ∨
      (∃j : ℕ, j ≤ 4 ∧ d=h+(j : ℝ)) ∨
      (∃j : ℕ, 1 ≤ j ∧ j ≤ 4 ∧ d=h+g+(j : ℝ)) := by
  have hkp : ¬(k : ℕ)<p := by omega
  have hkq : ¬(k : ℕ)<p+q := by omega
  intro d hd
  obtain ⟨i,hik,rfl⟩ := mem_disparitySet.mp hd
  have hi8 := i.isLt
  by_cases hip : (i : ℕ)<p
  · let j := p+q-2-(i : ℕ)
    have hj1 : 1 ≤ j := by dsimp [j]; omega
    have hj4 : j ≤ 4 := by dsimp [j]; omega
    have hcast : (j : ℝ)=(p : ℝ)+(q : ℝ)-2-((i : ℕ) : ℝ) := by
      dsimp [j]
      rw [Nat.cast_sub (by omega : (i : ℕ) ≤ p+q-2),Nat.cast_sub (by omega : 2 ≤ p+q)]
      push_cast
      ring
    have he : speeds c g h p q i-speeds c g h p q k=-(h+g+(j : ℝ)) := by
      simp only [speeds,if_pos hip,if_neg hkp,if_neg hkq]
      rw [hcast,hk,Nat.cast_add]
      ring
    refine Or.inr (Or.inr ⟨j,hj1,hj4,?_⟩)
    rw [he,abs_neg,abs_of_nonneg (by have := Nat.cast_nonneg (α := ℝ) j; linarith)]
  · by_cases hiq : (i : ℕ)<p+q
    · let j := p+q-1-(i : ℕ)
      have hj4 : j ≤ 4 := by dsimp [j]; omega
      have hcast : (j : ℝ)=(p : ℝ)+(q : ℝ)-1-((i : ℕ) : ℝ) := by
        dsimp [j]
        rw [Nat.cast_sub (by omega : (i : ℕ) ≤ p+q-1),Nat.cast_sub (by omega : 1 ≤ p+q)]
        push_cast
        ring
      have he : speeds c g h p q i-speeds c g h p q k=-(h+(j : ℝ)) := by
        simp only [speeds,if_neg hip,if_pos hiq,if_neg hkp,if_neg hkq]
        rw [hcast,hk,Nat.cast_add]
        ring
      refine Or.inr (Or.inl ⟨j,hj4,?_⟩)
      rw [he,abs_neg,abs_of_nonneg (by have := Nat.cast_nonneg (α := ℝ) j; linarith)]
    · let j := (i : ℕ)-(p+q)
      have hj1 : 1 ≤ j := by dsimp [j]; have := Fin.val_ne_of_ne hik; omega
      have hj4 : j ≤ 4 := by dsimp [j]; omega
      have hcast : (j : ℝ)=((i : ℕ) : ℝ)-((p+q : ℕ) : ℝ) := by
        dsimp [j]
        rw [Nat.cast_sub (by omega : p+q ≤ (i : ℕ))]
      have he : speeds c g h p q i-speeds c g h p q k=(j : ℝ) := by
        simp only [speeds,if_neg hip,if_neg hiq,if_neg hkp,if_neg hkq]
        rw [hcast,hk]
        ring
      refine Or.inl ⟨j,hj1,hj4,?_⟩
      rw [he,abs_of_nonneg (Nat.cast_nonneg j)]

theorem reflected_gate_members (c g h : ℝ) (p q : ℕ)
    (hp : 1 ≤ p) (hq : 2 ≤ q) (hsizes : p+q ≤ 6)
    (hh : 0<h) (k : Fin 8) (hk : (k : ℕ)=p+q) :
    h∈disparitySet (speeds c g h p q) k ∧ (1 : ℝ)∈disparitySet (speeds c g h p q) k := by
  have hkp : ¬(k : ℕ)<p := by omega
  have hkq : ¬(k : ℕ)<p+q := by omega
  constructor
  · let i : Fin 8 := ⟨p+q-1,by omega⟩
    apply mem_disparitySet.mpr
    refine ⟨i,by intro he; have := congrArg Fin.val he; dsimp [i] at this; omega,?_⟩
    have hicast : ((p+q-1 : ℕ) : ℝ)=((p+q : ℕ) : ℝ)-1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ p+q)]
      norm_num
    have he : speeds c g h p q i-speeds c g h p q k=-h := by
      simp only [speeds]
      rw [if_neg (by dsimp [i]; omega),if_pos (by dsimp [i]; omega),if_neg hkp,if_neg hkq]
      dsimp [i]
      rw [hk,hicast]
      ring
    rw [he,abs_neg,abs_of_pos hh]
  · let i : Fin 8 := ⟨p+q+1,by omega⟩
    apply mem_disparitySet.mpr
    refine ⟨i,by intro he; have := congrArg Fin.val he; dsimp [i] at this; omega,?_⟩
    have he : speeds c g h p q i-speeds c g h p q k=(1 : ℝ) := by
      simp only [speeds]
      rw [if_neg (by dsimp [i]; omega),if_neg (by dsimp [i]; omega),if_neg hkp,if_neg hkq]
      dsimp [i]
      rw [hk,Nat.cast_add]
      norm_num <;> ring
    rw [he]
    norm_num

theorem reflected_partition_native_bypass (c g h : ℝ) (p q : ℕ)
    (hp : 1 ≤ p) (hq : 2 ≤ q) (hsizes : p+q ≤ 6)
    (m n : ℤ) (hm : 1 ≤ m) (hg : 0<g) (hh : 0<h)
    (hentry1 : 1<(8*(m : ℝ)+1)*h)
    (hentry2 : (8*(m : ℝ)-1)*h<1)
    (hlo : 8*(n : ℝ) ≤ (8*(m : ℝ)+1)*(g+h))
    (hhi : (8*(m : ℝ)+1)*(g+h) ≤ 8*(n : ℝ)+3)
    (k : Fin 8) (hk : (k : ℕ)=p+q) :
    IsLeast (disparitySet (speeds c g h p q) k : Set ℝ) h ∧ InWay 1 (1/(8*h)) ∧
    IsMove (disparitySet (speeds c g h p q) k) (1/(8*h)) ((m : ℝ)+1/8) ∧
    LonelyAt (disparitySet (speeds c g h p q) k) ((m : ℝ)+1/8) := by
  obtain ⟨hgm,h1m⟩ := reflected_gate_members c g h p q hp hq hsizes hh k hk
  exact native_shape_bypass h g m n hm hh hg hentry1 hentry2
    (by simpa [add_comm] using hlo) (by simpa [add_comm] using hhi) hgm h1m
    (reflected_reading_shape c g h p q hp hq hsizes hg hh k hk)

#print axioms reflected_reading_shape
#print axioms reflected_gate_members
#print axioms reflected_partition_native_bypass
end Fresh.ThreeBlockBypassPartitionMirror
