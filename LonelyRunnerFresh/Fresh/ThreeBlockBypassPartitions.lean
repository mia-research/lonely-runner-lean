import Fresh.ThreeBlockBypassKernel
import Fresh.ThreeBlockPartitions

/-! Rules:1–4,8–18. Native first-move bypass for every ordered three-AP-block
size p≥2,q≥2,r=8−p−q≥1. Original subject is the last member of the left
block. The three integer-part ranges are derived from the physical labels;
all ten dimensions and closed-face co-setter ties were mapped first. -/
open Classical
namespace Fresh.ThreeBlockBypassPartitions
open Fresh Fresh.Cascade Fresh.Localisation Fresh.ThreeBlockPartitions
  Fresh.ThreeBlockBypassKernel

theorem physical_reading_shape (c g h : ℝ) (p q : ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q) (hsizes : p+q ≤ 7)
    (hg : 0<g) (hh : 0<h) (k : Fin 8) (hk : (k : ℕ)=p-1) :
    ∀d∈disparitySet (speeds c g h p q) k,
      (∃j : ℕ, 1 ≤ j ∧ j ≤ 4 ∧ d=(j : ℝ)) ∨
      (∃j : ℕ, j ≤ 4 ∧ d=g+(j : ℝ)) ∨
      (∃j : ℕ, 1 ≤ j ∧ j ≤ 4 ∧ d=g+h+(j : ℝ)) := by
  have hkp : (k : ℕ)<p := by omega
  have hkcast : ((p-1 : ℕ) : ℝ)=(p : ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p)]
    norm_num
  intro d hd
  obtain ⟨i,hik,rfl⟩ := mem_disparitySet.mp hd
  have hi8 := i.isLt
  by_cases hip : (i : ℕ)<p
  · let j := p-1-(i : ℕ)
    have hj1 : 1 ≤ j := by dsimp [j]; have := Fin.val_ne_of_ne hik; omega
    have hj4 : j ≤ 4 := by dsimp [j]; omega
    have hcast : (j : ℝ)=((p-1 : ℕ) : ℝ)-((i : ℕ) : ℝ) := by
      dsimp [j]
      rw [Nat.cast_sub (by omega : (i : ℕ) ≤ p-1)]
    have he : speeds c g h p q i-speeds c g h p q k=-(j : ℝ) := by
      simp only [speeds,if_pos hip,if_pos hkp]
      rw [hcast,hk]
      ring
    refine Or.inl ⟨j,hj1,hj4,?_⟩
    rw [he,abs_neg,abs_of_nonneg (Nat.cast_nonneg j)]
  · by_cases hiq : (i : ℕ)<p+q
    · let j := (i : ℕ)-p
      have hj4 : j ≤ 4 := by dsimp [j]; omega
      have hcast : (j : ℝ)=((i : ℕ) : ℝ)-(p : ℝ) := by
        dsimp [j]
        rw [Nat.cast_sub (by omega : p ≤ (i : ℕ))]
      have he : speeds c g h p q i-speeds c g h p q k=g+(j : ℝ) := by
        simp only [speeds,if_neg hip,if_pos hiq,if_pos hkp]
        rw [hcast,hk,hkcast]
        ring
      refine Or.inr (Or.inl ⟨j,hj4,?_⟩)
      rw [he,abs_of_nonneg (by have := Nat.cast_nonneg (α := ℝ) j; linarith)]
    · let j := (i : ℕ)-p-1
      have hj1 : 1 ≤ j := by dsimp [j]; omega
      have hj4 : j ≤ 4 := by dsimp [j]; omega
      have hcast : (j : ℝ)=((i : ℕ) : ℝ)-(p : ℝ)-1 := by
        dsimp [j]
        rw [Nat.cast_sub (by omega : 1 ≤ (i : ℕ)-p),Nat.cast_sub (by omega : p ≤ (i : ℕ))]
        norm_num
      have he : speeds c g h p q i-speeds c g h p q k=g+h+(j : ℝ) := by
        simp only [speeds,if_neg hip,if_neg hiq,if_pos hkp]
        rw [hcast,hk,hkcast]
        ring
      refine Or.inr (Or.inr ⟨j,hj1,hj4,?_⟩)
      rw [he,abs_of_nonneg (by have := Nat.cast_nonneg (α := ℝ) j; linarith)]

theorem physical_gate_members (c g h : ℝ) (p q : ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q) (hsizes : p+q ≤ 7)
    (hg : 0<g) (k : Fin 8) (hk : (k : ℕ)=p-1) :
    g∈disparitySet (speeds c g h p q) k ∧ (1 : ℝ)∈disparitySet (speeds c g h p q) k := by
  have hkp : (k : ℕ)<p := by omega
  have hkcast : ((p-1 : ℕ) : ℝ)=(p : ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ p)]
    norm_num
  constructor
  · let i : Fin 8 := ⟨p,by omega⟩
    apply mem_disparitySet.mpr
    refine ⟨i,by intro he; have := congrArg Fin.val he; dsimp [i] at this; omega,?_⟩
    have he : speeds c g h p q i-speeds c g h p q k=g := by
      simp only [speeds]
      rw [if_neg (by dsimp [i]; omega),if_pos (by dsimp [i]; omega),if_pos hkp]
      dsimp [i]
      rw [hk,hkcast]
      ring
    rw [he,abs_of_pos hg]
  · let i : Fin 8 := ⟨p-2,by omega⟩
    apply mem_disparitySet.mpr
    refine ⟨i,by intro he; have := congrArg Fin.val he; dsimp [i] at this; omega,?_⟩
    have hicast : ((p-2 : ℕ) : ℝ)=(p : ℝ)-2 := by
      rw [Nat.cast_sub hp]
      norm_num
    have he : speeds c g h p q i-speeds c g h p q k=(-1 : ℝ) := by
      simp only [speeds]
      rw [if_pos (by dsimp [i]; omega),if_pos hkp]
      dsimp [i]
      rw [hk,hkcast,hicast]
      ring
    rw [he]
    norm_num

theorem physical_partition_native_bypass (c g h : ℝ) (p q : ℕ)
    (hp : 2 ≤ p) (hq : 2 ≤ q) (hsizes : p+q ≤ 7)
    (m n : ℤ) (hm : 1 ≤ m) (hg : 0<g) (hh : 0<h)
    (hentry1 : 1<(8*(m : ℝ)+1)*g)
    (hentry2 : (8*(m : ℝ)-1)*g<1)
    (hlo : 8*(n : ℝ) ≤ (8*(m : ℝ)+1)*(g+h))
    (hhi : (8*(m : ℝ)+1)*(g+h) ≤ 8*(n : ℝ)+3)
    (k : Fin 8) (hk : (k : ℕ)=p-1) :
    IsLeast (disparitySet (speeds c g h p q) k : Set ℝ) g ∧ InWay 1 (1/(8*g)) ∧
    IsMove (disparitySet (speeds c g h p q) k) (1/(8*g)) ((m : ℝ)+1/8) ∧
    LonelyAt (disparitySet (speeds c g h p q) k) ((m : ℝ)+1/8) := by
  obtain ⟨hgm,h1m⟩ := physical_gate_members c g h p q hp hq hsizes hg k hk
  exact native_shape_bypass g h m n hm hg hh hentry1 hentry2 hlo hhi hgm h1m
    (physical_reading_shape c g h p q hp hq hsizes hg hh k hk)

#print axioms physical_reading_shape
#print axioms physical_gate_members
#print axioms physical_partition_native_bypass
end Fresh.ThreeBlockBypassPartitions
