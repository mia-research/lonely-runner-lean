import Fresh.FourBlockDoubleSingletonArrangement

/-! Exact reversal of four original physical blocks and integer gap laps.
Original disparity sets, and hence actual cascade moves, are identical.
This is a size/orientation reduction, not existence of native inputs. -/
namespace Fresh.FourBlockReversal
open Fresh Fresh.Localisation Fresh.FourBlockNeighbour

def rev (i : Fin 8) : Fin 8 := ⟨7-i.val,by omega⟩

theorem rev_rev (i : Fin 8) : rev (rev i)=i := by
  apply Fin.ext
  dsimp [rev]
  have := i.isLt
  omega

def reversal : Equiv.Perm (Fin 8) :=
  ⟨rev,rev,rev_rev,rev_rev⟩

theorem cut_complement {α : Type*} [AddZeroClass α] (a b : ℕ) (hs : a+b=8) (i : Fin 8) (x : α) :
    (if a ≤ (rev i).val then x else 0)+(if b ≤ i.val then x else 0)=x := by
  have hi := i.isLt
  by_cases ha : a ≤ (rev i).val
  · have hb : ¬ b ≤ i.val := by dsimp [rev] at ha; omega
    simp [ha,hb]
  · have hb : b ≤ i.val := by dsimp [rev] at ha; omega
    simp [ha,hb]

theorem speed_reversal (c g h j : ℝ) (p q r s : ℕ) (hs : p+q+r+s=8) (i : Fin 8) :
    speeds c j h g s r q i+speeds c g h j p q r (rev i)=2*c+6+g+h+j := by
  have h1 := cut_complement p (s+r+q) (by omega) i (g-1)
  have h2 := cut_complement (p+q) (s+r) (by omega) i (h-1)
  have h3 := cut_complement (p+q+r) s (by omega) i (j-1)
  have hn : (rev i).val+i.val=7 := by dsimp [rev]; have := i.isLt; omega
  have hc : (rev i : ℝ)+(i : ℝ)=7 := by exact_mod_cast hn
  dsimp [speeds]
  linarith only [h1,h2,h3,hc]

theorem lap_reversal (m a b e : ℤ) (p q r s : ℕ) (hs : p+q+r+s=8) (i : Fin 8) :
    wholeLap m e b a s r q i+wholeLap m a b e p q r (rev i)=6*m+a+b+e := by
  have h1 := cut_complement p (s+r+q) (by omega) i (a-m)
  have h2 := cut_complement (p+q) (s+r) (by omega) i (b-m)
  have h3 := cut_complement (p+q+r) s (by omega) i (e-m)
  have hn : (rev i).val+i.val=7 := by dsimp [rev]; have := i.isLt; omega
  have hc : ((rev i).val : ℤ)+(i.val : ℤ)=7 := by exact_mod_cast hn
  have hscaled := congrArg (fun z : ℤ => z*m) hc
  dsimp [wholeLap]
  nlinarith only [h1,h2,h3,hscaled]

theorem disparity_reversal (c g h j : ℝ) (p q r s : ℕ) (hs : p+q+r+s=8) (k : Fin 8) :
    disparitySet (speeds c j h g s r q) k=disparitySet (speeds c g h j p q r) (rev k) := by
  have habs (i : Fin 8) : |speeds c j h g s r q i-speeds c j h g s r q k|=
      |speeds c g h j p q r (rev i)-speeds c g h j p q r (rev k)| := by
    have hi := speed_reversal c g h j p q r s hs i
    have hk := speed_reversal c g h j p q r s hs k
    have hd : speeds c j h g s r q i-speeds c j h g s r q k=
      -(speeds c g h j p q r (rev i)-speeds c g h j p q r (rev k)) := by linarith only [hi,hk]
    rw [hd,abs_neg]
  ext d
  rw [mem_disparitySet,mem_disparitySet]
  constructor
  · rintro ⟨i,hi,rfl⟩
    refine ⟨rev i,fun he => hi (reversal.injective he),?_⟩
    exact (habs i).symm
  · rintro ⟨i,hi,rfl⟩
    refine ⟨rev i,?_,?_⟩
    · intro he
      have hh := congrArg rev he
      rw [rev_rev] at hh
      exact hi hh
    · rw [habs,rev_rev]

theorem isolation_reversal (c g h j : ℝ) (p q r s : ℕ) (hs : p+q+r+s=8) (k : Fin 8) :
    Isolation (speeds c j h g s r q) k ↔ Isolation (speeds c g h j p q r) (rev k) := by
  simp only [Isolation,Fresh.Localisation.isolatedAt_iff,disparity_reversal c g h j p q r s hs k]

theorem move_reversal (c g h j : ℝ) (p q r s : ℕ) (hs : p+q+r+s=8) (k : Fin 8) (Q P : ℝ) :
    IsMove (disparitySet (speeds c j h g s r q) k) Q P ↔
      IsMove (disparitySet (speeds c g h j p q r) (rev k)) Q P := by
  rw [disparity_reversal c g h j p q r s hs k]

theorem size_orientation (p q r s : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hs : 1 ≤ s)
    (ht : p+q+r+s=8) :
    (2 ≤ p ∧ 2 ≤ s) ∨
    (p=1 ∧ 2 ≤ s ∧ (s≥4 ∨ (s=3 ∧ q+r=4) ∨ (s=2 ∧ q+r=5))) ∨
    (s=1 ∧ 2 ≤ p ∧ (p≥4 ∨ (p=3 ∧ q+r=4) ∨ (p=2 ∧ q+r=5))) ∨
    (p=1 ∧ s=1 ∧ q+r=6) := by
  omega

#print axioms rev_rev
#print axioms cut_complement
#print axioms speed_reversal
#print axioms lap_reversal
#print axioms disparity_reversal
#print axioms isolation_reversal
#print axioms move_reversal
#print axioms size_orientation
end Fresh.FourBlockReversal
