import Fresh.TwoGapPacketBand
import Fresh.ThreeBlockMiddlePartitions

/-! Rules: 1–4, 8–18. Structural containment for near-gap subjects only.
The native signed readings yield explicit D/e/f coefficients; physical
signed scale, drift and relabeling give packet unit|z|. Direct AP subjects
are not asserted to be packet subjects. Repeated absolute readings are
allowed; physical speed positivity and injectivity remain explicit.
[PROVISIONAL: covering] finite structural partition/label cases.
-/
open Classical
namespace Fresh.TrainFlankPacketJoins
open Fresh Fresh.OneMover Fresh.ThreeBlockPartitions
open Fresh.ThreeBlockMiddlePartitions Fresh.TwoGapPacketBand

-- STANDING: DEFINITION
def NearGapSubject (p q : ℕ) (k : Fin 8) : Prop :=
  (k : ℕ)=p-1 ∨ (k : ℕ)=p ∨ (k : ℕ)=p+q-1 ∨ (k : ℕ)=p+q

theorem shape_215 (c g h : ℝ) (hgpos : 0<g) (hhpos : 0<h)
    (k : Fin 8) (hnear : NearGapSubject 2 1 k) :
    ∀i : Fin 8, i≠k → ∃D e f : ℕ,
      D≤4 ∧ e≤1 ∧ f≤1 ∧ 1≤D+e+f ∧
      |speeds c g h 2 1 i-speeds c g h 2 1 k|=
        (D : ℝ)+(e : ℝ)*g+(f : ℝ)*h := by
  fin_cases k
  · norm_num [NearGapSubject] at hnear
  · intro i hik
    fin_cases i
    · refine ⟨1,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((1 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · exact False.elim (hik rfl)
    · refine ⟨0,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(0 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨0,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(0 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨1,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(1 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨2,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(2 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨3,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(3 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨4,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(4 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
  · intro i hik
    fin_cases i
    · refine ⟨1,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((1 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨0,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((0 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · exact False.elim (hik rfl)
    · refine ⟨0,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(0 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨1,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(1 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨2,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(2 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨3,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(3 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨4,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(4 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
  · intro i hik
    fin_cases i
    · refine ⟨1,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((1 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨0,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((0 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨0,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((0 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · exact False.elim (hik rfl)
    · refine ⟨1,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(1 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨2,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(2 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨3,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(3 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨4,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(4 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
  · norm_num [NearGapSubject] at hnear
  · norm_num [NearGapSubject] at hnear
  · norm_num [NearGapSubject] at hnear
  · norm_num [NearGapSubject] at hnear

theorem shape_224 (c g h : ℝ) (hgpos : 0<g) (hhpos : 0<h)
    (k : Fin 8) (hnear : NearGapSubject 2 2 k) :
    ∀i : Fin 8, i≠k → ∃D e f : ℕ,
      D≤4 ∧ e≤1 ∧ f≤1 ∧ 1≤D+e+f ∧
      |speeds c g h 2 2 i-speeds c g h 2 2 k|=
        (D : ℝ)+(e : ℝ)*g+(f : ℝ)*h := by
  fin_cases k
  · norm_num [NearGapSubject] at hnear
  · intro i hik
    fin_cases i
    · refine ⟨1,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((1 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · exact False.elim (hik rfl)
    · refine ⟨0,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(0 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨1,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(1 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨1,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(1 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨2,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(2 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨3,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(3 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨4,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(4 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
  · intro i hik
    fin_cases i
    · refine ⟨1,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((1 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨0,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((0 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · exact False.elim (hik rfl)
    · refine ⟨1,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(1 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨1,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(1 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨2,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(2 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨3,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(3 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨4,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(4 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
  · intro i hik
    fin_cases i
    · refine ⟨2,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((2 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨1,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((1 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨1,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((1 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · exact False.elim (hik rfl)
    · refine ⟨0,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(0 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨1,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(1 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨2,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(2 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨3,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(3 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
  · intro i hik
    fin_cases i
    · refine ⟨2,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((2 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨1,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((1 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨1,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((1 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨0,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((0 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · exact False.elim (hik rfl)
    · refine ⟨1,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(1 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨2,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(2 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨3,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(3 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
  · norm_num [NearGapSubject] at hnear
  · norm_num [NearGapSubject] at hnear
  · norm_num [NearGapSubject] at hnear

theorem shape_233 (c g h : ℝ) (hgpos : 0<g) (hhpos : 0<h)
    (k : Fin 8) (hnear : NearGapSubject 2 3 k) :
    ∀i : Fin 8, i≠k → ∃D e f : ℕ,
      D≤4 ∧ e≤1 ∧ f≤1 ∧ 1≤D+e+f ∧
      |speeds c g h 2 3 i-speeds c g h 2 3 k|=
        (D : ℝ)+(e : ℝ)*g+(f : ℝ)*h := by
  fin_cases k
  · norm_num [NearGapSubject] at hnear
  · intro i hik
    fin_cases i
    · refine ⟨1,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((1 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · exact False.elim (hik rfl)
    · refine ⟨0,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(0 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨1,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(1 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨2,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(2 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨2,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(2 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨3,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(3 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨4,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(4 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
  · intro i hik
    fin_cases i
    · refine ⟨1,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((1 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨0,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((0 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · exact False.elim (hik rfl)
    · refine ⟨1,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(1 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨2,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(2 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨2,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(2 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨3,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(3 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨4,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(4 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
  · norm_num [NearGapSubject] at hnear
  · intro i hik
    fin_cases i
    · refine ⟨3,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((3 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨2,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((2 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨2,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((2 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨1,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((1 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · exact False.elim (hik rfl)
    · refine ⟨0,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(0 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨1,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(1 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨2,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(2 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
  · intro i hik
    fin_cases i
    · refine ⟨3,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((3 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨2,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((2 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨2,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((2 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨1,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((1 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨0,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((0 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · exact False.elim (hik rfl)
    · refine ⟨1,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(1 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨2,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(2 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
  · norm_num [NearGapSubject] at hnear
  · norm_num [NearGapSubject] at hnear

theorem shape_242 (c g h : ℝ) (hgpos : 0<g) (hhpos : 0<h)
    (k : Fin 8) (hnear : NearGapSubject 2 4 k) :
    ∀i : Fin 8, i≠k → ∃D e f : ℕ,
      D≤4 ∧ e≤1 ∧ f≤1 ∧ 1≤D+e+f ∧
      |speeds c g h 2 4 i-speeds c g h 2 4 k|=
        (D : ℝ)+(e : ℝ)*g+(f : ℝ)*h := by
  fin_cases k
  · norm_num [NearGapSubject] at hnear
  · intro i hik
    fin_cases i
    · refine ⟨1,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((1 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · exact False.elim (hik rfl)
    · refine ⟨0,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(0 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨1,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(1 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨2,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(2 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨3,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(3 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨3,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(3 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨4,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(4 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
  · intro i hik
    fin_cases i
    · refine ⟨1,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((1 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨0,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((0 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · exact False.elim (hik rfl)
    · refine ⟨1,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(1 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨2,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(2 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨3,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(3 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨3,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(3 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨4,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(4 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
  · norm_num [NearGapSubject] at hnear
  · norm_num [NearGapSubject] at hnear
  · intro i hik
    fin_cases i
    · refine ⟨4,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((4 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨3,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((3 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨3,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((3 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨2,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((2 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨1,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((1 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · exact False.elim (hik rfl)
    · refine ⟨0,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(0 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨1,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(1 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
  · intro i hik
    fin_cases i
    · refine ⟨4,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((4 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨3,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((3 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨3,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((3 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨2,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((2 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨1,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((1 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨0,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((0 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · exact False.elim (hik rfl)
    · refine ⟨1,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(1 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
  · norm_num [NearGapSubject] at hnear

theorem shape_314 (c g h : ℝ) (hgpos : 0<g) (hhpos : 0<h)
    (k : Fin 8) (hnear : NearGapSubject 3 1 k) :
    ∀i : Fin 8, i≠k → ∃D e f : ℕ,
      D≤4 ∧ e≤1 ∧ f≤1 ∧ 1≤D+e+f ∧
      |speeds c g h 3 1 i-speeds c g h 3 1 k|=
        (D : ℝ)+(e : ℝ)*g+(f : ℝ)*h := by
  fin_cases k
  · norm_num [NearGapSubject] at hnear
  · norm_num [NearGapSubject] at hnear
  · intro i hik
    fin_cases i
    · refine ⟨2,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((2 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨1,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((1 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · exact False.elim (hik rfl)
    · refine ⟨0,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(0 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨0,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(0 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨1,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(1 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨2,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(2 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨3,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(3 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
  · intro i hik
    fin_cases i
    · refine ⟨2,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((2 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨1,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((1 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨0,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((0 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · exact False.elim (hik rfl)
    · refine ⟨0,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(0 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨1,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(1 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨2,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(2 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨3,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(3 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
  · intro i hik
    fin_cases i
    · refine ⟨2,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((2 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨1,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((1 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨0,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((0 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨0,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((0 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · exact False.elim (hik rfl)
    · refine ⟨1,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(1 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨2,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(2 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨3,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(3 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
  · norm_num [NearGapSubject] at hnear
  · norm_num [NearGapSubject] at hnear
  · norm_num [NearGapSubject] at hnear

theorem shape_323 (c g h : ℝ) (hgpos : 0<g) (hhpos : 0<h)
    (k : Fin 8) (hnear : NearGapSubject 3 2 k) :
    ∀i : Fin 8, i≠k → ∃D e f : ℕ,
      D≤4 ∧ e≤1 ∧ f≤1 ∧ 1≤D+e+f ∧
      |speeds c g h 3 2 i-speeds c g h 3 2 k|=
        (D : ℝ)+(e : ℝ)*g+(f : ℝ)*h := by
  fin_cases k
  · norm_num [NearGapSubject] at hnear
  · norm_num [NearGapSubject] at hnear
  · intro i hik
    fin_cases i
    · refine ⟨2,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((2 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨1,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((1 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · exact False.elim (hik rfl)
    · refine ⟨0,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(0 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨1,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(1 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨1,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(1 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨2,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(2 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨3,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(3 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
  · intro i hik
    fin_cases i
    · refine ⟨2,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((2 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨1,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((1 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨0,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((0 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · exact False.elim (hik rfl)
    · refine ⟨1,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(1 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨1,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(1 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨2,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(2 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨3,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(3 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
  · intro i hik
    fin_cases i
    · refine ⟨3,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((3 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨2,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((2 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨1,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((1 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨1,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((1 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · exact False.elim (hik rfl)
    · refine ⟨0,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(0 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨1,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(1 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨2,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(2 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
  · intro i hik
    fin_cases i
    · refine ⟨3,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((3 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨2,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((2 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨1,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((1 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨1,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((1 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨0,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((0 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · exact False.elim (hik rfl)
    · refine ⟨1,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(1 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨2,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(2 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
  · norm_num [NearGapSubject] at hnear
  · norm_num [NearGapSubject] at hnear

theorem shape_332 (c g h : ℝ) (hgpos : 0<g) (hhpos : 0<h)
    (k : Fin 8) (hnear : NearGapSubject 3 3 k) :
    ∀i : Fin 8, i≠k → ∃D e f : ℕ,
      D≤4 ∧ e≤1 ∧ f≤1 ∧ 1≤D+e+f ∧
      |speeds c g h 3 3 i-speeds c g h 3 3 k|=
        (D : ℝ)+(e : ℝ)*g+(f : ℝ)*h := by
  fin_cases k
  · norm_num [NearGapSubject] at hnear
  · norm_num [NearGapSubject] at hnear
  · intro i hik
    fin_cases i
    · refine ⟨2,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((2 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨1,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((1 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · exact False.elim (hik rfl)
    · refine ⟨0,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(0 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨1,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(1 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨2,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(2 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨2,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(2 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨3,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(3 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
  · intro i hik
    fin_cases i
    · refine ⟨2,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((2 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨1,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((1 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨0,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((0 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · exact False.elim (hik rfl)
    · refine ⟨1,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(1 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨2,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(2 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨2,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(2 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨3,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(3 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
  · norm_num [NearGapSubject] at hnear
  · intro i hik
    fin_cases i
    · refine ⟨4,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((4 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨3,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((3 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨2,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((2 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨2,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((2 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨1,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((1 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · exact False.elim (hik rfl)
    · refine ⟨0,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(0 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨1,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(1 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
  · intro i hik
    fin_cases i
    · refine ⟨4,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((4 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨3,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((3 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨2,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((2 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨2,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((2 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨1,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((1 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨0,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((0 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · exact False.elim (hik rfl)
    · refine ⟨1,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(1 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
  · norm_num [NearGapSubject] at hnear

theorem shape_413 (c g h : ℝ) (hgpos : 0<g) (hhpos : 0<h)
    (k : Fin 8) (hnear : NearGapSubject 4 1 k) :
    ∀i : Fin 8, i≠k → ∃D e f : ℕ,
      D≤4 ∧ e≤1 ∧ f≤1 ∧ 1≤D+e+f ∧
      |speeds c g h 4 1 i-speeds c g h 4 1 k|=
        (D : ℝ)+(e : ℝ)*g+(f : ℝ)*h := by
  fin_cases k
  · norm_num [NearGapSubject] at hnear
  · norm_num [NearGapSubject] at hnear
  · norm_num [NearGapSubject] at hnear
  · intro i hik
    fin_cases i
    · refine ⟨3,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((3 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨2,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((2 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨1,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((1 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · exact False.elim (hik rfl)
    · refine ⟨0,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(0 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨0,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(0 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨1,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(1 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨2,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(2 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
  · intro i hik
    fin_cases i
    · refine ⟨3,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((3 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨2,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((2 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨1,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((1 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨0,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((0 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · exact False.elim (hik rfl)
    · refine ⟨0,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(0 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨1,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(1 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨2,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(2 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
  · intro i hik
    fin_cases i
    · refine ⟨3,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((3 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨2,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((2 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨1,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((1 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨0,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((0 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨0,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((0 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · exact False.elim (hik rfl)
    · refine ⟨1,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(1 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨2,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(2 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
  · norm_num [NearGapSubject] at hnear
  · norm_num [NearGapSubject] at hnear

theorem shape_422 (c g h : ℝ) (hgpos : 0<g) (hhpos : 0<h)
    (k : Fin 8) (hnear : NearGapSubject 4 2 k) :
    ∀i : Fin 8, i≠k → ∃D e f : ℕ,
      D≤4 ∧ e≤1 ∧ f≤1 ∧ 1≤D+e+f ∧
      |speeds c g h 4 2 i-speeds c g h 4 2 k|=
        (D : ℝ)+(e : ℝ)*g+(f : ℝ)*h := by
  fin_cases k
  · norm_num [NearGapSubject] at hnear
  · norm_num [NearGapSubject] at hnear
  · norm_num [NearGapSubject] at hnear
  · intro i hik
    fin_cases i
    · refine ⟨3,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((3 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨2,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((2 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨1,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((1 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · exact False.elim (hik rfl)
    · refine ⟨0,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(0 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨1,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(1 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨1,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(1 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨2,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(2 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
  · intro i hik
    fin_cases i
    · refine ⟨3,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((3 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨2,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((2 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨1,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((1 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨0,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((0 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · exact False.elim (hik rfl)
    · refine ⟨1,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(1 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨1,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(1 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨2,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(2 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
  · intro i hik
    fin_cases i
    · refine ⟨4,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((4 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨3,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((3 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨2,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((2 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨1,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((1 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨1,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((1 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · exact False.elim (hik rfl)
    · refine ⟨0,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(0 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨1,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(1 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
  · intro i hik
    fin_cases i
    · refine ⟨4,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((4 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨3,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((3 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨2,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((2 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨1,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((1 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨1,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((1 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨0,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((0 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · exact False.elim (hik rfl)
    · refine ⟨1,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(1 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
  · norm_num [NearGapSubject] at hnear

theorem shape_512 (c g h : ℝ) (hgpos : 0<g) (hhpos : 0<h)
    (k : Fin 8) (hnear : NearGapSubject 5 1 k) :
    ∀i : Fin 8, i≠k → ∃D e f : ℕ,
      D≤4 ∧ e≤1 ∧ f≤1 ∧ 1≤D+e+f ∧
      |speeds c g h 5 1 i-speeds c g h 5 1 k|=
        (D : ℝ)+(e : ℝ)*g+(f : ℝ)*h := by
  fin_cases k
  · norm_num [NearGapSubject] at hnear
  · norm_num [NearGapSubject] at hnear
  · norm_num [NearGapSubject] at hnear
  · norm_num [NearGapSubject] at hnear
  · intro i hik
    fin_cases i
    · refine ⟨4,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((4 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨3,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((3 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨2,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((2 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨1,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((1 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · exact False.elim (hik rfl)
    · refine ⟨0,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(0 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨0,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(0 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨1,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(1 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
  · intro i hik
    fin_cases i
    · refine ⟨4,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((4 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨3,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((3 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨2,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((2 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨1,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((1 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨0,1,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((0 : ℝ)+(1 : ℝ)*g+(0 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · exact False.elim (hik rfl)
    · refine ⟨0,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(0 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
    · refine ⟨1,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(1 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
  · intro i hik
    fin_cases i
    · refine ⟨4,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((4 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨3,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((3 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨2,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((2 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨1,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((1 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨0,1,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((0 : ℝ)+(1 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · refine ⟨0,0,1,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |-((0 : ℝ)+(0 : ℝ)*g+(1 : ℝ)*h)| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := by rw [abs_neg]; exact abs_of_pos (by positivity)
    · exact False.elim (hik rfl)
    · refine ⟨1,0,0,by omega,by omega,by omega,by omega,?_⟩
      norm_num only [Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat]
      calc
        _ = |(1 : ℝ)+(0 : ℝ)*g+(0 : ℝ)*h| := by
          congr 1
          norm_num [speeds]
          <;> ring
        _ = _ := abs_of_pos (by positivity)
  · norm_num [NearGapSubject] at hnear

theorem near_shape (c g h : ℝ) (p q : ℕ) (hp : 2≤p) (hq : 1≤q)
    (hpq : p+q≤6) (hgpos : 0<g) (hhpos : 0<h)
    (k : Fin 8) (hnear : NearGapSubject p q k) :
    ∀i : Fin 8, i≠k → ∃D e f : ℕ,
      D≤4 ∧ e≤1 ∧ f≤1 ∧ 1≤D+e+f ∧
      |speeds c g h p q i-speeds c g h p q k|=
        (D : ℝ)+(e : ℝ)*g+(f : ℝ)*h := by
  have hp5 : p≤5 := by omega
  have hq4 : q≤4 := by omega
  interval_cases p <;> interval_cases q
  · exact shape_215 c g h hgpos hhpos k hnear
  · exact shape_224 c g h hgpos hhpos k hnear
  · exact shape_233 c g h hgpos hhpos k hnear
  · exact shape_242 c g h hgpos hhpos k hnear
  · exact shape_314 c g h hgpos hhpos k hnear
  · exact shape_323 c g h hgpos hhpos k hnear
  · exact shape_332 c g h hgpos hhpos k hnear
  · omega
  · exact shape_413 c g h hgpos hhpos k hnear
  · exact shape_422 c g h hgpos hhpos k hnear
  · omega
  · omega
  · exact shape_512 c g h hgpos hhpos k hnear
  · omega
  · omega
  · omega

/-- Explicit physical join: the signed affine factor becomes positive packet
unit|z|. No total-gap bound is needed for these carried subjects. -/
theorem affine_near_into_packet {V : Fin 8→ℝ}
    (hpos : ∀i,0<V i) (hinj : Function.Injective V)
    (c g h B z : ℝ) (p q : ℕ) (σ : Equiv.Perm (Fin 8))
    (hp : 2≤p) (hq : 1≤q) (hpq : p+q≤6) (m a b : ℤ)
    (hgpos : 0<g) (hhpos : 0<h) (hm : 1≤ m)
    (hg : 8*(a : ℝ)+1≤(8*(m : ℝ)+1)*g)
    (hh : 8*(b : ℝ)+1≤(8*(m : ℝ)+1)*h)
    (hsum : (8*(m : ℝ)+1)*(g+h)≤8*((a : ℝ)+(b : ℝ))+3)
    (hz : z≠0) (hV : V=(fun i=>B+z*speeds c g h p q (σ i)))
    (k : Fin 8) (hnear : NearGapSubject p q (σ k)) : TwoGapPacketClass V k := by
  refine ⟨hpos,hinj,|z|,g,h,m,a,b,abs_pos.mpr hz,hgpos,hhpos,hm,hg,hh,hsum,?_⟩
  intro i hik
  have hσ : σ i≠σ k := by intro he; exact hik (σ.injective he)
  obtain ⟨D,e,f,hD,he,hf,hne,hshape⟩ := near_shape c g h p q hp hq hpq hgpos hhpos (σ k) hnear (σ i) hσ
  refine ⟨D,e,f,hD,he,hf,hne,?_⟩
  have hd : V i-V k=z*(speeds c g h p q (σ i)-speeds c g h p q (σ k)) := by
    rw [hV]
    dsimp
    ring
  rw [hd,abs_mul,hshape]

/-- The existing physical class supplies a labeling whose near subjects
are packet subjects. Direct AP subjects are outside this assertion. -/
theorem middle_near_into_packet {V : Fin 8→ℝ}
    (h : ThreeBlockMiddlePartitionsClass V) :
    ∃ (p q : ℕ) (σ : Equiv.Perm (Fin 8)),
      2≤p ∧ 1≤q ∧ p+q≤6 ∧ ∀k : Fin 8,
        NearGapSubject p q (σ k) → TwoGapPacketClass V k := by
  obtain ⟨hpos,hinj,c,g,h,B,z,p,q,m,a,b,σ,hp,hq,hpq,hm,hgpos,hhpos,hsmall,hg,hh,hsum,hz,hV⟩ := h
  refine ⟨p,q,σ,hp,hq,hpq,fun k hnear=>?_⟩
  exact affine_near_into_packet hpos hinj c g h B z p q σ hp hq hpq m a b hgpos hhpos hm hg hh hsum hz hV k hnear

#print axioms shape_215
#print axioms shape_224
#print axioms shape_233
#print axioms shape_242
#print axioms shape_314
#print axioms shape_323
#print axioms shape_332
#print axioms shape_413
#print axioms shape_422
#print axioms shape_512
#print axioms near_shape
#print axioms affine_near_into_packet
#print axioms middle_near_into_packet
set_option pp.fullNames true in
#print axioms Fresh.TwoGapPacketBand.clear_packet
set_option pp.fullNames true in
#print axioms Fresh.TwoGapPacketBand.twoGapPacket_isolation
end Fresh.TrainFlankPacketJoins
