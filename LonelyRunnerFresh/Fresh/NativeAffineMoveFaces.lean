import Fresh.NativeCoalescedCaptureRelay

/-!
An exact move between named openings is preserved by coordinated
interpolation when the two endpoint moves have a common entry label
for each reading. The proof interpolates the phase, exit-order and
chronology inequalities after clearing positive denominators.
-/

namespace Fresh.NativeAffineMoveFaces

open Fresh Cascade NativeEntryLabels NativeReturnCapture
  NativeOneReaderDeformation NativeCoalescedCaptureRelay

/-- Coordinatewise interpolation of positive reading vectors. -/
def blend {ι : Type*} (x y : ι → ℝ) (q : ℝ) (i : ι) : ℝ :=
  (1 - q) * x i + q * y i

private theorem blend_pos {ι : Type*} {x y : ι → ℝ} {q : ℝ}
    (hq : 0 ≤ q) (hq' : q ≤ 1) {i : ι} (hx : 0 < x i) (hy : 0 < y i) :
    0 < blend x y q i := by
  unfold blend
  by_cases h : q = 0
  · simpa [h] using hx
  · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr hq') hx.le)
      (mul_pos (lt_of_le_of_ne hq (Ne.symm h)) hy)

private theorem blend_le {ι : Type*} {x y : ι → ℝ} {q A B : ℝ}
    (hq : 0 ≤ q) (hq' : q ≤ 1) {i j : ι}
    (hx : A * x i ≤ B * x j) (hy : A * y i ≤ B * y j) :
    A * blend x y q i ≤ B * blend x y q j := by
  unfold blend
  nlinarith only [mul_le_mul_of_nonneg_left hx (sub_nonneg.mpr hq'),
    mul_le_mul_of_nonneg_left hy hq]

private theorem blend_lt {ι : Type*} {x y : ι → ℝ} {q A B : ℝ}
    (hq : 0 ≤ q) (hq' : q ≤ 1) {i j : ι}
    (hx : A * x i < B * x j) (hy : A * y i < B * y j) :
    A * blend x y q i < B * blend x y q j := by
  unfold blend
  by_cases h : q = 0
  · simpa [h] using hx
  · nlinarith only [mul_le_mul_of_nonneg_left hx.le (sub_nonneg.mpr hq'),
      mul_lt_mul_of_pos_left hy (lt_of_le_of_ne hq (Ne.symm h))]

private theorem positive_image {ι : Type*} [Fintype ι] {x : ι → ℝ}
    (hx : ∀ i, 0 < x i) : ∀ r ∈ Finset.univ.image x, 0 < r := by
  classical
  intro r hr
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
  exact hx i

/-- A move is determined by the actual entry labels at its origin and
the cross-multiplied opening bounds. Clear readings and losing captures
use the same weak opening bound. -/
theorem move_of_faces {ι : Type*} [Fintype ι] (x : ι → ℝ)
    (hx : ∀ i, 0 < x i) {a b : ι} {A : ℝ} (J : ι → ℤ)
    (htime : A * x b ≤ ((J b : ℝ) + 1 / 8) * x a)
    (hphase : ∀ i, ((J i : ℝ) - 1 / 8) * x a < A * x i ∧
      A * x i ≤ ((J i : ℝ) + 7 / 8) * x a)
    (horder : ∀ i, ((J i : ℝ) + 1 / 8) * x b ≤ ((J b : ℝ) + 1 / 8) * x i) :
    IsMove (Finset.univ.image x) (A / x a) (((J b : ℝ) + 1 / 8) / x b) := by
  classical
  have hlabel (i : ι) : label (x i * (A / x a)) = J i := by
    apply (entry_iff_label _ _ _).1
    apply (entry_interval _ _ _).2
    rw [← mul_div_assoc, lt_div_iff₀ (hx a), div_le_iff₀ (hx a), mul_comm (x i) A]
    exact hphase i
  apply move_of_opening_record (positive_image hx) _ _
    ((div_le_div_iff₀ (hx a) (hx b)).2 htime)
  · intro r hr
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
    unfold labelledOpening FastestCaptureRetention.opening
    rw [hlabel i, div_le_div_iff₀ (hx i) (hx b)]
    exact horder i
  · refine ⟨x b, Finset.mem_image_of_mem x (Finset.mem_univ b), ?_⟩
    simp [labelledOpening, FastestCaptureRetention.opening, hlabel b]

/-- Matching labelled moves at two endpoint arrangements determine the
move on the whole segment. In particular, a losing reading may change
from clear to captured while its entry label stays fixed. -/
theorem interpolate_move {ι : Type*} [Fintype ι] (x y : ι → ℝ)
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    {q A : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1) {a b : ι} (J : ι → ℤ)
    (hlabelx : ∀ i, label (x i * (A / x a)) = J i)
    (hlabely : ∀ i, label (y i * (A / y a)) = J i)
    (hmx : IsMove (Finset.univ.image x) (A / x a) (((J b : ℝ) + 1 / 8) / x b))
    (hmy : IsMove (Finset.univ.image y) (A / y a) (((J b : ℝ) + 1 / 8) / y b)) :
    IsMove (Finset.univ.image (blend x y q)) (A / blend x y q a)
      (((J b : ℝ) + 1 / 8) / blend x y q b) := by
  classical
  have phase {z : ι → ℝ} (hz : ∀ i, 0 < z i)
      (hl : ∀ i, label (z i * (A / z a)) = J i) (i : ι) :
      ((J i : ℝ) - 1 / 8) * z a < A * z i ∧
        A * z i ≤ ((J i : ℝ) + 7 / 8) * z a := by
    have h := (entry_interval _ _ _).1 ((entry_iff_label _ _ _).2 (hl i))
    rw [← mul_div_assoc, lt_div_iff₀ (hz a), div_le_iff₀ (hz a), mul_comm (z i) A] at h
    exact h
  have order {z : ι → ℝ} (hz : ∀ i, 0 < z i)
      (hl : ∀ i, label (z i * (A / z a)) = J i)
      (hm : IsMove (Finset.univ.image z) (A / z a) (((J b : ℝ) + 1 / 8) / z b))
      (i : ι) : ((J i : ℝ) + 1 / 8) * z b ≤ ((J b : ℝ) + 1 / 8) * z i := by
    have h := move_passes_entry_opening (positive_image hz) _ _ _ hm
      (Finset.mem_image_of_mem z (Finset.mem_univ i))
    rw [hl i] at h
    have h' := mul_le_mul_of_nonneg_right h (hz b).le
    rw [mul_assoc, div_mul_cancel₀ _ (hz b).ne', mul_comm (z i)] at h'
    exact h'
  apply move_of_faces _ (fun i => blend_pos hq hq' (hx i) (hy i)) J
  · exact blend_le hq hq'
      ((div_le_div_iff₀ (hx a) (hx b)).1 (le_of_isMove (positive_image hx) hmx))
      ((div_le_div_iff₀ (hy a) (hy b)).1 (le_of_isMove (positive_image hy) hmy))
  · intro i
    exact ⟨blend_lt hq hq' (phase hx hlabelx i).1 (phase hy hlabely i).1,
      blend_le hq hq' (phase hx hlabelx i).2 (phase hy hlabely i).2⟩
  · intro i
    exact blend_le hq hq' (order hx hlabelx hmx i) (order hy hlabely hmy i)

/-- An entry equality can occur at an endpoint of an open parameter
cell. The lower phase face need only be strict at one endpoint. The
actual boundary move is checked with its own native labels. -/
theorem interpolate_open_faces {ι : Type*} [Fintype ι] (x y : ι → ℝ)
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i)
    {q A : ℝ} (hq : 0 < q) (hq' : q < 1) {a b : ι} (J : ι → ℤ)
    (htime_x : A * x b ≤ ((J b : ℝ) + 1 / 8) * x a)
    (htime_y : A * y b ≤ ((J b : ℝ) + 1 / 8) * y a)
    (hphase : ∀ i, ((J i : ℝ) - 1 / 8) * x a ≤ A * x i ∧
      ((J i : ℝ) - 1 / 8) * y a ≤ A * y i ∧
      (((J i : ℝ) - 1 / 8) * x a < A * x i ∨
        ((J i : ℝ) - 1 / 8) * y a < A * y i) ∧
      A * x i ≤ ((J i : ℝ) + 7 / 8) * x a ∧
      A * y i ≤ ((J i : ℝ) + 7 / 8) * y a)
    (horder_x : ∀ i, ((J i : ℝ) + 1 / 8) * x b ≤ ((J b : ℝ) + 1 / 8) * x i)
    (horder_y : ∀ i, ((J i : ℝ) + 1 / 8) * y b ≤ ((J b : ℝ) + 1 / 8) * y i) :
    IsMove (Finset.univ.image (blend x y q)) (A / blend x y q a)
      (((J b : ℝ) + 1 / 8) / blend x y q b) := by
  apply move_of_faces _ (fun i => blend_pos hq.le hq'.le (hx i) (hy i)) J
  · exact blend_le hq.le hq'.le htime_x htime_y
  · intro i
    obtain ⟨hlx, hly, hstrict, hux, huy⟩ := hphase i
    refine ⟨?_, blend_le hq.le hq'.le hux huy⟩
    unfold blend
    rcases hstrict with h | h
    · nlinarith only [mul_lt_mul_of_pos_left h (sub_pos.mpr hq'),
        mul_le_mul_of_nonneg_left hly hq.le]
    · nlinarith only [mul_le_mul_of_nonneg_left hlx (sub_nonneg.mpr hq'.le),
        mul_lt_mul_of_pos_left h hq]
  · intro i
    exact blend_le hq.le hq'.le (horder_x i) (horder_y i)

/-- A whole proposed prefix follows from starting-reading inequalities.
Each row names the previous and next setter and the entry labels at
the previous opening. The labels and prefix length are unrestricted. -/
theorem prefix_of_faces {ι : Type*} [Fintype ι] (x : ι → ℝ)
    (hx : ∀ i, 0 < x i) (a : ℕ → ι) (A : ℕ → ℝ) (J : ℕ → ι → ℤ)
    (N : ℕ)
    (hanchor : ∀ n < N, A (n + 1) = (J n (a (n + 1)) : ℝ) + 1 / 8)
    (htime : ∀ n < N, A n * x (a (n + 1)) ≤ A (n + 1) * x (a n))
    (hphase : ∀ n < N, ∀ i, ((J n i : ℝ) - 1 / 8) * x (a n) < A n * x i ∧
      A n * x i ≤ ((J n i : ℝ) + 7 / 8) * x (a n))
    (horder : ∀ n < N, ∀ i, ((J n i : ℝ) + 1 / 8) * x (a (n + 1)) ≤
      A (n + 1) * x i) :
    ∀ n ≤ N, cascadeSeq (Finset.univ.image x) (A 0 / x (a 0)) n = A n / x (a n) := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    have hlt : n < N := by omega
    have hnext : IsMove (Finset.univ.image x) (A n / x (a n))
        (A (n + 1) / x (a (n + 1))) := by
      rw [hanchor n hlt]
      exact move_of_faces x hx (J n)
        (hanchor n hlt ▸ htime n hlt) (hphase n hlt)
        (hanchor n hlt ▸ horder n hlt)
    have hstep := cascadeSeq_isMove (Finset.univ.image x) (A 0 / x (a 0)) n
    rw [ih hlt.le] at hstep
    exact isMove_unique hstep hnext

/-- Physical positivity and strict rank order persist across the blend. -/
theorem ordered_blend {v w : Fin 8 → ℝ} (hv : IsOrderedArrangement v)
    (hw : IsOrderedArrangement w) {q : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1) :
    IsOrderedArrangement (blend v w q) := by
  refine ⟨fun i => blend_pos hq hq' (hv.1 i) (hw.1 i), ?_⟩
  intro i j hij
  simpa only [one_mul] using blend_lt hq hq' (A := 1) (B := 1)
    (by simpa using hv.2 hij) (by simpa using hw.2 hij)

/-- Along an ordered physical deformation, the disparity of any fixed
moving subject is the affine blend of its endpoint disparities. -/
theorem disparity_blend {v w : Fin 8 → ℝ} (hv : IsOrderedArrangement v)
    (hw : IsOrderedArrangement w) {q : ℝ} (hq : 0 ≤ q) (hq' : q ≤ 1)
    (i k : Fin 8) :
    |blend v w q i - blend v w q k| =
      blend (fun j => |v j - v k|) (fun j => |w j - w k|) q i := by
  rcases le_total i k with h | h
  · have hv' := sub_nonpos.mpr (hv.2.monotone h)
    have hw' := sub_nonpos.mpr (hw.2.monotone h)
    have hb : blend v w q i ≤ blend v w q k := by
      simpa only [one_mul] using blend_le hq hq' (A := 1) (B := 1)
        (by simpa using hv.2.monotone h) (by simpa using hw.2.monotone h)
    rw [abs_of_nonpos (sub_nonpos.mpr hb)]
    simp only [blend, abs_of_nonpos hv', abs_of_nonpos hw']
    ring
  · have hv' := sub_nonneg.mpr (hv.2.monotone h)
    have hw' := sub_nonneg.mpr (hw.2.monotone h)
    have hb : blend v w q k ≤ blend v w q i := by
      simpa only [one_mul] using blend_le hq hq' (A := 1) (B := 1)
        (by simpa using hv.2.monotone h) (by simpa using hw.2.monotone h)
    rw [abs_of_nonneg (sub_nonneg.mpr hb)]
    simp only [blend, abs_of_nonneg hv', abs_of_nonneg hw']
    ring

#print axioms blend_pos
#print axioms blend_le
#print axioms blend_lt
#print axioms positive_image
#print axioms move_of_faces
#print axioms interpolate_move
#print axioms interpolate_open_faces
#print axioms prefix_of_faces
#print axioms ordered_blend
#print axioms disparity_blend

end Fresh.NativeAffineMoveFaces
