import LonelyRunner.LRC.Spec.OrderSixN

/-!
# Neighbouring boxes: one stretch cut by one runner (n6_native, E32)

Runner `r` (speed `d > 0`) is clear on its lap-`k` band `[(6k+1)/(6d), (6k+5)/(6d)]` and in the way until
`(6k+7)/(6d)`, where its lap-`(k+1)` band starts. `J = [J₀, J₁]` is the stretch on which the other runners
are all clear. The box with `r` on lap `k` is lonely on the piece `[max J₀ e_k, min J₁ x_k]`; its neighbour,
with `r` on lap `k+1`, on `[max J₀ e_{k+1}, min J₁ x_{k+1}]`.

* `neighbours_open_iff` — both pieces have positive length iff `J₀ < x_k` and `e_{k+1} < J₁`: `J` straddles
  `r`'s blocked window.
* `stretch_long` — then `J₁ - J₀ > 1/(3d)`.
* `takeover_open` — if `J₀ ≤ x_k` (the lap-`k` piece may have shrunk to a point) and `e_{k+1} < J₁`, the
  neighbour's piece has positive length.
* `band_clear`, `piece_lonely` — every instant of a piece is lonely for `r` and the others.
-/

namespace N6Native

/-- Entry and exit of runner `d` on lap `k`. -/
noncomputable def ent (d : ℝ) (k : ℤ) : ℝ := (6 * k + 1) / (6 * d)
noncomputable def ext (d : ℝ) (k : ℤ) : ℝ := (6 * k + 5) / (6 * d)

theorem ent_lt_ext {d : ℝ} (hd : 0 < d) (k : ℤ) : ent d k < ext d k := by
  unfold ent ext; apply div_lt_div_of_pos_right _ (by positivity); linarith

theorem ext_lt_ent_succ {d : ℝ} (hd : 0 < d) (k : ℤ) : ext d k < ent d (k + 1) := by
  unfold ent ext; apply div_lt_div_of_pos_right _ (by positivity); push_cast; linarith

theorem ext_lt_ext_succ {d : ℝ} (hd : 0 < d) (k : ℤ) : ext d k < ext d (k + 1) := by
  unfold ext; apply div_lt_div_of_pos_right _ (by positivity); push_cast; linarith

theorem ent_lt_ent_succ {d : ℝ} (hd : 0 < d) (k : ℤ) : ent d k < ent d (k + 1) := by
  unfold ent; apply div_lt_div_of_pos_right _ (by positivity); push_cast; linarith

/-- The piece of `J` on which runner `d` reads in its lap-`k` band has positive length. -/
def PieceOpen (J₀ J₁ d : ℝ) (k : ℤ) : Prop := max J₀ (ent d k) < min J₁ (ext d k)

/-- **The cut.** Both neighbouring pieces are open iff `J` straddles the blocked window
`[x_k, e_{k+1}]`. -/
theorem neighbours_open_iff {J₀ J₁ d : ℝ} (hd : 0 < d) (k : ℤ) :
    (PieceOpen J₀ J₁ d k ∧ PieceOpen J₀ J₁ d (k + 1)) ↔ (J₀ < ext d k ∧ ent d (k + 1) < J₁) := by
  have a := ent_lt_ext hd k
  have b := ext_lt_ent_succ hd k
  have c := ent_lt_ext hd (k + 1)
  unfold PieceOpen
  simp only [max_lt_iff, lt_min_iff]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3, h4⟩, ⟨h5, h6⟩, h7, h8⟩
    exact ⟨h3, h6⟩
  · rintro ⟨h1, h2⟩
    have e := ext_lt_ext_succ hd k
    exact ⟨⟨⟨by linarith, by linarith⟩, h1, a⟩, ⟨by linarith, h2⟩, by linarith, c⟩

/-- **The stretch is longer than the blocked window**, a third of `r`'s lap. -/
theorem stretch_long {J₀ J₁ d : ℝ} (hd : 0 < d) (k : ℤ)
    (h : PieceOpen J₀ J₁ d k ∧ PieceOpen J₀ J₁ d (k + 1)) : 1 / (3 * d) < J₁ - J₀ := by
  obtain ⟨h1, h2⟩ := (neighbours_open_iff hd k).mp h
  have hw : ent d (k + 1) - ext d k = 1 / (3 * d) := by
    unfold ent ext; push_cast; field_simp; ring
  linarith

/-- **The takeover.** However far the lap-`k` piece has shrunk (`J₀ ≤ x_k`), the neighbour's piece is
open as long as `J` reaches past `r`'s next entry. -/
theorem takeover_open {J₀ J₁ d : ℝ} (hd : 0 < d) (k : ℤ) (h0 : J₀ ≤ ext d k)
    (h1 : ent d (k + 1) < J₁) : PieceOpen J₀ J₁ d (k + 1) := by
  have b := ext_lt_ent_succ hd k
  have c := ent_lt_ext hd (k + 1)
  have e := ext_lt_ext_succ hd k
  unfold PieceOpen
  simp only [max_lt_iff, lt_min_iff]
  exact ⟨⟨by linarith, h1⟩, by linarith, c⟩

/-- A runner reading in its lap-`k` band is clear. -/
theorem band_clear {d t : ℝ} (hd : 0 < d) {k : ℤ} (h1 : ent d k ≤ t) (h2 : t ≤ ext d k) :
    (6 : ℝ)⁻¹ ≤ circDist (d * t) := by
  unfold ent at h1; unfold ext at h2
  rw [div_le_iff₀ (by positivity)] at h1
  rw [le_div_iff₀ (by positivity)] at h2
  have hfr : Int.fract (d * t) = d * t - k := by
    rw [Int.fract_eq_iff]; exact ⟨by nlinarith, by nlinarith, k, by ring⟩
  unfold circDist; rw [hfr]
  exact le_min (by nlinarith) (by nlinarith)

/-- **Every instant of a piece is lonely**: `r` reads in its band, the others are clear on `J`. -/
theorem piece_lonely {ι : Type*} (others : Finset ι) (v : ι → ℝ) {J₀ J₁ d t : ℝ} (hd : 0 < d) {k : ℤ}
    (hJ : ∀ s, J₀ ≤ s → s ≤ J₁ → ∀ i ∈ others, (6 : ℝ)⁻¹ ≤ circDist (v i * s))
    (ht0 : max J₀ (ent d k) ≤ t) (ht1 : t ≤ min J₁ (ext d k)) :
    (6 : ℝ)⁻¹ ≤ circDist (d * t) ∧ ∀ i ∈ others, (6 : ℝ)⁻¹ ≤ circDist (v i * t) :=
  ⟨band_clear hd (le_of_max_le_right ht0) (le_of_le_min_right ht1),
    hJ t (le_of_max_le_left ht0) (le_of_le_min_left ht1)⟩

end N6Native

#print axioms N6Native.neighbours_open_iff
#print axioms N6Native.stretch_long
#print axioms N6Native.takeover_open
#print axioms N6Native.band_clear
#print axioms N6Native.piece_lonely
