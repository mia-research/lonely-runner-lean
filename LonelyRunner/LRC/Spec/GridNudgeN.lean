import LonelyRunner.LRC.Spec.MirrorCentreN

/-!
# The grid nudge: one blocked reading, pushed out by its own deviation

2026-09-26 (running log E85–E86).  Owner: *"any speed is just AP/grid and a deviation that is forced by `d_min`."*

At an instant `t₀` where every reading of the subject sits exactly on an eighth, `w j · t₀ = m j / 8` (every grid and
every progression at each of its `φ(8)` instants; for whole-number readings, every instant `a/8`), the readings with
`m j ≢ 0 (mod 8)` are clear and the ones with `m j ≡ 0` sit in the subject's slot.  When the only blocked reading is the
largest one, `w p`, a deviation of the instant by `±1/(8·w p)` moves it exactly to the slot edge and moves every other
reading by less than `1/8`:

* **forward** (`grid_nudge_forward`): if every other reading sits on a residue `1 … 6`, the subject is isolated at
  `t₀ + 1/(8·w p)` (a reading on residue `7` would be pushed into the slot);
* **backward** (`grid_nudge_backward`): if every other reading sits on `2 … 7`, it is isolated at `t₀ − 1/(8·w p)`.

The two fail together exactly when both edges `1` and `7` are occupied: the grid's pinned pair.  Everything here is
proved; no `sorry`, no `native_decide`.
-/

namespace LRC.GridNudge

open LRC.MirrorCentre

/-- A position `m/8 + δ` with `m mod 8 = r` and `r/8 + δ ∈ [1/8, 7/8]` is clear. -/
theorem clear_of_eighth {x δ : ℝ} (m : ℤ) (hx : x = (m : ℝ) / 8 + δ)
    (h1 : (1 : ℝ) / 8 ≤ ((m % 8 : ℤ) : ℝ) / 8 + δ) (h2 : ((m % 8 : ℤ) : ℝ) / 8 + δ ≤ 7 / 8) :
    (8 : ℝ)⁻¹ ≤ circDist x := by
  have hm : (m : ℝ) = 8 * ((m / 8 : ℤ) : ℝ) + ((m % 8 : ℤ) : ℝ) := by
    exact_mod_cast (Int.mul_ediv_add_emod m 8).symm
  rw [show (8 : ℝ)⁻¹ = 1 / 8 by norm_num]
  exact circDist_ge_of_window (m := m / 8) (by rw [hx, hm]; linarith) (by rw [hx, hm]; linarith) (by norm_num)

/-- **The forward nudge.** -/
theorem grid_nudge_forward {ι : Type*} {s : Finset ι} {w : ι → ℝ} {m : ι → ℤ} {t₀ : ℝ} {p : ι}
    (hpos : ∀ j ∈ s, 0 < w j) (hp : p ∈ s) (hmax : ∀ j ∈ s, w j ≤ w p)
    (hgrid : ∀ j ∈ s, w j * t₀ = (m j : ℝ) / 8) (hp8 : m p % 8 = 0)
    (hothers : ∀ j ∈ s, j ≠ p → 1 ≤ m j % 8 ∧ m j % 8 ≤ 6) :
    ∀ j ∈ s, (8 : ℝ)⁻¹ ≤ circDist (w j * (t₀ + 1 / (8 * w p))) := by
  have hwp := hpos p hp
  intro j hj
  have hwj := hpos j hj
  have hsplit : w j * (t₀ + 1 / (8 * w p)) = (m j : ℝ) / 8 + w j / (8 * w p) := by
    rw [mul_add, hgrid j hj]; field_simp
  have hδ0 : 0 < w j / (8 * w p) := by positivity
  have hδ1 : w j / (8 * w p) ≤ 1 / 8 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith [hmax j hj]
  by_cases hjp : j = p
  · subst hjp
    have hr : ((m j % 8 : ℤ) : ℝ) = 0 := by exact_mod_cast hp8
    have hδ : w j / (8 * w j) = 1 / 8 := by field_simp
    refine clear_of_eighth (m j) hsplit ?_ ?_ <;> rw [hr, hδ] <;> norm_num
  · obtain ⟨h1, h2⟩ := hothers j hj hjp
    have r1 : (1 : ℝ) ≤ ((m j % 8 : ℤ) : ℝ) := by exact_mod_cast h1
    have r2 : ((m j % 8 : ℤ) : ℝ) ≤ 6 := by exact_mod_cast h2
    refine clear_of_eighth (m j) hsplit ?_ ?_ <;> linarith

/-- **The backward nudge.** -/
theorem grid_nudge_backward {ι : Type*} {s : Finset ι} {w : ι → ℝ} {m : ι → ℤ} {t₀ : ℝ} {p : ι}
    (hpos : ∀ j ∈ s, 0 < w j) (hp : p ∈ s) (hmax : ∀ j ∈ s, w j ≤ w p)
    (hgrid : ∀ j ∈ s, w j * t₀ = (m j : ℝ) / 8) (hp8 : m p % 8 = 0)
    (hothers : ∀ j ∈ s, j ≠ p → 2 ≤ m j % 8 ∧ m j % 8 ≤ 7) :
    ∀ j ∈ s, (8 : ℝ)⁻¹ ≤ circDist (w j * (t₀ - 1 / (8 * w p))) := by
  have hwp := hpos p hp
  intro j hj
  have hwj := hpos j hj
  have hsplit : w j * (t₀ - 1 / (8 * w p)) = (m j : ℝ) / 8 + -(w j / (8 * w p)) := by
    rw [mul_sub, hgrid j hj]; field_simp; ring
  have hδ0 : 0 < w j / (8 * w p) := by positivity
  have hδ1 : w j / (8 * w p) ≤ 1 / 8 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith [hmax j hj]
  by_cases hjp : j = p
  · subst hjp
    -- `m p / 8 - 1/8` with `m p ≡ 0`: the edge `7/8` of the lap below
    have hm : (m j : ℝ) = 8 * ((m j / 8 - 1 : ℤ) : ℝ) + 8 := by
      have hz : m j = 8 * (m j / 8) := by omega
      have hr : (m j : ℝ) = 8 * ((m j / 8 : ℤ) : ℝ) := by exact_mod_cast hz
      push_cast; linarith
    have hδ : w j / (8 * w j) = 1 / 8 := by field_simp
    rw [show (8 : ℝ)⁻¹ = 1 / 8 by norm_num]
    exact circDist_ge_of_window (m := m j / 8 - 1) (by rw [hsplit, hm, hδ]; linarith)
      (by rw [hsplit, hm, hδ]; linarith) (by norm_num)
  · obtain ⟨h1, h2⟩ := hothers j hj hjp
    have r1 : (2 : ℝ) ≤ ((m j % 8 : ℤ) : ℝ) := by exact_mod_cast h1
    have r2 : ((m j % 8 : ℤ) : ℝ) ≤ 7 := by exact_mod_cast h2
    refine clear_of_eighth (m j) hsplit ?_ ?_ <;> linarith

/-- **Whole-number readings.**  At `t₀ = 1/8` every reading `d` sits at `d/8`.  If the largest reading `d₀` is the only
multiple of 8 and no reading is `7 (mod 8)`, the subject is isolated at `(1/8)(1 + 1/d₀)`. -/
theorem nat_nudge_forward {T : Finset ℕ} {d₀ : ℕ} (hpos : ∀ d ∈ T, 0 < d) (h0 : d₀ ∈ T) (hmax : ∀ d ∈ T, d ≤ d₀)
    (h8 : d₀ % 8 = 0) (hothers : ∀ d ∈ T, d ≠ d₀ → 1 ≤ d % 8 ∧ d % 8 ≤ 6) :
    ∀ d ∈ T, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * (1 / 8 + 1 / (8 * (d₀ : ℝ)))) := by
  refine grid_nudge_forward (s := T) (w := fun d => (d : ℝ)) (m := fun d => (d : ℤ)) (t₀ := 1 / 8) (p := d₀)
    (fun d hd => by dsimp only; exact_mod_cast hpos d hd) h0 (fun d hd => by dsimp only; exact_mod_cast hmax d hd)
    (fun d _ => by push_cast; ring) (by dsimp only; omega) ?_
  intro d hd hne
  obtain ⟨a, b⟩ := hothers d hd hne
  dsimp only
  constructor <;> omega

end LRC.GridNudge
