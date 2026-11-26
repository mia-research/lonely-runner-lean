import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.Cascade
import Fresh.OneMoverA
import Fresh.CascadeLanding

/-!
# The cascade's landing for a frozen set `S` of integer readings and one mover: shared lemmas (general `S`)

Written 2026-10-22.  New file.  `CascadeLanding.lean` treats the frozen sets `{1..7} \ {m}`; this file lets `S` be any finite
set of positive integers (the frozen disparities seen by any subject of the AP once one runner is the mover), and starts the
cascade at `1/(8a)` for `a ∈ S` the least reading.  The one-piece facts (`Holds`, `holds_clear`, `not_holds_inWay`,
`not_holds_len`, `not_holds_win`, `inWay_of_window`, `clear_scaled`) are reused unchanged.  Grades: [L].
-/

open Classical

namespace Fresh.OneMover

open Fresh

/-- Every frozen integer reading of `S` is clear at `t`. -/
-- STANDING: DEFINITION
def FClear (S : Finset ℕ) (t : ℝ) : Prop := ∀ i ∈ S, (1 / 8 : ℝ) ≤ distInt ((i : ℝ) * t)

/-- The frozen disparities as reals. -/
noncomputable def fset (S : Finset ℕ) : Finset ℝ := S.image (fun i : ℕ => (i : ℝ))

theorem mem_fset {S : Finset ℕ} {d : ℝ} : d ∈ fset S ↔ ∃ i ∈ S, (i : ℝ) = d := by
  unfold fset; simp only [Finset.mem_image]

theorem lonely_insert_iffG (S : Finset ℕ) (ρ s : ℝ) :
    Fresh.Cascade.LonelyAt (insert ρ (fset S)) s ↔ FClear S s ∧ (1 / 8 : ℝ) ≤ distInt (ρ * s) := by
  unfold Fresh.Cascade.LonelyAt FClear
  constructor
  · intro h
    exact ⟨fun i hi => h (i : ℝ) (Finset.mem_insert_of_mem (mem_fset.2 ⟨i, hi, rfl⟩)),
      h ρ (Finset.mem_insert_self _ _)⟩
  · rintro ⟨hF, hρ⟩ d hd
    rcases Finset.mem_insert.1 hd with rfl | hd
    · exact hρ
    · obtain ⟨i, hi, rfl⟩ := mem_fset.1 hd
      exact hF i hi

theorem pos_insertG {S : Finset ℕ} (hS : ∀ i ∈ S, 1 ≤ i) {ρ : ℝ} (hρ : 0 < ρ) :
    ∀ d ∈ insert ρ (fset S), 0 < d := by
  intro d hd
  rcases Finset.mem_insert.1 hd with rfl | hd
  · exact hρ
  · obtain ⟨i, hi, rfl⟩ := mem_fset.1 hd
    have := hS i hi
    exact_mod_cast this

theorem mem_insertG {S : Finset ℕ} (ρ : ℝ) {a : ℕ} (ha : a ∈ S) : (a : ℝ) ∈ insert ρ (fset S) :=
  Finset.mem_insert_of_mem (mem_fset.2 ⟨a, ha, rfl⟩)

theorem fnot (S : Finset ℕ) (i : ℕ) (hi : i ∈ S) (N : ℤ) (s : ℝ)
    (h1 : (N : ℝ) - 1 / 8 < (i : ℝ) * s) (h2 : (i : ℝ) * s < (N : ℝ) + 1 / 8) : ¬ FClear S s :=
  fun hF => not_le.2 (inWay_of_window N h1 h2) (hF i hi)

theorem lonely_geG {ds : Finset ℝ} {a : ℝ} (ha : a ∈ ds) (hapos : 0 < a) {s : ℝ} (hs : 0 < s)
    (hl : Fresh.Cascade.LonelyAt ds s) : 1 / (8 * a) ≤ s :=
  Fresh.Cascade.bound_le_of_lonely ha hapos hl hs

/-- If `T` is the first lonely instant and `a ∈ ds` is the least reading, the cascade from `1/(8a)` lands at `T`. -/
theorem cascade_landsG {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) {a : ℝ} (ha : a ∈ ds) {T : ℝ} (hT : 0 < T)
    (hf : IsFirst ds T) :
    (∃ seq : ℕ → ℝ, seq 0 = 1 / (8 * a) ∧ (∀ n, IsMove ds (seq n) (seq (n + 1))) ∧ ∃ N, seq (N + 1) = seq N) ∧
      ∀ seq : ℕ → ℝ, seq 0 = 1 / (8 * a) → (∀ n, IsMove ds (seq n) (seq (n + 1))) →
        ∀ N, seq (N + 1) = seq N → seq N = T := by
  have hb : 1 / (8 * a) ≤ T := Fresh.Cascade.bound_le_of_lonely ha (hpos a ha) hf.1 hT
  have hb0 : 0 < 1 / (8 * a) := by have := hpos a ha; positivity
  refine ⟨?_, ?_⟩
  · obtain ⟨N, hN⟩ := Fresh.Cascade.exists_fixed_of_lonely hpos hb0 hf.1 hb
    exact ⟨Fresh.Cascade.cascadeSeq ds (1 / (8 * a)), Fresh.Cascade.cascadeSeq_zero _ _,
      Fresh.Cascade.cascadeSeq_isMove _ _, N, hN⟩
  · intro seq h0 hmv N hN
    obtain ⟨hl, hmin⟩ := Fresh.Cascade.fixed_is_first_isolation hpos ha h0 hmv hN
    have hge : seq 0 ≤ seq N := Fresh.Cascade.start_le_seq hpos hmv N
    have hpos' : 0 < seq N := lt_of_lt_of_le (by rw [h0]; exact hb0) hge
    exact le_antisymm (hmin T hT hf.1) (hf.2 _ hpos' hl)

#print axioms lonely_insert_iffG
#print axioms cascade_landsG

end Fresh.OneMover
