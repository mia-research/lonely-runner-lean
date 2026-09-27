import LonelyRunner.LRC.Spec.TwoPinnerN

/-!
# Nested blocks: the ordering makes the set smaller

2026-09-27.  Running record: `RUNNING_LOG_order8_v1.md` E126.

Every reading `d` is clear on the blocks `[(8m+1)/(8d), (8m+7)/(8d)]` of time, one per lap `m`, of length `6/(8d)` and
period `8/(8d)`.  An interval of time of length `L` contains a whole block of `d` as soon as `8d·L ≥ 14` (one period and
one block).  So if each reading is at least `7/3` of the one before, the block of each reading contains a whole block of
the next: nest them from the slowest runner upwards, and every instant of the last block is clear for every runner.

* `exists_block_in`: an interval `[x, x + L]` with `x ≥ 0` and `8d·L ≥ 14` contains a block of `d`.
* `nested_clear`: for readings `d₀ ≤ d₁ ≤ …` given as a function `d : ℕ → ℝ` with `3·d (j+1) ≥ 7·d j` for `j < n`,
  some instant is clear (at least `1/8` from the subject) for `d 0, …, d n`.

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.NestedBlocks

/-- A block of the reading `d` on lap `m`: the instants `t` with `8m + 1 ≤ 8dt ≤ 8m + 7`. -/
def InBlock (d t : ℝ) (m : ℕ) : Prop := (8 * m + 1 : ℝ) ≤ 8 * d * t ∧ 8 * d * t ≤ 8 * m + 7

theorem clear_of_inBlock {d t : ℝ} {m : ℕ} (h : InBlock d t m) : (8 : ℝ)⁻¹ ≤ circDist (d * t) := by
  obtain ⟨h1, h2⟩ := h
  exact LRC.TwoPinner.clear_of_band (N := m) (by push_cast; linarith) (by push_cast; linarith)

/-- **An interval of length `L ≥ 14/(8d)` contains a whole block of `d`.** -/
theorem exists_block_in {d x L : ℝ} (hd : 0 < d) (hx : 0 ≤ x) (hL : 14 ≤ 8 * d * L) :
    ∃ m : ℕ, x ≤ (8 * m + 1) / (8 * d) ∧ (8 * m + 7) / (8 * d) ≤ x + L := by
  have hd8 : (0 : ℝ) < 8 * d := by positivity
  by_cases h : 8 * d * x - 1 ≤ 0
  · refine ⟨0, ?_, ?_⟩
    · rw [le_div_iff₀ hd8]; push_cast; linarith
    · rw [div_le_iff₀ hd8]; push_cast; nlinarith
  · push Not at h
    set m : ℕ := ⌈(8 * d * x - 1) / 8⌉₊ with hm
    have h1 : (8 * d * x - 1) / 8 ≤ (m : ℝ) := Nat.le_ceil _
    have h2 : (m : ℝ) < (8 * d * x - 1) / 8 + 1 := Nat.ceil_lt_add_one (by positivity)
    refine ⟨m, ?_, ?_⟩
    · rw [le_div_iff₀ hd8]; nlinarith
    · rw [div_le_iff₀ hd8]; nlinarith

/-- Growing readings stay positive. -/
theorem pos_of_grow (d : ℕ → ℝ) (h0 : 0 < d 0) (n : ℕ) (hgrow : ∀ j, j < n → 7 * d j ≤ 3 * d (j + 1)) :
    ∀ j, j ≤ n → 0 < d j := by
  intro j
  induction j with
  | zero => intro _; exact h0
  | succ q ih => intro hq; have := hgrow q (by omega); have := ih (by omega); linarith

/-- **Nested blocks.**  Readings with each at least `7/3` of the one before: some instant is clear for all of them. -/
theorem nested_clear (d : ℕ → ℝ) (h0 : 0 < d 0) (n : ℕ) (hgrow : ∀ j, j < n → 7 * d j ≤ 3 * d (j + 1)) :
    ∃ t : ℝ, 0 < t ∧ ∀ j, j ≤ n → (8 : ℝ)⁻¹ ≤ circDist (d j * t) := by
  -- the statement carried: a block of `d n` inside which every instant is clear for `d 0 … d n`
  have key : ∀ n' , n' ≤ n → ∃ m : ℕ, ∀ t, InBlock (d n') t m → ∀ j, j ≤ n' → (8 : ℝ)⁻¹ ≤ circDist (d j * t) := by
    intro n'
    induction n' with
    | zero =>
      intro _
      refine ⟨0, fun t ht j hj => ?_⟩
      have : j = 0 := by omega
      subst this; exact clear_of_inBlock ht
    | succ p ih =>
      intro hp
      obtain ⟨m, hm⟩ := ih (by omega)
      have hdp : 0 < d p := pos_of_grow d h0 n hgrow p (by omega)
      have hdp1 : 0 < d (p + 1) := pos_of_grow d h0 n hgrow (p + 1) hp
      -- the block of `d p` on lap `m`: [x, x + 6/(8 d p)]
      set x := (8 * m + 1 : ℝ) / (8 * d p) with hx
      have hx0 : 0 ≤ x := by positivity
      have hL : 14 ≤ 8 * d (p + 1) * (6 / (8 * d p)) := by
        have := hgrow p (by omega)
        rw [show 8 * d (p + 1) * (6 / (8 * d p)) = 6 * d (p + 1) / d p by field_simp]
        rw [le_div_iff₀ hdp]; linarith
      obtain ⟨m', hm'1, hm'2⟩ := exists_block_in hdp1 hx0 hL
      refine ⟨m', fun t ht j hj => ?_⟩
      rcases Nat.lt_or_ge j (p + 1) with hjp | hjp
      · -- t lies in the block of `d p` on lap `m`
        apply hm t _ j (by omega)
        obtain ⟨a1, a2⟩ := ht
        have hd8 : (0 : ℝ) < 8 * d (p + 1) := by positivity
        have hd8p : (0 : ℝ) < 8 * d p := by positivity
        have tlo : (8 * m' + 1 : ℝ) / (8 * d (p + 1)) ≤ t := by rw [div_le_iff₀ hd8]; linarith
        have thi : t ≤ (8 * m' + 7 : ℝ) / (8 * d (p + 1)) := by rw [le_div_iff₀ hd8]; linarith
        have t1 : x ≤ t := le_trans hm'1 tlo
        have t2 : t ≤ x + 6 / (8 * d p) := le_trans thi hm'2
        constructor
        · rw [hx, div_le_iff₀ hd8p] at t1; linarith
        · have : x + 6 / (8 * d p) = (8 * m + 7) / (8 * d p) := by rw [hx]; field_simp; ring
          rw [this, le_div_iff₀ hd8p] at t2; linarith
      · have : j = p + 1 := by omega
        subst this; exact clear_of_inBlock ht
  obtain ⟨m, hm⟩ := key n le_rfl
  have hdn : 0 < d n := pos_of_grow d h0 n hgrow n le_rfl
  refine ⟨(8 * m + 1) / (8 * (8 * d n)) * 8, by positivity, fun j hj => hm _ ⟨?_, ?_⟩ j hj⟩
  · field_simp; ring_nf; nlinarith
  · field_simp; ring_nf; nlinarith

end LRC.NestedBlocks
