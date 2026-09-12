import LonelyRunner.LRC.Construction8.Parts

/-!
# The lemma pass — general `n`

Source: `docs/n8/SKETCH_v6.md` §4 and §7c, `docs/n8/LEMMAS_v1.md` L2, and
`docs/n8/SKETCH_DEBTS_v2.md` §6, which orders the targets so each needs nothing above it.

Everything is stated at general `n`; `n = 8` is an instantiation. Nothing here uses measure,
covering, a witness, a carrier, or LRC at any order.
-/

namespace Construction8

/-! ## Below the threshold, the norm is the number itself

The one fact both lemmas below turn on: for a nonnegative real, `circDist x ≥ 1/n` forces
`x ≥ 1/n` outright, because `circDist` agrees with `x` on `[0, 1/n)`.
-/

theorem le_of_le_circDist {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x)
    (h : (n : ℝ)⁻¹ ≤ circDist x) : (n : ℝ)⁻¹ ≤ x := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  by_contra hlt
  push Not at hlt
  have h1 : (n : ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]; right; exact_mod_cast hn
  have hx1 : x < 1 := lt_of_lt_of_le hlt h1
  have hfract : Int.fract x = x := Int.fract_eq_self.mpr ⟨hx, hx1⟩
  have : circDist x ≤ x := by
    unfold circDist; rw [hfract]; exact min_le_left _ _
  linarith

/-! ## §7c / L2 — the ceiling on the reference step

If runner `i` is isolated at the step-`D` instant `t = a/(nD)`, then its nearest difference
`m` must itself clear the threshold there, and that forces `D ≤ a·m`.  With `a ≤ n−1` this is
the ceiling `D ≤ (n−1)·d_min(i)`: no larger step can ever serve.
-/

theorem step_ceiling {n : ℕ} (hn : 0 < n) {m a D : ℝ} (hm : 0 < m) (ha : 0 < a) (hD : 0 < D)
    (h : (n : ℝ)⁻¹ ≤ circDist (m * (a / (n * D)))) : D ≤ a * m := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hx : 0 ≤ m * (a / ((n : ℝ) * D)) := by positivity
  have key : (n : ℝ)⁻¹ ≤ m * (a / ((n : ℝ) * D)) := le_of_le_circDist hn hx h
  have hnd : (0 : ℝ) < (n : ℝ) * D := mul_pos hn' hD
  have step := mul_le_mul_of_nonneg_right key (le_of_lt hnd)
  have e1 : (n : ℝ)⁻¹ * ((n : ℝ) * D) = D := by field_simp
  have e2 : (m * (a / ((n : ℝ) * D))) * ((n : ℝ) * D) = a * m := by field_simp
  rw [e1, e2] at step
  exact step

/-! ## §4 — global isolation forces commensurable speeds

All `n` lonely at `t` puts every gap at exactly `1/n`, so the positions are a translate of the
uniform grid and every `(v_i − v_j)·t` is an integer multiple of `1/n`.  Any two differences are
then rationally related.  This is the arithmetic core of that step.
-/

theorem commensurable {n : ℕ} (hn : 0 < n) {t d e : ℝ} (ht : t ≠ 0)
    {a b : ℤ} (hd : d * t = (a : ℝ) / n) (he : e * t = (b : ℝ) / n) (hb : b ≠ 0) :
    ∃ q : ℚ, d = (q : ℝ) * e := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hb' : (b : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hb
  refine ⟨(a : ℚ) / (b : ℚ), ?_⟩
  have h1 : d * t * (b : ℝ) = e * t * (a : ℝ) := by
    rw [hd, he]; field_simp
  have key : t * (d * (b : ℝ) - e * (a : ℝ)) = 0 := by
    calc t * (d * (b : ℝ) - e * (a : ℝ))
        = d * t * (b : ℝ) - e * t * (a : ℝ) := by ring
      _ = 0 := by rw [h1]; ring
  have h2 : d * (b : ℝ) - e * (a : ℝ) = 0 := by
    rcases mul_eq_zero.mp key with h | h
    · exact absurd h ht
    · exact h
  push_cast
  field_simp
  linear_combination h2

end Construction8
