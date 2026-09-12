import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import LonelyRunner.LRC.Defs

/-!
# The n = 8 construction — parts 2(a), 3 and 6(b)

Source: `docs/n8/PROOF_CANDIDATE_v3.md`, parts 2(a), 3, 6(b), and the handover of
2026-09-13 §7 item 2, which names these three as the cheap independent first pass.

Nothing here uses measure, density, covering, a witness, or LRC at any other order.
-/

namespace Construction8

/-! ## Part 2(a) — all eight lonely forces every gap to be exactly `1/8`

Stated for `n` gaps and threshold `1/n`: the conservation law `∑ g = 1` turns the
inequality `g i ≥ 1/n` into an equality for every `i`.
-/

theorem gaps_all_eq {n : ℕ} (hn : 0 < n) (g : Fin n → ℝ)
    (hge : ∀ i, (n : ℝ)⁻¹ ≤ g i) (hsum : ∑ i, g i = 1) (i : Fin n) :
    g i = (n : ℝ)⁻¹ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  -- the slack `g i - 1/n` is nonnegative and sums to zero
  have hslack : ∑ j, (g j - (n : ℝ)⁻¹) = 0 := by
    rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
    norm_num
  have hnonneg : ∀ j ∈ Finset.univ, 0 ≤ g j - (n : ℝ)⁻¹ := fun j _ => sub_nonneg.mpr (hge j)
  have := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hslack i (Finset.mem_univ i)
  linarith

/-! ## Part 3 — the nearest speed is an adjacent one

Sortedness is the whole content: a speed below `i` is at least as far as `i`'s
immediate predecessor, so `d_min` is read off the two neighbours and nothing else.
-/

theorem nearest_below {n : ℕ} (v : Fin n → ℝ) (hv : StrictMono v)
    {i j p : Fin n} (hji : j < i) (hp : (p : ℕ) + 1 = (i : ℕ)) :
    |v i - v p| ≤ |v i - v j| := by
  have hpi : p < i := by
    have : (p : ℕ) < (i : ℕ) := by omega
    exact this
  have hjp : j ≤ p := by
    have hj : (j : ℕ) < (i : ℕ) := hji
    have : (j : ℕ) ≤ (p : ℕ) := by omega
    exact this
  have h1 : v j ≤ v p := hv.monotone hjp
  have h2 : v p < v i := hv hpi
  rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
  linarith

theorem nearest_above {n : ℕ} (v : Fin n → ℝ) (hv : StrictMono v)
    {i j s : Fin n} (hij : i < j) (hs : (i : ℕ) + 1 = (s : ℕ)) :
    |v i - v s| ≤ |v i - v j| := by
  have his : i < s := by
    have : (i : ℕ) < (s : ℕ) := by omega
    exact this
  have hsj : s ≤ j := by
    have hj : (i : ℕ) < (j : ℕ) := hij
    have : (s : ℕ) ≤ (j : ℕ) := by omega
    exact this
  have h1 : v s ≤ v j := hv.monotone hsj
  have h2 : v i < v s := hv his
  rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
  linarith

/-- Part 3, second half: nothing happens before `1/(n · m)`.  At any earlier time the
nearest runner has not yet opened to the threshold, so the runner is not lonely.  Stated
with the project's `circDist`. -/
theorem before_floor {n : ℕ} (hn : 0 < n) {m t : ℝ} (hm : 0 < m) (ht : 0 < t)
    (hlt : t < 1 / (n * m)) : circDist (m * t) < 1 / (n : ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hmt : 0 < m * t := mul_pos hm ht
  have hup : m * t < 1 / (n : ℝ) := by
    have : m * t < m * (1 / (n * m)) := by
      exact mul_lt_mul_of_pos_left hlt hm
    calc m * t < m * (1 / (n * m)) := this
      _ = 1 / (n : ℝ) := by field_simp
  have h1 : m * t < 1 := lt_of_lt_of_le hup (by
    rw [div_le_one hn']; exact_mod_cast hn)
  have hfract : Int.fract (m * t) = m * t :=
    Int.fract_eq_self.mpr ⟨le_of_lt hmt, h1⟩
  unfold circDist
  rw [hfract]
  exact lt_of_le_of_lt (min_le_left _ _) hup

/-! ## Part 6(b) — the deviation displaces by exactly `e_k · r / d` eighths

`V_k = v₀ + k·d + e_k` read at the reference instant `t = r/(n d)`.  The first term
is a common rotation, the second is the eighth `k r / n`, and the third is
`(e_k r / d)` measured in units of the eighth `1/n`.
-/

theorem displacement (n k : ℕ) (v₀ d e r : ℝ) (hd : d ≠ 0) (hn : (n : ℝ) ≠ 0) :
    (v₀ + k * d + e) * (r / (n * d))
      = v₀ * r / (n * d) + (k * r) / n + (e * r / d) * (n : ℝ)⁻¹ := by
  field_simp

end Construction8
