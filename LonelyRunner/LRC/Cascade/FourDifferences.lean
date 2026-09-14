import LonelyRunner.LRC.Cascade.SmallOrders
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Four differences at every `n ≥ 6`, and the slowest-setter recursion

Part of the cascade artefact (`LRC/Cascade/`).  Sections: no return across a few faster moves (`FasterMoves`); four
differences at `n ≥ 8` (`FourDifferences`); the algebra for `n = 6, 7` (`FourSixAlgebra`); four differences at every
`n ≥ 6` (`FourDifferencesSix`); `k` differences at every `n ≥ max(9, 2^(k−1))` (`SlowestRecursion`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-! ## no return after a few faster moves, every `n`

* `faster_lap_ge` — after `x`'s lap-`P` opening, a runner at least as fast as `x` is in the way only at laps `≥ P + 1`.
* `lap_factor_antitone` — the lap factor `(Q + 1/n)/(Q − 1/n)` decreases in `Q ≥ 1`.
* `bernoulli_upper` — `(1 + y)^g · (1 − g·y) ≤ 1` for `y ≥ 0`, `g·y ≤ 1`.
* `no_return_after_few_faster` — if `x` left at its lap-`P` opening and the next `m ≤ g` moves are set at laps `≥ P + 1`,
  then `x` is not in the way after them, whenever `n ≥ 2g + 2`.  (At `n = 8`, `g = 3`: the slowest runner cannot return
  across three faster moves.) -/

namespace FasterMoves

open ConstructionN MomentIterationN TerminationFour ChainBounds NearestState FewDifferences

theorem faster_lap_ge {n : ℕ} {x y t t' : ℝ} (hx : 0 < x) (hxy : x ≤ y) {P Q : ℤ} (hP : 0 ≤ P)
    (ht : t = ((P : ℝ) + (n : ℝ)⁻¹) / x) (htt : t < t') (hk : |y * t' - Q| < (n : ℝ)⁻¹) : P + 1 ≤ Q := by
  have hh0 : (0 : ℝ) ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg n)
  have hPr : (0 : ℝ) ≤ P := by exact_mod_cast hP
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hxt : x * t = P + (n : ℝ)⁻¹ := by rw [ht]; field_simp
  have ht0 : 0 ≤ t := by rw [ht]; exact div_nonneg (by linarith) hx.le
  have h1 : x * t ≤ y * t := mul_le_mul_of_nonneg_right hxy ht0
  have h2 : y * t < y * t' := mul_lt_mul_of_pos_left htt hy
  have h3 := (abs_lt.mp hk).2
  have h4 : (P : ℝ) < Q := by linarith
  have h5 : P < Q := by exact_mod_cast h4
  omega

theorem lap_factor_antitone {n : ℕ} [Fact (2 ≤ n)] {A B : ℤ} (hA : 1 ≤ A) (hAB : A ≤ B) :
    ((B : ℝ) + (n : ℝ)⁻¹) / ((B : ℝ) - (n : ℝ)⁻¹) ≤ ((A : ℝ) + (n : ℝ)⁻¹) / ((A : ℝ) - (n : ℝ)⁻¹) := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hh0 : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr hn0
  have hhle : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  have hAr : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hABr : (A : ℝ) ≤ B := by exact_mod_cast hAB
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

theorem bernoulli_upper {y : ℝ} (hy : 0 ≤ y) : ∀ g : ℕ, (g : ℝ) * y ≤ 1 → (1 + y) ^ g * (1 - g * y) ≤ 1 := by
  intro g
  induction g with
  | zero => intro _; simp
  | succ g ih =>
    intro hg
    push_cast at hg
    have hg' : (g : ℝ) * y ≤ 1 := by nlinarith
    have ih' := ih hg'
    have hp : 0 ≤ (1 + y) ^ g := pow_nonneg (by linarith) g
    have key : (1 + y) * (1 - ((g : ℝ) + 1) * y) ≤ 1 - g * y := by
      have e : (1 + y) * (1 - ((g : ℝ) + 1) * y) = 1 - g * y - ((g : ℝ) + 1) * (y * y) := by ring
      have : 0 ≤ ((g : ℝ) + 1) * (y * y) := mul_nonneg (by positivity) (mul_nonneg hy hy)
      linarith
    have h1 : 0 ≤ 1 - ((g : ℝ) + 1) * y := by linarith
    calc (1 + y) ^ (g + 1) * (1 - ((g + 1 : ℕ) : ℝ) * y) = (1 + y) ^ g * ((1 + y) * (1 - ((g : ℝ) + 1) * y)) := by
          push_cast; ring
      _ ≤ (1 + y) ^ g * (1 - g * y) := mul_le_mul_of_nonneg_left key hp
      _ ≤ 1 := ih'

/-- The lap factor at `P + 1` raised to `g` stays below the growth a lap-`P` return needs, when `n ≥ 2g + 2`. -/
theorem factor_pow_le_return {n : ℕ} [Fact (2 ≤ n)] {P : ℤ} (hP : 0 ≤ P) (g : ℕ) (hng : 2 * g + 2 ≤ n) :
    ((((P + 1 : ℤ) : ℝ) + (n : ℝ)⁻¹) / (((P + 1 : ℤ) : ℝ) - (n : ℝ)⁻¹)) ^ g ≤
      ((P : ℝ) + 1 - (n : ℝ)⁻¹) / ((P : ℝ) + (n : ℝ)⁻¹) := by
  have hn0 : (0 : ℝ) < n := n_pos
  set h : ℝ := (n : ℝ)⁻¹ with hh
  have hh0 : 0 < h := inv_pos.mpr hn0
  have hnh : (n : ℝ) * h = 1 := mul_inv_cancel₀ hn0.ne'
  have hhle : h ≤ 2⁻¹ := inv_le_half
  have hPr : (0 : ℝ) ≤ P := by exact_mod_cast hP
  have hng' : 2 * (g : ℝ) + 2 ≤ n := by exact_mod_cast hng
  push_cast
  have hden : 0 < (P : ℝ) + 1 - h := by linarith
  set y : ℝ := 2 * h / ((P : ℝ) + 1 - h) with hy
  have hy0 : 0 ≤ y := by rw [hy]; positivity
  have hF : ((P : ℝ) + 1 + h) / ((P : ℝ) + 1 - h) = 1 + y := by rw [hy]; field_simp; ring
  rw [hF]
  -- `g·y ≤ 1 − 2h/(P + 1 − h)·…`: from `2g·h ≤ 1 − 2h`
  have h2gh : 2 * (g : ℝ) * h ≤ 1 - 2 * h := by
    have : 2 * (g : ℝ) * h = (2 * g) * h := by ring
    have h3 : (2 * (g : ℝ)) * h ≤ ((n : ℝ) - 2) * h := mul_le_mul_of_nonneg_right (by linarith) hh0.le
    have e : ((n : ℝ) - 2) * h = 1 - 2 * h := by rw [sub_mul, hnh]
    linarith
  have hgy : (g : ℝ) * y ≤ (1 - 2 * h) / ((P : ℝ) + 1 - h) := by
    rw [hy]
    have e1 : (g : ℝ) * (2 * h / ((P : ℝ) + 1 - h)) = 2 * g * h / ((P : ℝ) + 1 - h) := by ring
    rw [e1]
    exact div_le_div_of_nonneg_right h2gh hden.le
  have hlt1 : (1 - 2 * h) / ((P : ℝ) + 1 - h) < 1 := by rw [div_lt_one hden]; linarith
  have hgy1 : (g : ℝ) * y ≤ 1 := by linarith
  have hpos : 0 < 1 - (g : ℝ) * y := by linarith
  have hb := bernoulli_upper hy0 g hgy1
  have hpow : (1 + y) ^ g ≤ 1 / (1 - g * y) := by rw [le_div_iff₀ hpos]; linarith
  refine le_trans hpow ?_
  rw [div_le_div_iff₀ hpos (by linarith)]
  -- `P + h ≤ (P + 1 − h)(1 − g·y)`
  have e3 : ((P : ℝ) + 1 - h) * (1 - g * y) = (P : ℝ) + 1 - h - 2 * g * h := by
    rw [hy]; field_simp
  nlinarith

/-- **No return across a few faster moves.** -/
theorem no_return_after_few_faster {n : ℕ} [Fact (2 ≤ n)] {x : ℝ} (hx : 0 < x) {P : ℤ} (hP : 0 ≤ P)
    (g m : ℕ) (hm : m ≤ g) (hng : 2 * g + 2 ≤ n) (t : ℕ → ℝ) (Q : ℕ → ℤ)
    (ht0 : t 0 = ((P : ℝ) + (n : ℝ)⁻¹) / x)
    (hgrow : ∀ j < m, t (j + 1) ≤ ((Q j : ℝ) + (n : ℝ)⁻¹) / ((Q j : ℝ) - (n : ℝ)⁻¹) * t j)
    (hlap : ∀ j < m, P + 1 ≤ Q j) (htpos : ∀ j, 0 < t j) (hlt : t 0 < t m) (hw : inWay n x (t m)) :
    False := by
  have hn0 : (0 : ℝ) < n := n_pos
  set h : ℝ := (n : ℝ)⁻¹ with hh
  have hh0 : 0 < h := inv_pos.mpr hn0
  have hhle : h ≤ 2⁻¹ := inv_le_half
  have hPr : (0 : ℝ) ≤ P := by exact_mod_cast hP
  set F : ℝ := (((P + 1 : ℤ) : ℝ) + h) / (((P + 1 : ℤ) : ℝ) - h) with hF
  have hF1 : 1 ≤ F := by
    rw [hF]; push_cast; rw [le_div_iff₀ (by linarith)]; linarith
  have ht0pos : 0 < t 0 := by rw [ht0]; exact div_pos (by linarith) hx
  have hbound : ∀ j ≤ m, t j ≤ F ^ j * t 0 := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have ihj := ih (by omega)
      have hQ := hlap j (by omega)
      have hfac : ((Q j : ℝ) + h) / ((Q j : ℝ) - h) ≤ F :=
        lap_factor_antitone (n := n) (by omega) hQ
      have htj0 : 0 ≤ t j := (htpos j).le
      calc t (j + 1) ≤ ((Q j : ℝ) + h) / ((Q j : ℝ) - h) * t j := hgrow j (by omega)
        _ ≤ F * t j := mul_le_mul_of_nonneg_right hfac htj0
        _ ≤ F * (F ^ j * t 0) := mul_le_mul_of_nonneg_left ihj (by linarith)
        _ = F ^ (j + 1) * t 0 := by ring
  have hr := return_growth hx hP ht0 hlt hw
  have hm1 := hbound m le_rfl
  have hpowm : F ^ m ≤ F ^ g := pow_le_pow_right₀ hF1 hm
  have hkey := factor_pow_le_return (n := n) hP g hng
  have : F ^ m * t 0 ≤ ((P : ℝ) + 1 - h) / ((P : ℝ) + h) * t 0 :=
    mul_le_mul_of_nonneg_right (le_trans hpowm hkey) ht0pos.le
  linarith

end FasterMoves


/-! ## four differences at every `n ≥ 8`: the iteration stops within seven moves

With at most four differences and nearest `a`, for `n ≥ 8`:
1. the nearest runner is clear at iterates `0 … 7` (`nearest_clear_first_moves`, since `((n + 1)/(n − 1))^7 ≤ n − 1`);
2. so eight moves would be set by the other three runners, consecutive setters distinct;
3. the slowest of those setters, `v`, sets at most once: a return across `≤ 3` moves is excluded by
   `no_return_after_few_faster` (`n ≥ 2·3 + 2`), and a gap of `≥ 4` moves would be four consecutive moves by the other
   two runners, which alternate — excluded by W2 (`no_four_alternation`);
4. hence four consecutive moves avoid `v`, and W2 excludes them.  So the seventh iterate is fixed. -/

namespace FourDifferences

open ConstructionN MomentIterationN TerminationFour ChainBounds NearestState FewDifferences WordRules FasterMoves

theorem faster_lap_ge' {n : ℕ} {x y t t' : ℝ} (hx : 0 < x) (hxy : x ≤ y) {P Q : ℤ} (hP : 0 ≤ P)
    (ht : t = ((P : ℝ) + (n : ℝ)⁻¹) / x) (htt : t ≤ t') (hk : |y * t' - Q| < (n : ℝ)⁻¹) : P + 1 ≤ Q := by
  have hh0 : (0 : ℝ) ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg n)
  have hPr : (0 : ℝ) ≤ P := by exact_mod_cast hP
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hxt : x * t = P + (n : ℝ)⁻¹ := by rw [ht]; field_simp
  have ht0 : 0 ≤ t := by rw [ht]; exact div_nonneg (by linarith) hx.le
  have h1 : x * t ≤ y * t := mul_le_mul_of_nonneg_right hxy ht0
  have h2 : y * t ≤ y * t' := mul_le_mul_of_nonneg_left htt hy.le
  have h3 := (abs_lt.mp hk).2
  have h4 : (P : ℝ) < Q := by linarith
  have h5 : P < Q := by exact_mod_cast h4
  omega

theorem iterate_stable {n : ℕ} {ds : Finset ℝ} {b : ℝ} {j : ℕ}
    (hfix : move n ds ((move n ds)^[j] b) = (move n ds)^[j] b) :
    ∀ i, (move n ds)^[j + i] b = (move n ds)^[j] b := by
  intro i
  induction i with
  | zero => rfl
  | succ i ih => rw [← add_assoc, Function.iterate_succ_apply', ih, hfix]

/-- W2 on a word of iterates: consecutive setters `s j, s (j+1), s (j+2), s (j+3)` cannot alternate. -/
theorem word_no_alternation {n : ℕ} [Fact (2 ≤ n)] (hn4 : 4 ≤ n) (t s : ℕ → ℝ) (q : ℕ → ℤ) (j : ℕ)
    (hs0 : 0 < s j) (hs1 : 0 < s (j + 1)) (hq0 : 0 ≤ q j) (hq1 : 0 ≤ q (j + 1))
    (e0 : t (j + 1) = ((q j : ℝ) + (n : ℝ)⁻¹) / s j)
    (e1 : t (j + 2) = ((q (j + 1) : ℝ) + (n : ℝ)⁻¹) / s (j + 1))
    (e2 : t (j + 3) = ((q (j + 2) : ℝ) + (n : ℝ)⁻¹) / s (j + 2))
    (k1 : |s (j + 1) * t (j + 1) - q (j + 1)| < (n : ℝ)⁻¹)
    (k2 : |s (j + 2) * t (j + 2) - q (j + 2)| < (n : ℝ)⁻¹)
    (lt12 : t (j + 1) < t (j + 2)) (lt23 : t (j + 2) < t (j + 3))
    (w3 : inWay n (s (j + 3)) (t (j + 3)))
    (hA : s j = s (j + 2)) (hB : s (j + 1) = s (j + 3)) : False := by
  apply no_four_alternation (n := n) hn4 hs0 hs1 hq0 hq1 (P' := q (j + 2))
  · rw [← e0]; exact k1
  · rw [← e0, ← e1]; exact lt12
  · rw [← e1, hA]; exact k2
  · rw [← e1, hA, ← e2]; exact lt23
  · rw [hA, ← e2, hB]; exact w3

/-- The slowest setter does not return across at most three moves (for `n ≥ 8`). -/
theorem word_no_slow_return {n : ℕ} [Fact (2 ≤ n)] (hn8 : 8 ≤ n) (t s : ℕ → ℝ) (q : ℕ → ℤ) (i k : ℕ)
    (hik : i + 1 < k) (hk4 : k ≤ i + 4) (htpos : ∀ j, 0 < t j) (hspos : ∀ j, i ≤ j → j ≤ k → 0 < s j)
    (hdat : ∀ j, i ≤ j → j < k → |s j * t j - q j| < (n : ℝ)⁻¹ ∧ t (j + 1) = ((q j : ℝ) + (n : ℝ)⁻¹) / s j)
    (hkw : inWay n (s k) (t k)) (hvmin : ∀ j, i < j → j < k → s i ≤ s j) (hsame : s k = s i)
    (hqi : 0 ≤ q i) (hmono : ∀ j j', j ≤ j' → t j ≤ t j') (hstrict : t (i + 1) < t k) : False := by
  set m := k - i - 1 with hm
  have hmk : i + 1 + m = k := by omega
  have hm3 : m ≤ 3 := by omega
  obtain ⟨-, hei⟩ := hdat i le_rfl (by omega)
  have hlap : ∀ j < m, q i + 1 ≤ q (i + 1 + j) := by
    intro j hj
    exact faster_lap_ge' (hspos i le_rfl (by omega)) (hvmin (i + 1 + j) (by omega) (by omega)) hqi hei
      (hmono _ _ (by omega)) (hdat (i + 1 + j) (by omega) (by omega)).1
  apply no_return_after_few_faster (n := n) (hspos i le_rfl (by omega)) hqi 3 m hm3 (by omega)
    (fun j => t (i + 1 + j)) (fun j => q (i + 1 + j)) hei
  · intro j hj
    obtain ⟨hk, he⟩ := hdat (i + 1 + j) (by omega) (by omega)
    have hQ : 1 ≤ q (i + 1 + j) := by have := hlap j hj; omega
    show t (i + 1 + (j + 1)) ≤ _
    have e : i + 1 + (j + 1) = i + 1 + j + 1 := by omega
    rw [e, he]
    exact (move_growth (hspos _ (by omega) (by omega)) (htpos _) hQ hk).le
  · exact hlap
  · exact fun j => htpos _
  · show t (i + 1 + 0) < t (i + 1 + m); rw [add_zero, hmk]; exact hstrict
  · show inWay n (s i) (t (i + 1 + m)); rw [hmk, ← hsame]; exact hkw

theorem four_diffs_stop_ge_eight {n : ℕ} [Fact (2 ≤ n)] (hn8 : 8 ≤ n) {ds : Finset ℝ}
    (hpos : ∀ d ∈ ds, 0 < d) (hcard : ds.card ≤ 4) {a : ℝ} (ha : a ∈ ds) (hmin : ∀ d ∈ ds, a ≤ d) :
    move n ds ((move n ds)^[7] (1 / (n * a))) = (move n ds)^[7] (1 / (n * a)) := by
  classical
  have ha0 := hpos a ha
  have hn0 : (0 : ℝ) < n := n_pos
  have hN8 : (8 : ℝ) ≤ n := by exact_mod_cast hn8
  have hh0 : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr hn0
  have hhle : (n : ℝ)⁻¹ ≤ 8⁻¹ := inv_anti₀ (by norm_num) hN8
  set b0 := 1 / ((n : ℝ) * a) with hb0
  set t : ℕ → ℝ := fun j => (move n ds)^[j] b0 with htdef
  have htsucc : ∀ j, t (j + 1) = move n ds (t j) := fun j => Function.iterate_succ_apply' _ _ _
  have hb0pos : 0 < b0 := by rw [hb0]; positivity
  have htpos : ∀ j, 0 < t j := fun j => lt_of_lt_of_le hb0pos (iterate_ge (n := n) ds b0 j)
  have htmono : ∀ j j', j ≤ j' → t j ≤ t j' := by
    have : Monotone t := monotone_nat_of_le_succ (fun j => by rw [htsucc]; exact le_move ds _)
    exact fun j j' h => this h
  have hat : ∀ j, (n : ℝ)⁻¹ ≤ a * t j := by
    intro j
    have hab : a * b0 = (n : ℝ)⁻¹ := by rw [hb0]; field_simp
    rw [← hab]; exact mul_le_mul_of_nonneg_left (iterate_ge (n := n) ds b0 j) ha0.le
  -- 1. the nearest runner is clear at iterates 0..7
  have hq1 : 1 ≤ (1 + (n : ℝ)⁻¹) / (1 - (n : ℝ)⁻¹) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  have hq97 : (1 + (n : ℝ)⁻¹) / (1 - (n : ℝ)⁻¹) ≤ 9 / 7 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have hclear : ∀ j ≤ 7, ¬ inWay n a (t j) := by
    intro j hj
    apply nearest_clear_first_moves hpos ha hmin j
    calc ((1 + (n : ℝ)⁻¹) / (1 - (n : ℝ)⁻¹)) ^ j ≤ ((1 + (n : ℝ)⁻¹) / (1 - (n : ℝ)⁻¹)) ^ 7 :=
          pow_le_pow_right₀ hq1 hj
      _ ≤ (9 / 7) ^ 7 := pow_le_pow_left₀ (by linarith) hq97 7
      _ ≤ n - 1 := by norm_num; linarith
  show move n ds (t 7) = t 7
  by_contra hne
  have hmoving : ∀ j ≤ 7, move n ds (t j) ≠ t j := by
    intro j hj hfix
    have hst := iterate_stable (n := n) (b := b0) hfix (7 - j)
    have e : j + (7 - j) = 7 := by omega
    rw [e] at hst
    apply hne
    show move n ds ((move n ds)^[7] b0) = (move n ds)^[7] b0
    rw [hst]; exact hfix
  -- 2. setters and laps
  have hex : ∀ j : ℕ, ∃ x : ℝ, ∃ k : ℤ, move n ds (t j) = t j ∨
      (x ∈ ds ∧ |x * t j - k| < (n : ℝ)⁻¹ ∧ t (j + 1) = ((k : ℝ) + (n : ℝ)⁻¹) / x) := by
    intro j
    rcases step_cases (n := n) hpos (t j) with h1 | ⟨x, hx, k, hk, he⟩
    · exact ⟨0, 0, Or.inl h1⟩
    · exact ⟨x, k, Or.inr ⟨hx, hk, by rw [htsucc, he]⟩⟩
  choose s q hsq using hex
  have hD : ∀ j ≤ 7, s j ∈ ds ∧ |s j * t j - q j| < (n : ℝ)⁻¹ ∧ t (j + 1) = ((q j : ℝ) + (n : ℝ)⁻¹) / s j := by
    intro j hj
    rcases hsq j with h1 | h1
    · exact absurd h1 (hmoving j hj)
    · exact h1
  have hspos : ∀ j ≤ 7, 0 < s j := fun j hj => hpos _ (hD j hj).1
  have hw : ∀ j ≤ 7, inWay n (s j) (t j) := fun j hj => inWay_of_near (hD j hj).2.1
  have hsa : ∀ j ≤ 7, s j ≠ a := fun j hj he => hclear j hj (he ▸ hw j hj)
  have hlt : ∀ j ≤ 7, t j < t (j + 1) := by
    intro j hj
    obtain ⟨-, hk, he⟩ := hD j hj
    have hx0 := hspos j hj
    have h1 : s j * t (j + 1) = q j + (n : ℝ)⁻¹ := by rw [he]; field_simp
    have : s j * t j < s j * t (j + 1) := by rw [h1]; linarith [(abs_lt.mp hk).2]
    exact lt_of_mul_lt_mul_left this hx0.le
  have hadj : ∀ j, j + 1 ≤ 7 → s (j + 1) ≠ s j := by
    intro j hj he
    have hw1 := hw (j + 1) hj
    rw [he, (hD j (by omega)).2.2] at hw1
    exact not_inWay_at_own_opening (hspos j (by omega)) (q j) hw1
  have hq1' : ∀ j ≤ 7, 1 ≤ q j := fun j hj =>
    lap_ge_one (hmin _ (hD j hj).1) (htpos j).le (hat j) (hD j hj).2.1
  have hW2 : ∀ j, j + 3 ≤ 7 → s j = s (j + 2) → s (j + 1) = s (j + 3) → False := by
    intro j hj hA hB
    exact word_no_alternation (n := n) (by omega) t s q j (hspos j (by omega)) (hspos (j + 1) (by omega))
      (by have := hq1' j (by omega); omega) (by have := hq1' (j + 1) (by omega); omega)
      (hD j (by omega)).2.2 (hD (j + 1) (by omega)).2.2 (hD (j + 2) (by omega)).2.2
      (hD (j + 1) (by omega)).2.1 (hD (j + 2) (by omega)).2.1
      (hlt (j + 1) (by omega)) (hlt (j + 2) (by omega)) (hw (j + 3) (by omega)) hA hB
  -- 3. the slowest setter
  obtain ⟨j0, hj0, hj0min⟩ := (Finset.range 8).exists_min_image s ⟨0, by simp⟩
  have hj0' : j0 ≤ 7 := by have := Finset.mem_range.mp hj0; omega
  set v := s j0 with hv
  have hvmin : ∀ j ≤ 7, v ≤ s j := fun j hj => hj0min j (Finset.mem_range.mpr (by omega))
  have hvds : v ∈ ds.erase a := Finset.mem_erase.mpr ⟨hsa j0 hj0', (hD j0 hj0').1⟩
  have hcard2 : ((ds.erase a).erase v).card ≤ 2 := by
    rw [Finset.card_erase_of_mem hvds, Finset.card_erase_of_mem ha]; omega
  -- four consecutive setters avoiding `v` contradict W2
  have hblock : ∀ j, j + 3 ≤ 7 → s j ≠ v → s (j + 1) ≠ v → s (j + 2) ≠ v → s (j + 3) ≠ v → False := by
    intro j hj h0 h1 h2 h3
    have mem : ∀ i, j ≤ i → i ≤ j + 3 → s i ≠ v → s i ∈ (ds.erase a).erase v := fun i hi1 hi2 hne =>
      Finset.mem_erase.mpr ⟨hne, Finset.mem_erase.mpr ⟨hsa i (by omega), (hD i (by omega)).1⟩⟩
    have hsub : ({s j, s (j + 1)} : Finset ℝ) ⊆ (ds.erase a).erase v := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact mem j le_rfl (by omega) h0
      · exact mem (j + 1) (by omega) (by omega) h1
    have hpair : ({s j, s (j + 1)} : Finset ℝ).card = 2 := Finset.card_pair (Ne.symm (hadj j (by omega)))
    have heq : ({s j, s (j + 1)} : Finset ℝ) = (ds.erase a).erase v :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    have m2 : s (j + 2) ∈ ({s j, s (j + 1)} : Finset ℝ) := by rw [heq]; exact mem (j + 2) (by omega) (by omega) h2
    have m3 : s (j + 3) ∈ ({s j, s (j + 1)} : Finset ℝ) := by rw [heq]; exact mem (j + 3) (by omega) (by omega) h3
    simp only [Finset.mem_insert, Finset.mem_singleton] at m2 m3
    have hA : s j = s (j + 2) := by
      rcases m2 with e | e
      · exact e.symm
      · exact absurd e (hadj (j + 1) (by omega))
    have hB : s (j + 1) = s (j + 3) := by
      rcases m3 with e | e
      · exact absurd (e.trans hA) (hadj (j + 2) (by omega))
      · exact e.symm
    exact hW2 j hj hA hB
  -- `v` occurs at most once
  have honce : ∀ i k, i < k → k ≤ 7 → s i = v → s k = v → False := by
    intro i k hik hk7 hi hk
    -- take the first occurrence of `v` after `i`
    have hex' : ∃ k', i < k' ∧ k' ≤ 7 ∧ s k' = v := ⟨k, hik, hk7, hk⟩
    let k' := Nat.find hex'
    obtain ⟨hik', hk'7, hk'v⟩ := Nat.find_spec hex'
    have hbetween : ∀ j, i < j → j < k' → s j ≠ v := by
      intro j hj1 hj2 hjv
      exact Nat.find_min hex' hj2 ⟨hj1, by omega, hjv⟩
    rcases Nat.lt_or_ge (i + 4) k' with hfar | hnear
    · exact hblock (i + 1) (by omega) (hbetween _ (by omega) (by omega)) (hbetween _ (by omega) (by omega))
        (hbetween _ (by omega) (by omega)) (hbetween _ (by omega) (by omega))
    · have hik1 : i + 1 < k' := by
        rcases Nat.lt_or_ge (i + 1) k' with h | h
        · exact h
        · have : k' = i + 1 := by omega
          exfalso; apply hadj i (by omega); rw [← this]; rw [hk'v, hi]
      exact word_no_slow_return (n := n) hn8 t s q i k' hik1 hnear htpos
        (fun j h1 h2 => hspos j (by omega)) (fun j h1 h2 => ⟨(hD j (by omega)).2.1, (hD j (by omega)).2.2⟩)
        (hw k' hk'7) (fun j h1 h2 => by rw [hi]; exact hvmin j (by omega)) (by rw [hk'v, hi])
        (by have := hq1' i (by omega); omega) htmono
        (lt_of_lt_of_le (hlt (i + 1) (by omega)) (htmono _ _ (by omega)))
  -- 4. a block of four avoiding `v`
  have hnot : ∀ j ≤ 7, j ≠ j0 → s j ≠ v := by
    intro j hj hne' hjv
    rcases Nat.lt_or_gt_of_ne hne' with h | h
    · exact honce j j0 h hj0' hjv rfl
    · exact honce j0 j h hj rfl hjv
  rcases Nat.lt_or_ge j0 4 with h | h
  · exact hblock 4 (by omega) (hnot 4 (by omega) (by omega)) (hnot 5 (by omega) (by omega))
      (hnot 6 (by omega) (by omega)) (hnot 7 (by omega) (by omega))
  · exact hblock 0 (by omega) (hnot 0 (by omega) (by omega)) (hnot 1 (by omega) (by omega))
      (hnot 2 (by omega) (by omega)) (hnot 3 (by omega) (by omega))

end FourDifferences


/-! ## algebra for four differences at `n = 6, 7`

* `lap_factor_antitone_real` — the lap factor decreases in a real lap `≥ 1`.
* `three_move_bound` — for `n ≥ 6`, `P ≥ 0` and `2A ≥ (P + 1)(n − 2)`:
  `F(A)·F(P + 1)·F(A + 1) ≤ (P + 1 − 1/n)/(P + 1/n)` (a return across three moves `y z y` whose middle runner forces
  `y`'s lap up by the return lemma).  Proof: reduce to `A = (P + 1)(n − 2)/2`; with `x = n − 6` the cleared difference
  times 4 is a polynomial in `x, P` with positive coefficients.
* `sorted_lap_prod` — a runner's moves land on distinct laps `≥ 1`, so the product of their lap factors is at most
  `∏_{r=1}^{m} F(r)` for `m` moves.
* `g_balance` — with `g m = ∏_{r=1}^{m} F(r)`: `a + b ≤ 2m → g a · g b ≤ g m · g m`. -/

namespace FourSixAlgebra

open ConstructionN MomentIterationN

theorem lap_factor_antitone_real {n : ℕ} [Fact (2 ≤ n)] {A B : ℝ} (hA : 1 ≤ A) (hAB : A ≤ B) :
    (B + (n : ℝ)⁻¹) / (B - (n : ℝ)⁻¹) ≤ (A + (n : ℝ)⁻¹) / (A - (n : ℝ)⁻¹) := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hh0 : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr hn0
  have hhle : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

theorem three_move_poly (N P : ℝ) (hN : 6 ≤ N) (hP : 0 ≤ P) :
    (N * ((P + 1) * (N - 2) / 2) + 1) * (N * (P + 1) + 1) * (N * ((P + 1) * (N - 2) / 2 + 1) + 1) * (N * P + 1) ≤
      (N * P + N - 1) * ((N * ((P + 1) * (N - 2) / 2) - 1) * (N * (P + 1) - 1) *
        (N * ((P + 1) * (N - 2) / 2 + 1) - 1)) := by
  obtain ⟨x, hx, rfl⟩ : ∃ x, 0 ≤ x ∧ N = x + 6 := ⟨N - 6, by linarith, by ring⟩
  have key : 4 * ((( x + 6) * P + (x + 6) - 1) * (((x + 6) * ((P + 1) * ((x + 6) - 2) / 2) - 1) *
      ((x + 6) * (P + 1) - 1) * ((x + 6) * ((P + 1) * ((x + 6) - 2) / 2 + 1) - 1)) -
      ((x + 6) * ((P + 1) * ((x + 6) - 2) / 2) + 1) * ((x + 6) * (P + 1) + 1) *
      ((x + 6) * ((P + 1) * ((x + 6) - 2) / 2 + 1) + 1) * ((x + 6) * P + 1)) =
      1*x^6*P^3 + 3*x^6*P^2 + 3*x^6*P + 1*x^6 + 28*x^5*P^3 + 87*x^5*P^2 + 90*x^5*P + 31*x^5 + 312*x^4*P^3 + 1014*x^4*P^2 + 1094*x^4*P + 392*x^4 + 1728*x^3*P^3 + 5980*x^3*P^2 + 6828*x^3*P + 2576*x^3 + 4752*x^2*P^3 + 18216*x^2*P^2 + 22668*x^2*P + 9208*x^2 + 5184*x*P^3 + 25056*x*P^2 + 36576*x*P + 16748*x + 8640*P^2 + 20304*P + 11784 := by ring
  have hE : 0 ≤ 1*x^6*P^3 + 3*x^6*P^2 + 3*x^6*P + 1*x^6 + 28*x^5*P^3 + 87*x^5*P^2 + 90*x^5*P + 31*x^5 + 312*x^4*P^3 + 1014*x^4*P^2 + 1094*x^4*P + 392*x^4 + 1728*x^3*P^3 + 5980*x^3*P^2 + 6828*x^3*P + 2576*x^3 + 4752*x^2*P^3 + 18216*x^2*P^2 + 22668*x^2*P + 9208*x^2 + 5184*x*P^3 + 25056*x*P^2 + 36576*x*P + 16748*x + 8640*P^2 + 20304*P + 11784 := by
    linarith [mul_nonneg (pow_nonneg hx 6) (pow_nonneg hP 3), mul_nonneg (pow_nonneg hx 6) (pow_nonneg hP 2), mul_nonneg (pow_nonneg hx 6) (pow_nonneg hP 1), pow_nonneg hx 6, mul_nonneg (pow_nonneg hx 5) (pow_nonneg hP 3), mul_nonneg (pow_nonneg hx 5) (pow_nonneg hP 2), mul_nonneg (pow_nonneg hx 5) (pow_nonneg hP 1), pow_nonneg hx 5, mul_nonneg (pow_nonneg hx 4) (pow_nonneg hP 3), mul_nonneg (pow_nonneg hx 4) (pow_nonneg hP 2), mul_nonneg (pow_nonneg hx 4) (pow_nonneg hP 1), pow_nonneg hx 4, mul_nonneg (pow_nonneg hx 3) (pow_nonneg hP 3), mul_nonneg (pow_nonneg hx 3) (pow_nonneg hP 2), mul_nonneg (pow_nonneg hx 3) (pow_nonneg hP 1), pow_nonneg hx 3, mul_nonneg (pow_nonneg hx 2) (pow_nonneg hP 3), mul_nonneg (pow_nonneg hx 2) (pow_nonneg hP 2), mul_nonneg (pow_nonneg hx 2) (pow_nonneg hP 1), pow_nonneg hx 2, mul_nonneg (pow_nonneg hx 1) (pow_nonneg hP 3), mul_nonneg (pow_nonneg hx 1) (pow_nonneg hP 2), mul_nonneg (pow_nonneg hx 1) (pow_nonneg hP 1), pow_nonneg hx 1, pow_nonneg hP 2, pow_nonneg hP 1]
  linarith

theorem three_move_bound {n : ℕ} [Fact (2 ≤ n)] (hn6 : 6 ≤ n) {P A : ℝ} (hP : 0 ≤ P)
    (hA : (P + 1) * ((n : ℝ) - 2) ≤ 2 * A) :
    (A + (n : ℝ)⁻¹) / (A - (n : ℝ)⁻¹) * ((P + 1 + (n : ℝ)⁻¹) / (P + 1 - (n : ℝ)⁻¹)) *
        ((A + 1 + (n : ℝ)⁻¹) / (A + 1 - (n : ℝ)⁻¹)) ≤ (P + 1 - (n : ℝ)⁻¹) / (P + (n : ℝ)⁻¹) := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hN6 : (6 : ℝ) ≤ n := by exact_mod_cast hn6
  have hh0 : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr hn0
  have hhle : (n : ℝ)⁻¹ ≤ 6⁻¹ := inv_anti₀ (by norm_num) hN6
  set Am := (P + 1) * ((n : ℝ) - 2) / 2 with hAm
  have hAm1 : 1 ≤ Am := by rw [hAm]; nlinarith
  have hAAm : Am ≤ A := by rw [hAm]; linarith
  have f1 := lap_factor_antitone_real (n := n) hAm1 hAAm
  have f2 := lap_factor_antitone_real (n := n) (by linarith : (1 : ℝ) ≤ Am + 1) (by linarith : Am + 1 ≤ A + 1)
  have hFP : 0 ≤ (P + 1 + (n : ℝ)⁻¹) / (P + 1 - (n : ℝ)⁻¹) := div_nonneg (by linarith) (by linarith)
  have hFA : 0 ≤ (A + 1 + (n : ℝ)⁻¹) / (A + 1 - (n : ℝ)⁻¹) := div_nonneg (by linarith) (by linarith)
  have hFAm : 0 ≤ (Am + (n : ℝ)⁻¹) / (Am - (n : ℝ)⁻¹) := div_nonneg (by linarith) (by linarith)
  have step1 : (A + (n : ℝ)⁻¹) / (A - (n : ℝ)⁻¹) * ((P + 1 + (n : ℝ)⁻¹) / (P + 1 - (n : ℝ)⁻¹)) *
        ((A + 1 + (n : ℝ)⁻¹) / (A + 1 - (n : ℝ)⁻¹)) ≤
      (Am + (n : ℝ)⁻¹) / (Am - (n : ℝ)⁻¹) * ((P + 1 + (n : ℝ)⁻¹) / (P + 1 - (n : ℝ)⁻¹)) *
        ((Am + 1 + (n : ℝ)⁻¹) / (Am + 1 - (n : ℝ)⁻¹)) := by
    apply mul_le_mul (mul_le_mul_of_nonneg_right f1 hFP) f2 hFA (mul_nonneg hFAm hFP)
  refine le_trans step1 ?_
  -- clear denominators
  have hNh : (n : ℝ) * (n : ℝ)⁻¹ = 1 := mul_inv_cancel₀ hn0.ne'
  have e : ∀ Q : ℝ, 1 ≤ Q → (Q + (n : ℝ)⁻¹) / (Q - (n : ℝ)⁻¹) = ((n : ℝ) * Q + 1) / ((n : ℝ) * Q - 1) := by
    intro Q hQ
    have hd1 : Q - (n : ℝ)⁻¹ ≠ 0 := by linarith
    have hd2 : (n : ℝ) * Q - 1 ≠ 0 := by nlinarith
    rw [div_eq_div_iff hd1 hd2]
    linear_combination (2 * Q) * hNh
  have e2 : (P + 1 - (n : ℝ)⁻¹) / (P + (n : ℝ)⁻¹) = ((n : ℝ) * P + (n : ℝ) - 1) / ((n : ℝ) * P + 1) := by
    have hd1 : P + (n : ℝ)⁻¹ ≠ 0 := by linarith
    have hd2 : (n : ℝ) * P + 1 ≠ 0 := by nlinarith
    rw [div_eq_div_iff hd1 hd2]
    linear_combination (-(2 * P + 1)) * hNh
  rw [e Am hAm1, e (P + 1) (by linarith), e (Am + 1) (by linarith), e2]
  have hNP : 0 < (n : ℝ) * P + 1 := by nlinarith
  have hd1 : 0 < (n : ℝ) * Am - 1 := by nlinarith
  have hd2 : 0 < (n : ℝ) * (P + 1) - 1 := by nlinarith
  have hd3 : 0 < (n : ℝ) * (Am + 1) - 1 := by nlinarith
  rw [div_mul_div_comm, div_mul_div_comm, div_le_div_iff₀ (by positivity) hNP]
  have := three_move_poly (n : ℝ) P hN6 hP
  rw [hAm]
  linarith


theorem one_le_cast_add_one (m : ℕ) : (1 : ℝ) ≤ (m : ℝ) + 1 := by
  have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m); linarith

/-- `g n m = ∏_{r=1}^{m} (r + 1/n)/(r − 1/n)`. -/
noncomputable def g (n : ℕ) (m : ℕ) : ℝ :=
  ∏ r ∈ Finset.range m, (((r : ℝ) + 1) + (n : ℝ)⁻¹) / (((r : ℝ) + 1) - (n : ℝ)⁻¹)

theorem factor_ge_one {n : ℕ} [Fact (2 ≤ n)] {Q : ℝ} (hQ : 1 ≤ Q) : 1 ≤ (Q + (n : ℝ)⁻¹) / (Q - (n : ℝ)⁻¹) := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hh0 : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr hn0
  have hhle : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  rw [le_div_iff₀ (by linarith)]; linarith

theorem g_succ {n : ℕ} (m : ℕ) : g n (m + 1) = g n m * ((((m : ℝ) + 1) + (n : ℝ)⁻¹) / (((m : ℝ) + 1) - (n : ℝ)⁻¹)) := by
  unfold g; rw [Finset.prod_range_succ]

theorem g_one_le {n : ℕ} [Fact (2 ≤ n)] (m : ℕ) : 1 ≤ g n m := by
  induction m with
  | zero => simp [g]
  | succ m ih =>
    rw [g_succ]
    have := factor_ge_one (n := n) (one_le_cast_add_one m)
    nlinarith

theorem g_mono {n : ℕ} [Fact (2 ≤ n)] {a b : ℕ} (hab : a ≤ b) : g n a ≤ g n b := by
  induction b with
  | zero => have : a = 0 := by omega
            subst this; exact le_rfl
  | succ b ih =>
    rcases Nat.lt_or_ge a (b + 1) with h | h
    · rw [g_succ]
      have h1 := ih (by omega)
      have h2 := factor_ge_one (n := n) (one_le_cast_add_one b)
      have h3 := g_one_le (n := n) b
      nlinarith
    · have : a = b + 1 := by omega
      subst this; exact le_rfl

theorem g_balance_aux {n : ℕ} [Fact (2 ≤ n)] (m : ℕ) :
    ∀ d a b : ℕ, b = a + d → a + b ≤ 2 * m → g n a * g n b ≤ g n m * g n m := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro a b hb hsum
    rcases Nat.lt_or_ge m b with hmb | hbm
    · -- b > m, so a < m and d ≥ 2
      have hd2 : 2 ≤ d := by omega
      obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      have hfac : ((((b' : ℕ) : ℝ) + 1) + (n : ℝ)⁻¹) / ((((b' : ℕ) : ℝ) + 1) - (n : ℝ)⁻¹) ≤
          ((((a : ℕ) : ℝ) + 1) + (n : ℝ)⁻¹) / ((((a : ℕ) : ℝ) + 1) - (n : ℝ)⁻¹) :=
        lap_factor_antitone_real (one_le_cast_add_one a) (by
          have : a ≤ b' := by omega
          exact_mod_cast Nat.add_le_add_right this 1)
      have hga := g_one_le (n := n) a
      have hgb := g_one_le (n := n) b'
      calc g n a * g n (b' + 1) = g n a * g n b' * ((((b' : ℝ) + 1) + (n : ℝ)⁻¹) / (((b' : ℝ) + 1) - (n : ℝ)⁻¹)) := by
            rw [g_succ]; ring
        _ ≤ g n a * g n b' * ((((a : ℝ) + 1) + (n : ℝ)⁻¹) / (((a : ℝ) + 1) - (n : ℝ)⁻¹)) :=
            mul_le_mul_of_nonneg_left hfac (by nlinarith)
        _ = g n (a + 1) * g n b' := by rw [g_succ]; ring
        _ ≤ g n m * g n m := ih (d - 2) (by omega) (a + 1) b' (by omega) (by omega)
    · have h1 := g_mono (n := n) (show a ≤ m by omega)
      have h2 := g_mono (n := n) hbm
      have h3 := g_one_le (n := n) a
      have h4 := g_one_le (n := n) b
      nlinarith

theorem g_balance {n : ℕ} [Fact (2 ≤ n)] {a b m : ℕ} (h : a + b ≤ 2 * m) : g n a * g n b ≤ g n m * g n m := by
  rcases le_total a b with hab | hab
  · exact g_balance_aux m (b - a) a b (by omega) h
  · rw [mul_comm]; exact g_balance_aux m (a - b) b a (by omega) (by omega)

/-- **Sorted laps.**  Distinct laps `≥ 1` give a lap-factor product at most `g` of their number. -/
theorem sorted_lap_prod {n : ℕ} [Fact (2 ≤ n)] {ι : Type*} (q : ι → ℤ) (k : ℕ) :
    ∀ S : Finset ι, S.card = k → (∀ i ∈ S, 1 ≤ q i) → Set.InjOn q S →
      ∏ i ∈ S, (((q i : ℝ)) + (n : ℝ)⁻¹) / (((q i : ℝ)) - (n : ℝ)⁻¹) ≤ g n k := by
  classical
  induction k with
  | zero =>
    intro S hS _ _
    rw [Finset.card_eq_zero] at hS; subst hS; simp [g]
  | succ k ih =>
    intro S hS hq hinj
    have hne : S.Nonempty := by rw [← Finset.card_pos, hS]; omega
    obtain ⟨i, hi, himax⟩ := S.exists_max_image q hne
    -- the largest lap is at least `k + 1`
    have hbig : ((k : ℤ) + 1) ≤ q i := by
      have hsub : S.image q ⊆ Finset.Icc 1 (q i) := by
        intro z hz
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
        exact Finset.mem_Icc.mpr ⟨hq j hj, himax j hj⟩
      have hc := Finset.card_le_card hsub
      rw [Finset.card_image_of_injOn hinj, hS, Int.card_Icc] at hc
      have : (0 : ℤ) ≤ q i + 1 - 1 := by have := hq i hi; omega
      omega
    have herase : (S.erase i).card = k := by rw [Finset.card_erase_of_mem hi, hS]; rfl
    have hrest := ih (S.erase i) herase (fun j hj => hq j (Finset.mem_of_mem_erase hj))
      (hinj.mono (fun j hj => Finset.mem_of_mem_erase hj))
    rw [← Finset.mul_prod_erase S _ hi, g_succ]
    have hfac : (((q i : ℝ)) + (n : ℝ)⁻¹) / (((q i : ℝ)) - (n : ℝ)⁻¹) ≤
        (((k : ℝ) + 1) + (n : ℝ)⁻¹) / (((k : ℝ) + 1) - (n : ℝ)⁻¹) :=
      lap_factor_antitone_real (one_le_cast_add_one k) (by exact_mod_cast hbig)
    have hrest0 : 0 ≤ ∏ j ∈ S.erase i, (((q j : ℝ)) + (n : ℝ)⁻¹) / (((q j : ℝ)) - (n : ℝ)⁻¹) := by
      apply Finset.prod_nonneg
      intro j hj
      have hqj : (1 : ℝ) ≤ q j := by exact_mod_cast hq j (Finset.mem_of_mem_erase hj)
      exact le_trans zero_le_one (factor_ge_one hqj)
    have hF0 : 0 ≤ (((k : ℝ) + 1) + (n : ℝ)⁻¹) / (((k : ℝ) + 1) - (n : ℝ)⁻¹) :=
      le_trans zero_le_one (factor_ge_one (one_le_cast_add_one k))
    calc (((q i : ℝ)) + (n : ℝ)⁻¹) / (((q i : ℝ)) - (n : ℝ)⁻¹) *
          ∏ j ∈ S.erase i, (((q j : ℝ)) + (n : ℝ)⁻¹) / (((q j : ℝ)) - (n : ℝ)⁻¹)
        ≤ (((k : ℝ) + 1) + (n : ℝ)⁻¹) / (((k : ℝ) + 1) - (n : ℝ)⁻¹) * g n k :=
          mul_le_mul hfac hrest hrest0 hF0
      _ = g n k * ((((k : ℝ) + 1) + (n : ℝ)⁻¹) / (((k : ℝ) + 1) - (n : ℝ)⁻¹)) := by ring

end FourSixAlgebra


/-! ## four differences at every `n ≥ 6` -/

namespace FourDifferencesSix

open ConstructionN MomentIterationN TerminationFour ChainBounds NearestState FewDifferences WordRules FasterMoves
  FourDifferences FourSixAlgebra

/-- The slowest setter does not return across at most `g` moves, `n ≥ 2g + 2`. -/
theorem word_no_slow_return_g {n : ℕ} [Fact (2 ≤ n)] (g : ℕ) (hng : 2 * g + 2 ≤ n) (t s : ℕ → ℝ) (q : ℕ → ℤ)
    (i k : ℕ) (hik : i + 1 < k) (hkg : k ≤ i + g + 1) (htpos : ∀ j, 0 < t j)
    (hspos : ∀ j, i ≤ j → j ≤ k → 0 < s j)
    (hdat : ∀ j, i ≤ j → j < k → |s j * t j - q j| < (n : ℝ)⁻¹ ∧ t (j + 1) = ((q j : ℝ) + (n : ℝ)⁻¹) / s j)
    (hkw : inWay n (s k) (t k)) (hvmin : ∀ j, i < j → j < k → s i ≤ s j) (hsame : s k = s i)
    (hqi : 0 ≤ q i) (hmono : ∀ j j', j ≤ j' → t j ≤ t j') (hstrict : t (i + 1) < t k) : False := by
  set m := k - i - 1 with hm
  have hmk : i + 1 + m = k := by omega
  have hmg : m ≤ g := by omega
  obtain ⟨-, hei⟩ := hdat i le_rfl (by omega)
  have hlap : ∀ j < m, q i + 1 ≤ q (i + 1 + j) := by
    intro j hj
    exact faster_lap_ge' (hspos i le_rfl (by omega)) (hvmin (i + 1 + j) (by omega) (by omega)) hqi hei
      (hmono _ _ (by omega)) (hdat (i + 1 + j) (by omega) (by omega)).1
  apply no_return_after_few_faster (n := n) (hspos i le_rfl (by omega)) hqi g m hmg hng
    (fun j => t (i + 1 + j)) (fun j => q (i + 1 + j)) hei
  · intro j hj
    obtain ⟨hk, he⟩ := hdat (i + 1 + j) (by omega) (by omega)
    have hQ : 1 ≤ q (i + 1 + j) := by have := hlap j hj; omega
    show t (i + 1 + (j + 1)) ≤ _
    have e : i + 1 + (j + 1) = i + 1 + j + 1 := by omega
    rw [e, he]
    exact (move_growth (hspos _ (by omega) (by omega)) (htpos _) hQ hk).le
  · exact hlap
  · exact fun j => htpos _
  · show t (i + 1 + 0) < t (i + 1 + m); rw [add_zero, hmk]; exact hstrict
  · show inWay n (s i) (t (i + 1 + m)); rw [hmk, ← hsame]; exact hkw

/-- **Three moves `y z y` cannot carry the slowest setter back** (`n ≥ 6`). -/
theorem word_no_slow_return_three {n : ℕ} [Fact (2 ≤ n)] (hn6 : 6 ≤ n) (t s : ℕ → ℝ) (q : ℕ → ℤ) (i : ℕ)
    (htpos : ∀ j, 0 < t j) (hspos : ∀ j, i ≤ j → j ≤ i + 4 → 0 < s j)
    (hdat : ∀ j, i ≤ j → j < i + 4 → |s j * t j - q j| < (n : ℝ)⁻¹ ∧ t (j + 1) = ((q j : ℝ) + (n : ℝ)⁻¹) / s j)
    (hw4 : inWay n (s (i + 4)) (t (i + 4)))
    (hvmin : ∀ j, i < j → j < i + 4 → s i ≤ s j) (hsame : s (i + 4) = s i) (hy : s (i + 3) = s (i + 1))
    (hqi : 0 ≤ q i) (hmono : ∀ j j', j ≤ j' → t j ≤ t j') (hlt : ∀ j, i ≤ j → j < i + 4 → t j < t (j + 1)) :
    False := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hh0 : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr hn0
  have hhle : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
  have hN6 : (6 : ℝ) ≤ n := by exact_mod_cast hn6
  have k0 : |s i * t i - q i| < (n : ℝ)⁻¹ := (hdat i le_rfl (by omega)).1
  have e0 : t (i + 1) = ((q i : ℝ) + (n : ℝ)⁻¹) / s i := (hdat i le_rfl (by omega)).2
  have k1 : |s (i + 1) * t (i + 1) - q (i + 1)| < (n : ℝ)⁻¹ := (hdat (i + 1) (by omega) (by omega)).1
  have e1 : t (i + 2) = ((q (i + 1) : ℝ) + (n : ℝ)⁻¹) / s (i + 1) := (hdat (i + 1) (by omega) (by omega)).2
  have k2 : |s (i + 2) * t (i + 2) - q (i + 2)| < (n : ℝ)⁻¹ := (hdat (i + 2) (by omega) (by omega)).1
  have e2 : t (i + 3) = ((q (i + 2) : ℝ) + (n : ℝ)⁻¹) / s (i + 2) := (hdat (i + 2) (by omega) (by omega)).2
  have k3 : |s (i + 3) * t (i + 3) - q (i + 3)| < (n : ℝ)⁻¹ := (hdat (i + 3) (by omega) (by omega)).1
  have e3 : t (i + 4) = ((q (i + 3) : ℝ) + (n : ℝ)⁻¹) / s (i + 3) := (hdat (i + 3) (by omega) (by omega)).2
  have hv0 := hspos i le_rfl (by omega)
  have hy0 := hspos (i + 1) (by omega) (by omega)
  have hz0 := hspos (i + 2) (by omega) (by omega)
  have hq1 : q i + 1 ≤ q (i + 1) :=
    faster_lap_ge' hv0 (hvmin (i + 1) (by omega) (by omega)) hqi e0 (hmono _ _ (by omega)) k1
  have hq2 : q i + 1 ≤ q (i + 2) :=
    faster_lap_ge' hv0 (hvmin (i + 2) (by omega) (by omega)) hqi e0 (hmono _ _ (by omega)) k2
  have hq1nn : 0 ≤ q (i + 1) := by omega
  have k3' : |s (i + 1) * t (i + 3) - q (i + 3)| < (n : ℝ)⁻¹ := by rw [← hy]; exact k3
  have hq3 : q (i + 1) + 1 ≤ q (i + 3) :=
    faster_lap_ge' hy0 le_rfl hq1nn e1 (hmono _ _ (by omega)) k3'
  have hwy : inWay n (s (i + 1)) (t (i + 3)) := inWay_of_near k3'
  have r := return_lemma (n := n) (x := s (i + 1)) (y := s (i + 2)) (P := q (i + 1)) (Q := q (i + 2)) hy0 hz0
    hq1nn (by rw [← e1]; exact k2) (by rw [← e1, ← e2]; exact hlt (i + 2) (by omega) (by omega))
    (by rw [← e2]; exact hwy)
  have hn6z : (6 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn6
  have hint : q (i + 2) * ((n : ℤ) - 2) ≤ 2 * q (i + 1) := by
    have : q (i + 2) * ((n : ℤ) - 2) < 2 * q (i + 1) + 1 := r
    omega
  have hPr : (0 : ℝ) ≤ (q i : ℝ) := by exact_mod_cast hqi
  have hA : ((q i : ℝ) + 1) * ((n : ℝ) - 2) ≤ 2 * (q (i + 1) : ℝ) := by
    have h1 : ((q (i + 2) * ((n : ℤ) - 2) : ℤ) : ℝ) ≤ ((2 * q (i + 1) : ℤ) : ℝ) := by exact_mod_cast hint
    push_cast at h1
    have h2 : (q i : ℝ) + 1 ≤ (q (i + 2) : ℝ) := by exact_mod_cast hq2
    have hn2 : (0 : ℝ) ≤ (n : ℝ) - 2 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right h2 hn2]
  have hbound := three_move_bound hn6 hPr hA
  have hq11 : (1 : ℤ) ≤ q (i + 1) := by omega
  have hA1 : (1 : ℝ) ≤ (q (i + 1) : ℝ) := by exact_mod_cast hq11
  have f2 : ((q (i + 2) : ℝ) + (n : ℝ)⁻¹) / ((q (i + 2) : ℝ) - (n : ℝ)⁻¹) ≤
      ((q i : ℝ) + 1 + (n : ℝ)⁻¹) / ((q i : ℝ) + 1 - (n : ℝ)⁻¹) :=
    lap_factor_antitone_real (by linarith) (by exact_mod_cast hq2)
  have f3 : ((q (i + 3) : ℝ) + (n : ℝ)⁻¹) / ((q (i + 3) : ℝ) - (n : ℝ)⁻¹) ≤
      ((q (i + 1) : ℝ) + 1 + (n : ℝ)⁻¹) / ((q (i + 1) : ℝ) + 1 - (n : ℝ)⁻¹) :=
    lap_factor_antitone_real (by linarith) (by exact_mod_cast hq3)
  have g1 := move_growth hy0 (htpos (i + 1)) (by omega : (1 : ℤ) ≤ q (i + 1)) k1
  have g2 := move_growth hz0 (htpos (i + 2)) (by omega : (1 : ℤ) ≤ q (i + 2)) k2
  have g3 := move_growth hy0 (htpos (i + 3)) (by omega : (1 : ℤ) ≤ q (i + 3)) k3'
  have e3' : t (i + 4) = ((q (i + 3) : ℝ) + (n : ℝ)⁻¹) / s (i + 1) := by rw [← hy]; exact e3
  rw [← e1] at g1; rw [← e2] at g2; rw [← e3'] at g3
  set F1 := ((q (i + 1) : ℝ) + (n : ℝ)⁻¹) / ((q (i + 1) : ℝ) - (n : ℝ)⁻¹) with hF1
  set F2 := ((q (i + 2) : ℝ) + (n : ℝ)⁻¹) / ((q (i + 2) : ℝ) - (n : ℝ)⁻¹) with hF2
  set F3 := ((q (i + 3) : ℝ) + (n : ℝ)⁻¹) / ((q (i + 3) : ℝ) - (n : ℝ)⁻¹) with hF3
  set G2 := ((q i : ℝ) + 1 + (n : ℝ)⁻¹) / ((q i : ℝ) + 1 - (n : ℝ)⁻¹) with hG2
  set G3 := ((q (i + 1) : ℝ) + 1 + (n : ℝ)⁻¹) / ((q (i + 1) : ℝ) + 1 - (n : ℝ)⁻¹) with hG3
  set R := ((q i : ℝ) + 1 - (n : ℝ)⁻¹) / ((q i : ℝ) + (n : ℝ)⁻¹) with hR
  have hF1 : 0 ≤ F1 := le_trans zero_le_one (factor_ge_one hA1)
  have hF2 : 0 ≤ F2 := le_trans zero_le_one (factor_ge_one (by
    have : (1 : ℤ) ≤ q (i + 2) := by omega
    exact_mod_cast this))
  have hF3 : 0 ≤ F3 := le_trans zero_le_one (factor_ge_one (by
    have : (1 : ℤ) ≤ q (i + 3) := by omega
    exact_mod_cast this))
  have hG2 : 0 ≤ G2 := le_trans zero_le_one (factor_ge_one (by linarith))
  have hwv : inWay n (s i) (t (i + 4)) := by rw [← hsame]; exact hw4
  have hlt14 : t (i + 1) < t (i + 4) :=
    lt_of_lt_of_le (hlt (i + 1) (by omega) (by omega)) (hmono _ _ (by omega))
  have hr := return_growth hv0 hqi e0 hlt14 hwv
  have ht1 := htpos (i + 1)
  have c1 : t (i + 4) ≤ F3 * (F2 * (F1 * t (i + 1))) := by
    have a1 : t (i + 3) ≤ F2 * (F1 * t (i + 1)) :=
      le_trans g2.le (mul_le_mul_of_nonneg_left g1.le hF2)
    exact le_trans g3.le (mul_le_mul_of_nonneg_left a1 hF3)
  have c2 : F3 * (F2 * (F1 * t (i + 1))) ≤ G3 * (G2 * (F1 * t (i + 1))) := by
    have hFt : 0 ≤ F1 * t (i + 1) := mul_nonneg hF1 ht1.le
    exact mul_le_mul f3 (mul_le_mul_of_nonneg_right f2 hFt) (mul_nonneg hF2 hFt) (le_trans hF3 f3)
  have c3 : G3 * (G2 * (F1 * t (i + 1))) = (F1 * G2 * G3) * t (i + 1) := by ring
  have c4 : (F1 * G2 * G3) * t (i + 1) ≤ R * t (i + 1) := mul_le_mul_of_nonneg_right hbound ht1.le
  linarith


theorem factor_le_sixth {n : ℕ} [Fact (2 ≤ n)] (hn6 : 6 ≤ n) {Q : ℝ} (hQ : 1 ≤ Q) :
    (Q + (n : ℝ)⁻¹) / (Q - (n : ℝ)⁻¹) ≤ (Q + 1 / 6) / (Q - 1 / 6) := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hN6 : (6 : ℝ) ≤ n := by exact_mod_cast hn6
  have hh0 : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr hn0
  have hhle : (n : ℝ)⁻¹ ≤ 6⁻¹ := inv_anti₀ (by norm_num) hN6
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

theorem g_count_bound {n : ℕ} [Fact (2 ≤ n)] (hn6 : 6 ≤ n) : g n 1 * (g n 3 * g n 3) ≤ (n : ℝ) - 1 := by
  have hN6 : (6 : ℝ) ≤ n := by exact_mod_cast hn6
  have f : ∀ r : ℕ, r ≤ 2 → 0 ≤ (((r : ℝ) + 1) + (n : ℝ)⁻¹) / (((r : ℝ) + 1) - (n : ℝ)⁻¹) ∧
      (((r : ℝ) + 1) + (n : ℝ)⁻¹) / (((r : ℝ) + 1) - (n : ℝ)⁻¹) ≤ (((r : ℝ) + 1) + 1 / 6) / (((r : ℝ) + 1) - 1 / 6) :=
    fun r _ => ⟨le_trans zero_le_one (factor_ge_one (one_le_cast_add_one r)), factor_le_sixth hn6 (one_le_cast_add_one r)⟩
  have g1 : g n 1 ≤ 7 / 5 := by
    have h := (f 0 (by norm_num)).2
    simp only [g, Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    norm_num at h ⊢; linarith
  have g3 : g n 3 ≤ 1729 / 935 := by
    obtain ⟨p0, h0⟩ := f 0 (by norm_num)
    obtain ⟨p1, h1⟩ := f 1 (by norm_num)
    obtain ⟨p2, h2⟩ := f 2 (by norm_num)
    simp only [g, Finset.prod_range_succ, Finset.prod_range_zero, one_mul]
    norm_num at h0 h1 h2 p0 p1 p2 ⊢
    calc ((1 + (n : ℝ)⁻¹) / (1 - (n : ℝ)⁻¹)) * ((2 + (n : ℝ)⁻¹) / (2 - (n : ℝ)⁻¹)) *
          ((3 + (n : ℝ)⁻¹) / (3 - (n : ℝ)⁻¹))
        ≤ (7 / 5) * (13 / 11) * (19 / 17) := by
          apply mul_le_mul (mul_le_mul (by linarith) (by linarith) p1 (by norm_num)) (by linarith) p2 (by norm_num)
      _ = 1729 / 935 := by norm_num
  have hg1 : 1 ≤ g n 1 := g_one_le 1
  have hg3 : 1 ≤ g n 3 := g_one_le 3
  calc g n 1 * (g n 3 * g n 3) ≤ (7 / 5) * ((1729 / 935) * (1729 / 935)) := by
        apply mul_le_mul g1 (mul_le_mul g3 g3 (by linarith) (by norm_num)) (by nlinarith) (by norm_num)
    _ ≤ 5 := by norm_num
    _ ≤ (n : ℝ) - 1 := by linarith

/-- **Four differences, every `n ≥ 6`: the iteration from the bound stops within seven moves.** -/
theorem four_diffs_stop_ge_six {n : ℕ} [Fact (2 ≤ n)] (hn6 : 6 ≤ n) {ds : Finset ℝ}
    (hpos : ∀ d ∈ ds, 0 < d) (hcard : ds.card ≤ 4) {a : ℝ} (ha : a ∈ ds) (hmin : ∀ d ∈ ds, a ≤ d) :
    move n ds ((move n ds)^[7] (1 / (n * a))) = (move n ds)^[7] (1 / (n * a)) := by
  classical
  have ha0 := hpos a ha
  have hn0 : (0 : ℝ) < n := n_pos
  have hN6 : (6 : ℝ) ≤ n := by exact_mod_cast hn6
  have hh0 : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr hn0
  set b0 := 1 / ((n : ℝ) * a) with hb0
  set t : ℕ → ℝ := fun j => (move n ds)^[j] b0 with htdef
  have htsucc : ∀ j, t (j + 1) = move n ds (t j) := fun j => Function.iterate_succ_apply' _ _ _
  have hb0pos : 0 < b0 := by rw [hb0]; positivity
  have htpos : ∀ j, 0 < t j := fun j => lt_of_lt_of_le hb0pos (iterate_ge (n := n) ds b0 j)
  have htmono : ∀ j j', j ≤ j' → t j ≤ t j' := by
    have : Monotone t := monotone_nat_of_le_succ (fun j => by rw [htsucc]; exact le_move ds _)
    exact fun j j' h => this h
  have hab : a * b0 = (n : ℝ)⁻¹ := by rw [hb0]; field_simp
  have hat : ∀ j, (n : ℝ)⁻¹ ≤ a * t j := by
    intro j
    rw [← hab]; exact mul_le_mul_of_nonneg_left (iterate_ge (n := n) ds b0 j) ha0.le
  show move n ds (t 7) = t 7
  by_contra hne
  have hmoving : ∀ j ≤ 7, move n ds (t j) ≠ t j := by
    intro j hj hfix
    have hst := iterate_stable (n := n) (b := b0) hfix (7 - j)
    have e : j + (7 - j) = 7 := by omega
    rw [e] at hst
    apply hne
    show move n ds ((move n ds)^[7] b0) = (move n ds)^[7] b0
    rw [hst]; exact hfix
  have hex : ∀ j : ℕ, ∃ x : ℝ, ∃ k : ℤ, move n ds (t j) = t j ∨
      (x ∈ ds ∧ |x * t j - k| < (n : ℝ)⁻¹ ∧ t (j + 1) = ((k : ℝ) + (n : ℝ)⁻¹) / x) := by
    intro j
    rcases step_cases (n := n) hpos (t j) with h1 | ⟨x, hx, k, hk, he⟩
    · exact ⟨0, 0, Or.inl h1⟩
    · exact ⟨x, k, Or.inr ⟨hx, hk, by rw [htsucc, he]⟩⟩
  choose s q hsq using hex
  have hD : ∀ j ≤ 7, s j ∈ ds ∧ |s j * t j - q j| < (n : ℝ)⁻¹ ∧ t (j + 1) = ((q j : ℝ) + (n : ℝ)⁻¹) / s j := by
    intro j hj
    rcases hsq j with h1 | h1
    · exact absurd h1 (hmoving j hj)
    · exact h1
  have hdat : ∀ j ≤ 7, |s j * t j - q j| < (n : ℝ)⁻¹ ∧ t (j + 1) = ((q j : ℝ) + (n : ℝ)⁻¹) / s j :=
    fun j hj => ⟨(hD j hj).2.1, (hD j hj).2.2⟩
  have hspos : ∀ j ≤ 7, 0 < s j := fun j hj => hpos _ (hD j hj).1
  have hw : ∀ j ≤ 7, inWay n (s j) (t j) := fun j hj => inWay_of_near (hD j hj).2.1
  have hlt : ∀ j ≤ 7, t j < t (j + 1) := by
    intro j hj
    obtain ⟨-, hk, he⟩ := hD j hj
    have hx0 := hspos j hj
    have h1 : s j * t (j + 1) = q j + (n : ℝ)⁻¹ := by rw [he]; field_simp
    have : s j * t j < s j * t (j + 1) := by rw [h1]; linarith [(abs_lt.mp hk).2]
    exact lt_of_mul_lt_mul_left this hx0.le
  have hadj : ∀ j, j + 1 ≤ 7 → s (j + 1) ≠ s j := by
    intro j hj he
    have hw1 := hw (j + 1) hj
    rw [he, (hD j (by omega)).2.2] at hw1
    exact not_inWay_at_own_opening (hspos j (by omega)) (q j) hw1
  have hq1' : ∀ j ≤ 7, 1 ≤ q j := fun j hj =>
    lap_ge_one (hmin _ (hD j hj).1) (htpos j).le (hat j) (hD j hj).2.1
  have hW2 : ∀ j, j + 3 ≤ 7 → s j = s (j + 2) → s (j + 1) = s (j + 3) → False := by
    intro j hj hA hB
    exact word_no_alternation (n := n) (by omega) t s q j (hspos j (by omega)) (hspos (j + 1) (by omega))
      (by have := hq1' j (by omega); omega) (by have := hq1' (j + 1) (by omega); omega)
      (hD j (by omega)).2.2 (hD (j + 1) (by omega)).2.2 (hD (j + 2) (by omega)).2.2
      (hD (j + 1) (by omega)).2.1 (hD (j + 2) (by omega)).2.1
      (hlt (j + 1) (by omega)) (hlt (j + 2) (by omega)) (hw (j + 3) (by omega)) hA hB
  -- two consecutive setters avoiding `v` in a two-element set force the third
  have htwo : ∀ L, L ≤ 8 → (∀ j < L, s j ≠ a) → ∀ v ∈ ds.erase a, ∀ j, j + 2 < L →
      s j ≠ v → s (j + 1) ≠ v → s (j + 2) ≠ v → s (j + 2) = s j := by
    intro L hL hna v hvX j hj h0 h1 h2
    have hcard2 : ((ds.erase a).erase v).card ≤ 2 := by
      rw [Finset.card_erase_of_mem hvX, Finset.card_erase_of_mem ha]; omega
    have mem : ∀ i, i < L → s i ≠ v → s i ∈ (ds.erase a).erase v := fun i hi hne' =>
      Finset.mem_erase.mpr ⟨hne', Finset.mem_erase.mpr ⟨hna i hi, (hD i (by omega)).1⟩⟩
    have hsub : ({s j, s (j + 1)} : Finset ℝ) ⊆ (ds.erase a).erase v := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact mem j (by omega) h0
      · exact mem (j + 1) (by omega) h1
    have hpair : ({s j, s (j + 1)} : Finset ℝ).card = 2 := Finset.card_pair (Ne.symm (hadj j (by omega)))
    have heq : ({s j, s (j + 1)} : Finset ℝ) = (ds.erase a).erase v :=
      Finset.eq_of_subset_of_card_le hsub (by omega)
    have m2 : s (j + 2) ∈ ({s j, s (j + 1)} : Finset ℝ) := by rw [heq]; exact mem (j + 2) (by omega) h2
    simp only [Finset.mem_insert, Finset.mem_singleton] at m2
    rcases m2 with e | e
    · exact e
    · exact absurd e (hadj (j + 1) (by omega))
  have hblock : ∀ L, L ≤ 8 → (∀ j < L, s j ≠ a) → ∀ v ∈ ds.erase a, ∀ j, j + 3 < L →
      s j ≠ v → s (j + 1) ≠ v → s (j + 2) ≠ v → s (j + 3) ≠ v → False := by
    intro L hL hna v hvX j hj h0 h1 h2 h3
    have hA := htwo L hL hna v hvX j (by omega) h0 h1 h2
    have hB := htwo L hL hna v hvX (j + 1) (by omega) h1 h2 h3
    exact hW2 j (by omega) hA.symm hB.symm
  -- the slowest setter of a prefix sets at most once in it
  have hprefix : ∀ L, L ≤ 8 → (∀ j < L, s j ≠ a) → ∀ j0, j0 < L → (∀ j < L, s j0 ≤ s j) →
      ∀ i k, i < k → k < L → s i = s j0 → s k = s j0 → False := by
    intro L hL hna j0 hj0L hj0min i k hik hkL hi hk
    have hvX : s j0 ∈ ds.erase a := Finset.mem_erase.mpr ⟨hna j0 hj0L, (hD j0 (by omega)).1⟩
    have hex' : ∃ k', i < k' ∧ k' < L ∧ s k' = s j0 := ⟨k, hik, hkL, hk⟩
    set k' := Nat.find hex' with hk'def
    obtain ⟨hik', hk'L, hk'v⟩ := Nat.find_spec hex'
    have hbetween : ∀ j, i < j → j < k' → s j ≠ s j0 := fun j hj1 hj2 hjv =>
      Nat.find_min hex' hj2 ⟨hj1, by omega, hjv⟩
    rcases Nat.lt_or_ge (i + 4) k' with hfar | hnear
    · exact hblock L hL hna (s j0) hvX (i + 1) (by omega) (hbetween _ (by omega) (by omega))
        (hbetween _ (by omega) (by omega)) (hbetween _ (by omega) (by omega)) (hbetween _ (by omega) (by omega))
    · have hik1 : i + 1 < k' := by
        rcases Nat.lt_or_ge (i + 1) k' with h | h
        · exact h
        · exfalso
          have e : k' = i + 1 := by omega
          apply hadj i (by omega)
          rw [← e, hk'v, hi]
      have hvmin' : ∀ j, i < j → j < k' → s i ≤ s j := fun j h1 h2 => by
        rw [hi]; exact hj0min j (by omega)
      rcases Nat.lt_or_ge k' (i + 4) with hk3 | hk4
      · exact word_no_slow_return_g (n := n) 2 (by omega) t s q i k' hik1 (by omega) htpos
          (fun j _ _ => hspos j (by omega)) (fun j _ _ => hdat j (by omega)) (hw k' (by omega))
          hvmin' (by rw [hk'v, hi]) (by have := hq1' i (by omega); omega) htmono
          (lt_of_lt_of_le (hlt (i + 1) (by omega)) (htmono _ _ (by omega)))
      · have hk4' : k' = i + 4 := by omega
        have hy : s (i + 3) = s (i + 1) :=
          htwo L hL hna (s j0) hvX (i + 1) (by omega) (hbetween _ (by omega) (by omega))
            (hbetween _ (by omega) (by omega)) (hbetween _ (by omega) (by omega))
        have hw4 : inWay n (s (i + 4)) (t (i + 4)) := hw (i + 4) (by omega)
        have hsame : s (i + 4) = s i := by rw [← hk4', hk'v, hi]
        exact word_no_slow_return_three (n := n) hn6 t s q i htpos (fun j _ _ => hspos j (by omega))
          (fun j _ _ => hdat j (by omega)) hw4
          (fun j h1 h2 => by rw [hi]; exact hj0min j (by omega)) hsame hy
          (by have := hq1' i (by omega); omega) htmono (fun j _ _ => hlt j (by omega))
  -- product recurrence along the chain
  have hrec : ∀ j, j ≤ 8 → a * t j ≤
      (n : ℝ)⁻¹ * ∏ i ∈ Finset.range j, (((q i : ℝ)) + (n : ℝ)⁻¹) / (((q i : ℝ)) - (n : ℝ)⁻¹) := by
    intro j
    induction j with
    | zero => intro _; rw [Finset.prod_range_zero, mul_one]; exact le_of_eq hab
    | succ j ih =>
      intro hj
      have ih' := ih (by omega)
      obtain ⟨-, hk, he⟩ := hD j (by omega)
      have hg := move_growth (hspos j (by omega)) (htpos j) (hq1' j (by omega)) hk
      rw [← he] at hg
      rw [Finset.prod_range_succ]
      have hqj : (1 : ℝ) ≤ q j := by exact_mod_cast hq1' j (by omega)
      have hF := le_trans zero_le_one (factor_ge_one (n := n) hqj)
      have h1 := mul_le_mul_of_nonneg_left hg.le ha0.le
      have h3 := mul_le_mul_of_nonneg_left ih' hF
      calc a * t (j + 1) ≤ a * ((((q j : ℝ)) + (n : ℝ)⁻¹) / (((q j : ℝ)) - (n : ℝ)⁻¹) * t j) := h1
        _ = (((q j : ℝ)) + (n : ℝ)⁻¹) / (((q j : ℝ)) - (n : ℝ)⁻¹) * (a * t j) := by ring
        _ ≤ _ := h3
        _ = _ := by ring
  -- laps increase along one runner's moves
  have hlapinc : ∀ i i', i < i' → i' ≤ 7 → s i = s i' → q i < q i' := by
    intro i i' hii hi7 hs
    obtain ⟨-, -, he⟩ := hD i (by omega)
    obtain ⟨-, hk', -⟩ := hD i' hi7
    have hx0 := hspos i (by omega)
    have h1 : t (i + 1) ≤ t i' := htmono _ _ (by omega)
    have h2 : s i * t (i + 1) = q i + (n : ℝ)⁻¹ := by rw [he]; field_simp
    have h3 : s i * t (i + 1) ≤ s i * t i' := mul_le_mul_of_nonneg_left h1 hx0.le
    rw [hs] at h2 h3
    have h4 := (abs_lt.mp hk').2
    have : (q i : ℝ) < q i' := by linarith
    exact_mod_cast this
  -- the nearest runner is clear at iterates 0..7
  have hclear : ∀ j, j ≤ 7 → ¬ inWay n a (t j) := by
    intro j
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj hwa
      have hna : ∀ i < j, s i ≠ a := fun i hi he => ih i hi (by omega) (he ▸ hw i (by omega))
      rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · subst hj0
        have e : t 0 = ((0 : ℤ) + (n : ℝ)⁻¹) / a := by
          show b0 = _; rw [hb0, Int.cast_zero, zero_add]; field_simp
        rw [e] at hwa
        exact not_inWay_at_own_opening ha0 0 hwa
      · obtain ⟨j0, hj0, hj0min⟩ := (Finset.range j).exists_min_image s ⟨0, Finset.mem_range.mpr hjpos⟩
        have hj0' : j0 < j := Finset.mem_range.mp hj0
        have hmin' : ∀ i < j, s j0 ≤ s i := fun i hi => hj0min i (Finset.mem_range.mpr hi)
        have honce := hprefix j (by omega) hna j0 hj0' hmin'
        have hvX : s j0 ∈ ds.erase a := Finset.mem_erase.mpr ⟨hna j0 hj0', (hD j0 (by omega)).1⟩
        have hmaps : ∀ i ∈ Finset.range j, s i ∈ ds.erase a := fun i hi =>
          Finset.mem_erase.mpr ⟨hna i (Finset.mem_range.mp hi), (hD i (by have := Finset.mem_range.mp hi; omega)).1⟩
        have hprod : ∏ i ∈ Finset.range j, (((q i : ℝ)) + (n : ℝ)⁻¹) / (((q i : ℝ)) - (n : ℝ)⁻¹) =
            ∏ x ∈ ds.erase a, ∏ i ∈ (Finset.range j).filter (fun i => s i = x),
              (((q i : ℝ)) + (n : ℝ)⁻¹) / (((q i : ℝ)) - (n : ℝ)⁻¹) :=
          (Finset.prod_fiberwise_of_maps_to hmaps _).symm
        have hfib : ∀ x, ∏ i ∈ (Finset.range j).filter (fun i => s i = x),
            (((q i : ℝ)) + (n : ℝ)⁻¹) / (((q i : ℝ)) - (n : ℝ)⁻¹) ≤ g n ((Finset.range j).filter (fun i => s i = x)).card := by
          intro x
          apply sorted_lap_prod q _ _ rfl
          · intro i hi
            have := (Finset.mem_filter.mp hi).1
            exact hq1' i (by have := Finset.mem_range.mp this; omega)
          · intro i hi i' hi' hqq
            obtain ⟨hir, hix⟩ := Finset.mem_filter.mp hi
            obtain ⟨hir', hix'⟩ := Finset.mem_filter.mp hi'
            have hir2 := Finset.mem_range.mp hir
            have hir2' := Finset.mem_range.mp hir'
            by_contra hne'
            rcases Nat.lt_or_gt_of_ne hne' with h | h
            · exact absurd hqq (ne_of_lt (hlapinc i i' h (by omega) (hix.trans hix'.symm)))
            · exact absurd hqq.symm (ne_of_lt (hlapinc i' i h (by omega) (hix'.trans hix.symm)))
        have hsumcard : ∑ x ∈ ds.erase a, ((Finset.range j).filter (fun i => s i = x)).card = j := by
          rw [← Finset.card_eq_sum_card_fiberwise hmaps, Finset.card_range]
        have hvcard : ((Finset.range j).filter (fun i => s i = s j0)).card ≤ 1 := by
          rw [Finset.card_le_one]
          intro i hi i' hi'
          obtain ⟨hir, hix⟩ := Finset.mem_filter.mp hi
          obtain ⟨hir', hix'⟩ := Finset.mem_filter.mp hi'
          by_contra hne'
          rcases Nat.lt_or_gt_of_ne hne' with h | h
          · exact honce i i' h (Finset.mem_range.mp hir') hix hix'
          · exact honce i' i h (Finset.mem_range.mp hir) hix' hix
        have hgnonneg : ∀ m, 0 ≤ g n m := fun m => le_trans zero_le_one (g_one_le m)
        have hfibnonneg : ∀ x, 0 ≤ ∏ i ∈ (Finset.range j).filter (fun i => s i = x),
            (((q i : ℝ)) + (n : ℝ)⁻¹) / (((q i : ℝ)) - (n : ℝ)⁻¹) := by
          intro x; apply Finset.prod_nonneg; intro i hi
          have := (Finset.mem_filter.mp hi).1
          have hqi : (1 : ℝ) ≤ q i := by exact_mod_cast hq1' i (by have := Finset.mem_range.mp this; omega)
          exact le_trans zero_le_one (factor_ge_one hqi)
        set c : ℝ → ℕ := fun x => ((Finset.range j).filter (fun i => s i = x)).card with hcdef
        have hsplit := Finset.add_sum_erase (ds.erase a) c hvX
        have hothers : ∑ x ∈ (ds.erase a).erase (s j0), c x ≤ 6 := by
          have h1 : 1 ≤ c (s j0) := by
            rw [hcdef]; apply Finset.card_pos.mpr
            exact ⟨j0, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj0', rfl⟩⟩
          have h2 : c (s j0) + ∑ x ∈ (ds.erase a).erase (s j0), c x = j := by rw [hsplit, hcdef]; exact hsumcard
          omega
        have hc2 : ((ds.erase a).erase (s j0)).card ≤ 2 := by
          rw [Finset.card_erase_of_mem hvX, Finset.card_erase_of_mem ha]; omega
        have hrest : ∏ x ∈ (ds.erase a).erase (s j0), g n (c x) ≤ g n 3 * g n 3 := by
          rcases Nat.lt_or_ge ((ds.erase a).erase (s j0)).card 2 with hlt2 | hge2
          · rcases Nat.lt_or_ge ((ds.erase a).erase (s j0)).card 1 with hlt1 | hge1
            · have hemp : (ds.erase a).erase (s j0) = ∅ := Finset.card_eq_zero.mp (by omega)
              rw [hemp, Finset.prod_empty]
              nlinarith [g_one_le (n := n) 3]
            · obtain ⟨x1, hx1⟩ := Finset.card_eq_one.mp (by omega : ((ds.erase a).erase (s j0)).card = 1)
              rw [hx1, Finset.prod_singleton]
              have hs1 : c x1 ≤ 6 := by
                have := hothers; rw [hx1, Finset.sum_singleton] at this; exact this
              have hb := g_balance (n := n) (a := c x1) (b := 0) (m := 3) (by omega)
              have hg0 : g n 0 = 1 := by simp [g]
              rw [hg0, mul_one] at hb; exact hb
          · obtain ⟨x1, x2, hx12, hx⟩ := Finset.card_eq_two.mp (by omega : ((ds.erase a).erase (s j0)).card = 2)
            rw [hx, Finset.prod_pair hx12]
            have hs12 : c x1 + c x2 ≤ 6 := by
              have := hothers; rw [hx, Finset.sum_pair hx12] at this; exact this
            exact g_balance (by omega)
        have hbound : ∏ i ∈ Finset.range j, (((q i : ℝ)) + (n : ℝ)⁻¹) / (((q i : ℝ)) - (n : ℝ)⁻¹) ≤
            g n 1 * (g n 3 * g n 3) := by
          rw [hprod, ← Finset.mul_prod_erase (ds.erase a) _ hvX]
          have h1 : ∏ i ∈ (Finset.range j).filter (fun i => s i = s j0),
              (((q i : ℝ)) + (n : ℝ)⁻¹) / (((q i : ℝ)) - (n : ℝ)⁻¹) ≤ g n 1 :=
            le_trans (hfib (s j0)) (g_mono hvcard)
          have h2 : ∏ x ∈ (ds.erase a).erase (s j0), ∏ i ∈ (Finset.range j).filter (fun i => s i = x),
              (((q i : ℝ)) + (n : ℝ)⁻¹) / (((q i : ℝ)) - (n : ℝ)⁻¹) ≤ g n 3 * g n 3 :=
            le_trans (Finset.prod_le_prod (fun x _ => hfibnonneg x) (fun x _ => hfib x)) hrest
          exact mul_le_mul h1 h2 (Finset.prod_nonneg (fun x _ => hfibnonneg x)) (hgnonneg 1)
        have hcount := g_count_bound (n := n) hn6
        have hat_j := hrec j (by omega)
        have hup : a * t j ≤ 1 - (n : ℝ)⁻¹ := by
          have h1 : (n : ℝ)⁻¹ * ∏ i ∈ Finset.range j, (((q i : ℝ)) + (n : ℝ)⁻¹) / (((q i : ℝ)) - (n : ℝ)⁻¹) ≤
              (n : ℝ)⁻¹ * ((n : ℝ) - 1) := mul_le_mul_of_nonneg_left (le_trans hbound hcount) hh0.le
          have h2 : (n : ℝ)⁻¹ * ((n : ℝ) - 1) = 1 - (n : ℝ)⁻¹ := by field_simp
          linarith
        exact nearest_clear_general (hat j) hup hwa
  -- the whole eight moves
  have hna8 : ∀ j < 8, s j ≠ a := fun j hj he => hclear j (by omega) (he ▸ hw j (by omega))
  obtain ⟨j0, hj0, hj0min⟩ := (Finset.range 8).exists_min_image s ⟨0, by simp⟩
  have hj0' : j0 < 8 := Finset.mem_range.mp hj0
  have hmin8 : ∀ j < 8, s j0 ≤ s j := fun j hj => hj0min j (Finset.mem_range.mpr hj)
  have honce8 := hprefix 8 le_rfl hna8 j0 hj0' hmin8
  have hvX : s j0 ∈ ds.erase a := Finset.mem_erase.mpr ⟨hna8 j0 hj0', (hD j0 (by omega)).1⟩
  have hnot : ∀ j < 8, j ≠ j0 → s j ≠ s j0 := by
    intro j hj hne' hjv
    rcases Nat.lt_or_gt_of_ne hne' with h | h
    · exact honce8 j j0 h hj0' hjv rfl
    · exact honce8 j0 j h hj rfl hjv
  rcases Nat.lt_or_ge j0 4 with h | h
  · exact hblock 8 le_rfl hna8 (s j0) hvX 4 (by omega) (hnot 4 (by omega) (by omega))
      (hnot 5 (by omega) (by omega)) (hnot 6 (by omega) (by omega)) (hnot 7 (by omega) (by omega))
  · exact hblock 8 le_rfl hna8 (s j0) hvX 0 (by omega) (hnot 0 (by omega) (by omega))
      (hnot 1 (by omega) (by omega)) (hnot 2 (by omega) (by omega)) (hnot 3 (by omega) (by omega))

end FourDifferencesSix



/-! ## the slowest-setter recursion: any number of differences

In a run of consecutive moves whose setters lie in a set `S` of `r` runners, take the slowest setter `v` of the run.
Between two of its settings the moves are set by the other `≤ r − 1` runners, all faster than `v`; if that gap has at
most `g` moves, `v` cannot be back in the way when `n ≥ 2g + 2` (`word_no_slow_return_g`).  By induction on `r`, when
`2^r ≤ n` a run has at most `2^r − 1` moves (`run_length_le`).  With the nearest runner clear for the first `n − 1` moves
(`n ≥ 9`), a subject with `k` differences stops within `2^(k−1) − 1` moves whenever `2^(k−1) ≤ n`
(`stops_slowest_recursion`). -/

namespace SlowestRecursion

open ConstructionN MomentIterationN TerminationFour ChainBounds NearestState FewDifferences WordRules FasterMoves
  FourDifferences FourDifferencesSix

/-- **Runs of moves set by `r` runners have at most `2^r − 1` moves, when `2^r ≤ n`.** -/
theorem run_length_le {n : ℕ} [Fact (2 ≤ n)] (t s : ℕ → ℝ) (q : ℕ → ℤ) (N : ℕ)
    (htpos : ∀ j, 0 < t j) (hmono : ∀ j j', j ≤ j' → t j ≤ t j')
    (hspos : ∀ j < N, 0 < s j)
    (hdat : ∀ j < N, |s j * t j - q j| < (n : ℝ)⁻¹ ∧ t (j + 1) = ((q j : ℝ) + (n : ℝ)⁻¹) / s j)
    (hw : ∀ j < N, inWay n (s j) (t j)) (hq0 : ∀ j < N, 0 ≤ q j)
    (hadj : ∀ j, j + 1 < N → s (j + 1) ≠ s j) (hlt : ∀ j < N, t j < t (j + 1)) :
    ∀ r : ℕ, 2 ^ r ≤ n → ∀ S : Finset ℝ, S.card ≤ r → ∀ i L : ℕ, i + L ≤ N →
      (∀ j, i ≤ j → j < i + L → s j ∈ S) → L ≤ 2 ^ r - 1 := by
  classical
  intro r
  induction r with
  | zero =>
    intro _ S hS i L hiL hmem
    have hS0 : S = ∅ := Finset.card_eq_zero.mp (by omega)
    rcases Nat.eq_zero_or_pos L with h | h
    · simp [h]
    · exact absurd (hmem i le_rfl (by omega)) (by rw [hS0]; exact Finset.notMem_empty _)
  | succ r ih =>
    intro hn S hS i L hiL hmem
    have hpow : 2 ^ (r + 1) = 2 ^ r * 2 := pow_succ 2 r
    have hpos1 : 1 ≤ 2 ^ r := Nat.one_le_two_pow
    have hn' : 2 ^ r ≤ n := by omega
    rcases Nat.eq_zero_or_pos L with hL | hL
    · omega
    obtain ⟨j0, hj0, hj0min⟩ := (Finset.Ico i (i + L)).exists_min_image s ⟨i, Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩⟩
    obtain ⟨hij0, hj0L⟩ := Finset.mem_Ico.mp hj0
    have hmin' : ∀ j, i ≤ j → j < i + L → s j0 ≤ s j := fun j h1 h2 => hj0min j (Finset.mem_Ico.mpr ⟨h1, h2⟩)
    have hvS : s j0 ∈ S := hmem j0 hij0 hj0L
    have hcardE : (S.erase (s j0)).card ≤ r := by rw [Finset.card_erase_of_mem hvS]; omega
    -- the slowest setter of the run sets at most once in it
    have honce : ∀ p p', i ≤ p → p < p' → p' < i + L → s p = s j0 → s p' = s j0 → False := by
      intro p p' hip hpp hp'L hp hp'
      have hex : ∃ k', p < k' ∧ k' < i + L ∧ s k' = s j0 := ⟨p', hpp, hp'L, hp'⟩
      set k' := Nat.find hex with hk'def
      obtain ⟨hpk, hk'L, hk'v⟩ := Nat.find_spec hex
      have hbetween : ∀ j, p < j → j < k' → s j ≠ s j0 := fun j hj1 hj2 hjv =>
        Nat.find_min hex hj2 ⟨hj1, by omega, hjv⟩
      have hpk2 : p + 1 < k' := by
        rcases Nat.lt_or_ge (p + 1) k' with h | h
        · exact h
        · exfalso
          have e : k' = p + 1 := by omega
          apply hadj p (by omega)
          rw [← e, hk'v, hp]
      -- the gap is a run over `S.erase v`
      have hgap : k' - p - 1 ≤ 2 ^ r - 1 :=
        ih hn' (S.erase (s j0)) hcardE (p + 1) (k' - p - 1) (by omega)
          (fun j h1 h2 => Finset.mem_erase.mpr ⟨hbetween j (by omega) (by omega), hmem j (by omega) (by omega)⟩)
      exact word_no_slow_return_g (n := n) (2 ^ r - 1) (by omega) t s q p k' hpk2 (by omega) htpos
        (fun j _ h2 => hspos j (by omega)) (fun j _ h2 => hdat j (by omega)) (hw k' (by omega))
        (fun j h1 h2 => by rw [hp]; exact hmin' j (by omega) (by omega)) (by rw [hk'v, hp])
        (hq0 p (by omega)) hmono (lt_of_lt_of_le (hlt (p + 1) (by omega)) (hmono _ _ (by omega)))
    have hnotv : ∀ j, i ≤ j → j < i + L → j ≠ j0 → s j ≠ s j0 := by
      intro j h1 h2 hne hjv
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · exact honce j j0 h1 h hj0L hjv rfl
      · exact honce j0 j hij0 h h2 rfl hjv
    have hleft : j0 - i ≤ 2 ^ r - 1 :=
      ih hn' (S.erase (s j0)) hcardE i (j0 - i) (by omega)
        (fun j h1 h2 => Finset.mem_erase.mpr ⟨hnotv j h1 (by omega) (by omega), hmem j h1 (by omega)⟩)
    have hright : i + L - j0 - 1 ≤ 2 ^ r - 1 :=
      ih hn' (S.erase (s j0)) hcardE (j0 + 1) (i + L - j0 - 1) (by omega)
        (fun j h1 h2 => Finset.mem_erase.mpr ⟨hnotv j (by omega) (by omega) (by omega), hmem j (by omega) (by omega)⟩)
    omega

theorem factor_pow_le_exp_two {n : ℕ} [Fact (2 ≤ n)] (hn9 : 9 ≤ n) :
    ((1 + (n : ℝ)⁻¹) / (1 - (n : ℝ)⁻¹)) ^ (n - 1) ≤ (n : ℝ) - 1 := by
  have hn0 : (0 : ℝ) < n := n_pos
  have hN9 : (9 : ℝ) ≤ n := by exact_mod_cast hn9
  have hne : (n : ℝ) - 1 ≠ 0 := by linarith
  have hnn : (n : ℝ) ≠ 0 := hn0.ne'
  have hm : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have hq : (1 + (n : ℝ)⁻¹) / (1 - (n : ℝ)⁻¹) = 2 / ((n : ℝ) - 1) + 1 := by
    have h1 : 1 - (n : ℝ)⁻¹ ≠ 0 := by
      have : (n : ℝ)⁻¹ ≤ 9⁻¹ := inv_anti₀ (by norm_num) hN9
      linarith
    rw [div_add_one hne, div_eq_div_iff h1 hne]
    field_simp
    ring
  rw [hq]
  have hx0 : (0 : ℝ) ≤ 2 / ((n : ℝ) - 1) := div_nonneg (by norm_num) (by linarith)
  have h1 : (2 / ((n : ℝ) - 1) + 1) ^ (n - 1) ≤ Real.exp (2 / ((n : ℝ) - 1)) ^ (n - 1) :=
    pow_le_pow_left₀ (by linarith) (Real.add_one_le_exp _) _
  have h2 : Real.exp (2 / ((n : ℝ) - 1)) ^ (n - 1) = Real.exp 2 := by
    rw [← Real.exp_nat_mul, hm]; congr 1; field_simp
  have h3 : Real.exp 2 < 8 := by
    have := Real.exp_one_lt_d9
    have e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]; nlinarith [Real.exp_pos 1]
  linarith

/-- **A subject with `k` differences stops within `2^(k−1) − 1` moves at every `n ≥ 9` with `2^(k−1) ≤ n`.** -/
theorem stops_slowest_recursion {n : ℕ} [Fact (2 ≤ n)] (hn9 : 9 ≤ n) (k : ℕ) (hk : 2 ^ (k - 1) ≤ n)
    {ds : Finset ℝ} (hpos : ∀ d ∈ ds, 0 < d) (hcard : ds.card ≤ k) {a : ℝ} (ha : a ∈ ds)
    (hmin : ∀ d ∈ ds, a ≤ d) :
    move n ds ((move n ds)^[2 ^ (k - 1) - 1] (1 / (n * a))) = (move n ds)^[2 ^ (k - 1) - 1] (1 / (n * a)) := by
  classical
  have ha0 := hpos a ha
  have hn0 : (0 : ℝ) < n := n_pos
  have hk1 : 1 ≤ k := by
    have := Finset.card_pos.mpr ⟨a, ha⟩; omega
  set L0 := 2 ^ (k - 1) - 1 with hL0
  have hpos1 : 1 ≤ 2 ^ (k - 1) := Nat.one_le_two_pow
  set b0 := 1 / ((n : ℝ) * a) with hb0
  set t : ℕ → ℝ := fun j => (move n ds)^[j] b0 with htdef
  have htsucc : ∀ j, t (j + 1) = move n ds (t j) := fun j => Function.iterate_succ_apply' _ _ _
  have hb0pos : 0 < b0 := by rw [hb0]; positivity
  have htpos : ∀ j, 0 < t j := fun j => lt_of_lt_of_le hb0pos (iterate_ge (n := n) ds b0 j)
  have htmono : ∀ j j', j ≤ j' → t j ≤ t j' := by
    have : Monotone t := monotone_nat_of_le_succ (fun j => by rw [htsucc]; exact le_move ds _)
    exact fun j j' h => this h
  have hab : a * b0 = (n : ℝ)⁻¹ := by rw [hb0]; field_simp
  have hat : ∀ j, (n : ℝ)⁻¹ ≤ a * t j := by
    intro j; rw [← hab]; exact mul_le_mul_of_nonneg_left (iterate_ge (n := n) ds b0 j) ha0.le
  -- the nearest runner is clear at iterates 0 … n − 1
  have hq1 : 1 ≤ (1 + (n : ℝ)⁻¹) / (1 - (n : ℝ)⁻¹) := by
    have : (n : ℝ)⁻¹ ≤ 2⁻¹ := inv_le_half
    have : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr hn0
    rw [le_div_iff₀ (by linarith)]; linarith
  have hclear : ∀ j ≤ L0, ¬ inWay n a (t j) := by
    intro j hj
    apply nearest_clear_first_moves hpos ha hmin j
    exact le_trans (pow_le_pow_right₀ hq1 (by omega)) (factor_pow_le_exp_two hn9)
  show move n ds (t L0) = t L0
  by_contra hne
  have hmoving : ∀ j ≤ L0, move n ds (t j) ≠ t j := by
    intro j hj hfix
    have hst := iterate_stable (n := n) (b := b0) hfix (L0 - j)
    have e : j + (L0 - j) = L0 := by omega
    rw [e] at hst
    apply hne
    show move n ds ((move n ds)^[L0] b0) = (move n ds)^[L0] b0
    rw [hst]; exact hfix
  have hex : ∀ j : ℕ, ∃ x : ℝ, ∃ k : ℤ, move n ds (t j) = t j ∨
      (x ∈ ds ∧ |x * t j - k| < (n : ℝ)⁻¹ ∧ t (j + 1) = ((k : ℝ) + (n : ℝ)⁻¹) / x) := by
    intro j
    rcases step_cases (n := n) hpos (t j) with h1 | ⟨x, hx, k, hk, he⟩
    · exact ⟨0, 0, Or.inl h1⟩
    · exact ⟨x, k, Or.inr ⟨hx, hk, by rw [htsucc, he]⟩⟩
  choose s q hsq using hex
  have hD : ∀ j < L0 + 1, s j ∈ ds ∧ |s j * t j - q j| < (n : ℝ)⁻¹ ∧
      t (j + 1) = ((q j : ℝ) + (n : ℝ)⁻¹) / s j := by
    intro j hj
    rcases hsq j with h1 | h1
    · exact absurd h1 (hmoving j (by omega))
    · exact h1
  have hspos : ∀ j < L0 + 1, 0 < s j := fun j hj => hpos _ (hD j hj).1
  have hw : ∀ j < L0 + 1, inWay n (s j) (t j) := fun j hj => inWay_of_near (hD j hj).2.1
  have hlt : ∀ j < L0 + 1, t j < t (j + 1) := by
    intro j hj
    obtain ⟨-, hk, he⟩ := hD j hj
    have hx0 := hspos j hj
    have h1 : s j * t (j + 1) = q j + (n : ℝ)⁻¹ := by rw [he]; field_simp
    have : s j * t j < s j * t (j + 1) := by rw [h1]; linarith [(abs_lt.mp hk).2]
    exact lt_of_mul_lt_mul_left this hx0.le
  have hadj : ∀ j, j + 1 < L0 + 1 → s (j + 1) ≠ s j := by
    intro j hj he
    have hw1 := hw (j + 1) hj
    rw [he, (hD j (by omega)).2.2] at hw1
    exact not_inWay_at_own_opening (hspos j (by omega)) (q j) hw1
  have hq0 : ∀ j < L0 + 1, 0 ≤ q j := fun j hj => by
    have := lap_ge_one (hmin _ (hD j hj).1) (htpos j).le (hat j) (hD j hj).2.1; omega
  have hS : ∀ j, 0 ≤ j → j < 0 + (L0 + 1) → s j ∈ ds.erase a := fun j _ h2 =>
    Finset.mem_erase.mpr ⟨fun he => hclear j (by omega) (he ▸ hw j (by omega)), (hD j (by omega)).1⟩
  have hcardS : (ds.erase a).card ≤ k - 1 := by rw [Finset.card_erase_of_mem ha]; omega
  have := run_length_le (n := n) t s q (L0 + 1) htpos htmono hspos (fun j hj => ⟨(hD j hj).2.1, (hD j hj).2.2⟩)
    hw hq0 hadj hlt (k - 1) hk (ds.erase a) hcardS 0 (L0 + 1) (by omega) hS
  omega

end SlowestRecursion
