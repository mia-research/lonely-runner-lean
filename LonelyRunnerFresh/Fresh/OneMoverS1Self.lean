import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.OneMoverA
import Fresh.OneMoverS1

/-!
# S1, the mover is the subject: the AP with the subject moved to any speed

Written 2026-10-22.  New file; nothing existing is edited.

Setting as in `Fresh.OneMoverS1`: speeds `c + i` (`i = 0 … 7`), except runner `k` (the subject) at speed `x`.
`s1_self`: if `x` is not the speed of another runner, the subject is isolated at some positive instant.

Proof.  The other seven speeds differ by integers, so at an integer instant `N` they all have the same reading
`-(x - c) N` modulo one: at an integer time the other seven runners stand together, and the subject is isolated there
iff `distInt ((x - c) N) ≥ 1/8`.
* `x - c` not an integer: some positive integer `N` works (`exists_nat_clear`).
* `x - c = k` (the AP itself): `t = 1/8`.
* `x - c = n` an integer outside `0 … 7`: the readings are `|i - n|`.  For `n ≥ 9` or `n ≤ -2` they lie in `[D, 7D]`
  with `D` the least, so `t = 1/(8D)` (the subject's bound; `thm8`).  For `n = 8` or `n = -1` they are
  `{1..8}` minus one value, which is `F_j` plus the free reading `8`: `Fresh.OneMover.family`.
* `x - c = p` with `p` another runner's position: excluded by the hypothesis (two equal speeds).
Grades: [L].  No density, cap, move count or clock.
-/

open Classical

namespace Fresh.OneMover

open Fresh Fresh.Localisation

theorem reading_eq (c x : ℝ) (k i : Fin 8) (hik : i ≠ k) (n : ℤ) (hn : x - c = n) :
    oneMover c x k i - oneMover c x k k = ((i : ℕ) : ℝ) - (n : ℝ) := by
  have h1 : oneMover c x k i = c + ((i : ℕ) : ℝ) := by simp [oneMover, hik]
  have h2 : oneMover c x k k = x := by simp [oneMover]
  rw [h1, h2]; linarith

theorem thm8 {D r : ℝ} (hD : 0 < D) (h1 : D ≤ r) (h7 : r ≤ 7 * D) :
    (1 / 8 : ℝ) ≤ distInt (r * (1 / (8 * D))) := by
  apply clear_of_window 0
  · push_cast; rw [mul_one_div, le_div_iff₀ (by positivity)]; nlinarith
  · push_cast; rw [mul_one_div, div_le_iff₀ (by positivity)]; nlinarith

/-- A real that is not an integer has a positive integer multiple that is at least `1/8` from every integer.
**[PROVISIONAL: counting tool]** the multiples `|η| N` are equally spaced against the clear arc `[1/8, 7/8]`; it supports:
at an integer instant the seven other runners stand together and the free subject is clear of them. -/
theorem exists_nat_clear (y : ℝ) (hy : ∀ z : ℤ, y ≠ z) :
    ∃ N : ℕ, 1 ≤ N ∧ (1 / 8 : ℝ) ≤ distInt (y * N) := by
  set η : ℝ := y - (round y : ℝ) with hηdef
  have hη : η ≠ 0 := by
    intro h; apply hy (round y); linarith
  have hηa : 0 < |η| := abs_pos.2 hη
  have hη2 : |η| ≤ 1 / 2 := abs_sub_round y
  by_cases h8 : (1 / 8 : ℝ) ≤ |η|
  · refine ⟨1, le_refl _, ?_⟩
    simpa [distInt, hηdef] using h8
  · have h8 : |η| < 1 / 8 := lt_of_not_ge h8
    set x : ℝ := 1 / (8 * |η|) with hxdef
    have hx1 : 1 < x := by
      rw [hxdef, lt_div_iff₀ (by positivity)]; nlinarith
    have hxd : |η| * x = 1 / 8 := by rw [hxdef]; field_simp
    have hN1 : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
    have hN2 : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one (by linarith)
    refine ⟨⌈x⌉₊, ?_, ?_⟩
    · have : 0 < ⌈x⌉₊ := Nat.ceil_pos.2 (by linarith)
      omega
    · have e : y * (⌈x⌉₊ : ℝ) = η * (⌈x⌉₊ : ℝ) + (((round y * (⌈x⌉₊ : ℤ) : ℤ)) : ℝ) := by
        rw [hηdef]; push_cast; ring
      rw [e, distInt_add_int, ← distInt_abs_mul]
      have a1 := mul_le_mul_of_nonneg_left hN1 hηa.le
      have a2 := mul_le_mul_of_nonneg_left hN2.le hηa.le
      apply clear_of_window 0
      · push_cast; nlinarith
      · push_cast; nlinarith

/-- **[PROVISIONAL: counting tool]** inherited from `exists_nat_clear` and `family`.  S1 for a mover that is the subject. -/
theorem s1_self (c x : ℝ) (k : Fin 8) (hx : ∀ p : Fin 8, p ≠ k → x ≠ c + ((p : ℕ) : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ IsolatedAt (oneMover c x k) k t := by
  by_cases hy : ∀ z : ℤ, x - c ≠ z
  · -- not an integer: an integer instant
    obtain ⟨N, hN1, hN⟩ := exists_nat_clear (x - c) hy
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    refine ⟨N, hNpos, fun i hik => ?_⟩
    have h1 : oneMover c x k i = c + ((i : ℕ) : ℝ) := by simp [oneMover, hik]
    have h2 : oneMover c x k k = x := by simp [oneMover]
    rw [h1, h2]
    have e : (c + ((i : ℕ) : ℝ) - x) * (N : ℝ) = -((x - c) * (N : ℝ)) + ((((i : ℕ) * N : ℕ) : ℤ) : ℝ) := by
      push_cast; ring
    rw [e, distInt_add_int, distInt_neg]
    exact hN
  · have hy' : ∃ z : ℤ, x - c = z := by
      by_contra hcon
      exact hy (fun z hz => hcon ⟨z, hz⟩)
    obtain ⟨n, hn⟩ := hy'
    have hread := fun i (hik : i ≠ k) => reading_eq c x k i hik n hn
    have hk : (k : ℕ) < 8 := k.isLt
    -- the cases for the integer n
    by_cases hnk : n = ((k : ℕ) : ℤ)
    · -- the AP itself: t = 1/8
      refine ⟨1 / 8, by norm_num, fun i hik => ?_⟩
      rw [hread i hik, hnk]
      have hik' : (i : ℕ) ≠ (k : ℕ) := fun h => hik (Fin.ext h)
      have hi := i.isLt
      push_cast
      rcases lt_or_gt_of_ne hik' with hlt | hgt
      · have h1 : ((i : ℕ) : ℝ) + 1 ≤ ((k : ℕ) : ℝ) := by exact_mod_cast hlt
        have h7 : ((k : ℕ) : ℝ) ≤ 7 := by exact_mod_cast (by omega : (k : ℕ) ≤ 7)
        have h0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
        rw [← distInt_neg]
        apply clear_of_window 0
        · push_cast; nlinarith
        · push_cast; nlinarith
      · have h1 : ((k : ℕ) : ℝ) + 1 ≤ ((i : ℕ) : ℝ) := by exact_mod_cast hgt
        have h7 : ((i : ℕ) : ℝ) ≤ 7 := by exact_mod_cast (by omega : (i : ℕ) ≤ 7)
        have h0 : (0 : ℝ) ≤ ((k : ℕ) : ℝ) := Nat.cast_nonneg _
        apply clear_of_window 0
        · push_cast; nlinarith
        · push_cast; nlinarith
    · by_cases hin : 0 ≤ n ∧ n ≤ 7
      · -- another runner's speed
        exfalso
        have hp : n.toNat < 8 := by omega
        have hpk : (⟨n.toNat, hp⟩ : Fin 8) ≠ k := by
          intro h
          apply hnk
          have := congrArg Fin.val h
          simp at this
          omega
        apply hx ⟨n.toNat, hp⟩ hpk
        have : ((n.toNat : ℕ) : ℝ) = (n : ℝ) := by
          have : ((n.toNat : ℕ) : ℤ) = n := Int.toNat_of_nonneg hin.1
          exact_mod_cast this
        simp only [this]
        linarith
      · -- an integer outside 0..7
        have hout : n ≤ -1 ∨ 8 ≤ n := by omega
        by_cases hn8 : n = 8
        · subst hn8
          by_cases hk0 : (k : ℕ) = 0
          · refine ⟨1 / 8, by norm_num, fun i hik => ?_⟩
            rw [hread i hik]
            have hik' : (i : ℕ) ≠ (k : ℕ) := fun h => hik (Fin.ext h)
            have hi := i.isLt
            have h1 : (1 : ℝ) ≤ ((i : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ (i : ℕ))
            have h7 : ((i : ℕ) : ℝ) ≤ 7 := by exact_mod_cast (by omega : (i : ℕ) ≤ 7)
            rw [show (((i : ℕ) : ℝ) - ((8 : ℤ) : ℝ)) * (1 / 8) = -((8 - ((i : ℕ) : ℝ)) * (1 / 8)) by push_cast; ring,
              distInt_neg]
            apply clear_of_window 0
            · push_cast; nlinarith
            · push_cast; nlinarith
          · obtain ⟨t, ht, hF, h8⟩ := family (8 - (k : ℕ)) (by omega) (by omega) 8 (by norm_num)
            refine ⟨t, ht, fun i hik => ?_⟩
            rw [hread i hik]
            have hik' : (i : ℕ) ≠ (k : ℕ) := fun h => hik (Fin.ext h)
            have hi := i.isLt
            by_cases hi0 : (i : ℕ) = 0
            · rw [show (((i : ℕ) : ℝ) - ((8 : ℤ) : ℝ)) * t = -(8 * t) by rw [hi0]; push_cast; ring, distInt_neg]
              exact h8
            · have key := hF (8 - (i : ℕ)) (by omega) (by omega) (by omega)
              rw [show (((i : ℕ) : ℝ) - ((8 : ℤ) : ℝ)) * t = -((((8 - (i : ℕ) : ℕ)) : ℝ) * t) by
                rw [Nat.cast_sub (by omega)]; push_cast; ring, distInt_neg]
              exact key
        by_cases hnm : n = -1
        · subst hnm
          by_cases hk7 : (k : ℕ) = 7
          · refine ⟨1 / 8, by norm_num, fun i hik => ?_⟩
            rw [hread i hik]
            have hik' : (i : ℕ) ≠ (k : ℕ) := fun h => hik (Fin.ext h)
            have hi := i.isLt
            have h0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
            have h6 : ((i : ℕ) : ℝ) ≤ 6 := by exact_mod_cast (by omega : (i : ℕ) ≤ 6)
            rw [show (((i : ℕ) : ℝ) - ((-1 : ℤ) : ℝ)) * (1 / 8) = ((i : ℝ) + 1) * (1 / 8) by push_cast; ring]
            apply clear_of_window 0
            · push_cast; nlinarith
            · push_cast; nlinarith
          · obtain ⟨t, ht, hF, h8⟩ := family ((k : ℕ) + 1) (by omega) (by omega) 8 (by norm_num)
            refine ⟨t, ht, fun i hik => ?_⟩
            rw [hread i hik]
            have hik' : (i : ℕ) ≠ (k : ℕ) := fun h => hik (Fin.ext h)
            have hi := i.isLt
            by_cases hi7 : (i : ℕ) = 7
            · rw [show (((i : ℕ) : ℝ) - ((-1 : ℤ) : ℝ)) * t = 8 * t by rw [hi7]; push_cast; ring]
              exact h8
            · have key := hF ((i : ℕ) + 1) (by omega) (by omega) (by omega)
              rw [show (((i : ℕ) : ℝ) - ((-1 : ℤ) : ℝ)) * t = (((i : ℕ) + 1 : ℕ) : ℝ) * t by push_cast; ring]
              exact key
        by_cases hbig : 9 ≤ n
        · set D : ℝ := (n : ℝ) - 7 with hD
          have hnR : (9 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hbig
          have hDpos : 0 < D := by rw [hD]; linarith
          refine ⟨1 / (8 * D), by positivity, fun i hik => ?_⟩
          rw [hread i hik]
          have hi := i.isLt
          have h0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
          have h7 : ((i : ℕ) : ℝ) ≤ 7 := by exact_mod_cast (by omega : (i : ℕ) ≤ 7)
          rw [show (((i : ℕ) : ℝ) - (n : ℝ)) * (1 / (8 * D)) = -(((n : ℝ) - ((i : ℕ) : ℝ)) * (1 / (8 * D))) by ring,
            distInt_neg]
          exact thm8 hDpos (by rw [hD]; linarith) (by rw [hD]; linarith)
        · have hsm : n ≤ -2 := by omega
          set D : ℝ := -(n : ℝ) with hD
          have hnR : (n : ℝ) ≤ -2 := by exact_mod_cast hsm
          have hDpos : 0 < D := by rw [hD]; linarith
          refine ⟨1 / (8 * D), by positivity, fun i hik => ?_⟩
          rw [hread i hik]
          have hi := i.isLt
          have h0 : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
          have h7 : ((i : ℕ) : ℝ) ≤ 7 := by exact_mod_cast (by omega : (i : ℕ) ≤ 7)
          exact thm8 hDpos (by rw [hD]; linarith) (by rw [hD]; linarith)

#print axioms thm8
#print axioms exists_nat_clear
#print axioms s1_self

theorem s1 (c x : ℝ) (m k : Fin 8) (hx : ∀ p : Fin 8, p ≠ m → x ≠ c + ((p : ℕ) : ℝ)) :
    ∃ t : ℝ, 0 < t ∧ IsolatedAt (oneMover c x m) k t := by
  by_cases hkm : k = m
  · subst hkm
    exact s1_self c x k hx
  · exact s1_other c x k m hkm (hx k hkm)

theorem oneMover_isArrangement (c x : ℝ) (m : Fin 8) (hc : 0 < c) (hx0 : 0 < x)
    (hx : ∀ p : Fin 8, p ≠ m → x ≠ c + ((p : ℕ) : ℝ)) : IsArrangement (oneMover c x m) := by
  constructor
  · intro i
    unfold oneMover
    split_ifs
    · exact hx0
    · have : (0 : ℝ) ≤ ((i : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
  · intro i j h
    unfold oneMover at h
    split_ifs at h with hi hj hj
    · rw [hi, hj]
    · exact absurd h (hx j hj)
    · exact absurd h.symm (hx i hi)
    · exact Fin.ext (by exact_mod_cast (add_left_cancel h))

/-- **S1** (existence witnesses; **[PROVISIONAL: covering]** and **[PROVISIONAL: counting tool]** by inheritance; not the
cascade's landing).  Eight positive distinct speeds: the AP `c + i` with one runner `m` moved to any speed `x`.  Every one of the
eight runners is isolated at some positive instant. -/
theorem s1_all (c x : ℝ) (m : Fin 8) (hc : 0 < c) (hx0 : 0 < x)
    (hx : ∀ p : Fin 8, p ≠ m → x ≠ c + ((p : ℕ) : ℝ)) :
    IsArrangement (oneMover c x m) ∧ ∀ k : Fin 8, Isolation (oneMover c x m) k :=
  ⟨oneMover_isArrangement c x m hc hx0 hx, fun k => s1 c x m k hx⟩

#print axioms s1
#print axioms oneMover_isArrangement
#print axioms s1_all

end Fresh.OneMover
