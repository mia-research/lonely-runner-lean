import LonelyRunner.LRC.Spec.DoubledNbhdCasesN

/-!
# The doubled-slot family under deviation: every runner lonely at a named instant

2026-09-27.  `DoubledSlotN` exhibits every runner of the doubled-slot family (the AP with the runner of slot `r` moved
by whole laps into slot `s`, `m ≥ 1`).  Here every speed is deviated by `|eᵢ| ≤ 1/(512(m + 1))` and every runner is
still lonely at a named positive instant (`dd_exists`), the undeviated instant relocated:

* **runners outside the pair**: the grid rule at class 1, or class 3 when the doubled slot is a class-1 neighbour slot
  (`GridClassN`); one neighbour when the other neighbour slot is the empty one;
* **the far member**: the ratio condition at its nearest runner (`far_role`), or one of seven named openings;
* **the home member**: the partner's actual opening at an interior slot (`home_role`); at an end of the progression
  the far-end runner's or the partner's actual opening (`end_s_r`, generated).

Each case names its flank and lap; the instant is that flank's actual opening.  Units, not primes: the partner's
numerator is a unit mod its denominator (φ), and the classes 1, 3 are units of `ℤ/8`.  No `sorry`, no `native_decide`.
Evidence: `experiments/nN/redo/doubled_nbhd_named_v1.out` (75,264 cases, no failure).
-/

set_option linter.style.longLine false
set_option maxHeartbeats 8000000

namespace LRC.DoubledNbhd

open Arrangement LRC.DoubledSlot LRC.GridNbhd LRC.GridClass

/-- The deviated doubled-slot arrangement. -/
noncomputable def ddV (s r m : ℕ) (e : Fin 8 → ℝ) (i : Fin 8) : ℝ := 100 + (dsZ s r m i : ℝ) + e i

theorem gridTp_pos {p q : ℝ} {DA DB : ℤ} {a b : ℝ} (hp : 0 < p) (hq : 0 < q)
    (hA : (0 < DA ∧ 0 < a) ∨ (DA < 0 ∧ a < 0)) (hB : (0 < DB ∧ 0 < b) ∨ (DB < 0 ∧ b < 0)) :
    0 < gridTp p q DA DB a b := by
  have tA : ∀ c : ℝ, 0 < c → 0 < c * DA / (8 * a) := by
    intro c hc
    rcases hA with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have : (0 : ℝ) < DA := by exact_mod_cast h1
      exact div_pos (mul_pos hc this) (by linarith)
    · have : (DA : ℝ) < 0 := by exact_mod_cast h1
      exact div_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hc this) (by linarith)
  have tB : ∀ c : ℝ, 0 < c → 0 < c * DB / (8 * b) := by
    intro c hc
    rcases hB with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have : (0 : ℝ) < DB := by exact_mod_cast h1
      exact div_pos (mul_pos hc this) (by linarith)
    · have : (DB : ℝ) < 0 := by exact_mod_cast h1
      exact div_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hc this) (by linarith)
  unfold gridTp
  split_ifs
  all_goals first
    | exact tA p hp | exact tB p hp | exact tA q hq | exact tB q hq
    | exact lt_max_of_lt_left (tA p hp) | exact lt_min (tA p hp) (tB p hp)

/-- The sign of a deviated reading, from its whole part. -/
theorem sign_pair {x η : ℝ} {D : ℤ} (hη : η < 1) (hx : |x - D| ≤ η) (hD : D ≠ 0) :
    (0 < D ∧ 0 < x) ∨ (D < 0 ∧ x < 0) := by
  have h := abs_le.mp hx
  rcases lt_or_gt_of_ne hD with h1 | h1
  · right; refine ⟨h1, ?_⟩
    have : (D : ℝ) ≤ -1 := by exact_mod_cast (show D ≤ -1 by omega)
    linarith
  · left; refine ⟨h1, ?_⟩
    have : (1 : ℝ) ≤ D := by exact_mod_cast (show 1 ≤ D by omega)
    linarith

theorem pos_single {c x : ℝ} {D : ℤ} (hc : 0 < c) (h : (0 < D ∧ 0 < x) ∨ (D < 0 ∧ x < 0)) :
    0 < c * D / (8 * x) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have : (0 : ℝ) < D := by exact_mod_cast h1
    exact div_pos (mul_pos hc this) (by linarith)
  · have : (D : ℝ) < 0 := by exact_mod_cast h1
    exact div_pos_of_neg_of_neg (mul_neg_of_pos_of_neg hc this) (by linarith)

/-- The residue table for the class-`p` rule: a reading off the runner's own slot and off both neighbour slots
lands in `2 … 6` at class `p` and at its mirror `q` (checked residue by residue). -/
theorem rest_p (p q x : ℤ) (hpq : (p = 1 ∧ q = 7) ∨ (p = 3 ∧ q = 5)) (h0 : x % 8 ≠ 0) (hA : x % 8 ≠ p)
    (hB : x % 8 ≠ 8 - p) :
    (2 ≤ (p * x) % 8 ∧ (p * x) % 8 ≤ 6) ∧ (2 ≤ (q * x) % 8 ∧ (q * x) % 8 ≤ 6) := by
  have hr0 : 0 ≤ x % 8 := Int.emod_nonneg _ (by norm_num)
  have hr8 : x % 8 < 8 := Int.emod_lt_of_pos _ (by norm_num)
  rw [Int.mul_emod p, Int.mul_emod q]
  generalize x % 8 = r at *
  rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> interval_cases r <;> omega

/-- A neighbour's residue at class `c`. -/
theorem edge_res {c x t v : ℤ} (hc : c % 8 = c) (hx : x % 8 = v) (ht : (c * v) % 8 = t) : (c * x) % 8 = t := by
  rw [Int.mul_emod, hx, hc]; exact ht

theorem far_exc (r : ℕ) (hr1 : 1 ≤ r) (hr7 : r ≤ 7) {δ : Fin 8 → ℝ} {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1 / 512)
    (hδ : ∀ j, |δ j - ((dsZ 0 r 1 j - dsZ 0 r 1 ⟨r, by omega⟩ : ℤ) : ℝ)| ≤ η) :
    ∃ t : ℝ, 0 < t ∧ ∀ j : Fin 8, j ≠ ⟨r, by omega⟩ → (8 : ℝ)⁻¹ ≤ circDist (δ j * t) := by
  interval_cases r
  · exact farx_1 hη0 hη1 hδ
  · exact farx_2 hη0 hη1 hδ
  · exact farx_3 hη0 hη1 hδ
  · exact farx_4 hη0 hη1 hδ
  · exact farx_5 hη0 hη1 hδ
  · exact farx_6 hη0 hη1 hδ
  · exact farx_7 hη0 hη1 hδ

theorem home_end (s r m : ℕ) (hs : s = 0 ∨ s = 7) (hr1 : 1 ≤ r) (hr6 : r ≤ 6) (hm : 1 ≤ m) {δ : Fin 8 → ℝ}
    {η : ℝ} (hη0 : 0 ≤ η) (hηm : η * (256 * ((m : ℝ) + 1)) ≤ 1)
    (hδ : ∀ j, |δ j - ((dsZ s r m j - dsZ s r m ⟨s, by omega⟩ : ℤ) : ℝ)| ≤ η) :
    ∃ t : ℝ, 0 < t ∧ ∀ j : Fin 8, j ≠ ⟨s, by omega⟩ → (8 : ℝ)⁻¹ ≤ circDist (δ j * t) := by
  rcases hs with rfl | rfl <;> interval_cases r
  · exact end_0_1 hm hη0 hηm hδ
  · exact end_0_2 hm hη0 hηm hδ
  · exact end_0_3 hm hη0 hηm hδ
  · exact end_0_4 hm hη0 hηm hδ
  · exact end_0_5 hm hη0 hηm hδ
  · exact end_0_6 hm hη0 hηm hδ
  · exact end_7_1 hm hη0 hηm hδ
  · exact end_7_2 hm hη0 hηm hδ
  · exact end_7_3 hm hη0 hηm hδ
  · exact end_7_4 hm hη0 hηm hδ
  · exact end_7_5 hm hη0 hηm hδ
  · exact end_7_6 hm hη0 hηm hδ

/-- **Every runner of the deviated doubled-slot family has a positive lonely instant**, named per case. -/
theorem dd_exists (s r m : ℕ) (hs : s < 8) (hr : r < 8) (hsr : s ≠ r) (hm : 1 ≤ m) (e : Fin 8 → ℝ)
    (he : ∀ i, |e i| ≤ 1 / (512 * ((m : ℝ) + 1))) (k : Fin 8) :
    ∃ t : ℝ, 0 < t ∧ LonelyAt (ddV s r m e) k t := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set η : ℝ := 1 / (256 * ((m : ℝ) + 1)) with hηdef
  have hη0 : 0 ≤ η := by positivity
  have hηm : η * (256 * ((m : ℝ) + 1)) ≤ 1 := by
    have : η * (256 * ((m : ℝ) + 1)) = 1 := by rw [hηdef]; field_simp
    exact le_of_eq this
  have hη1 : η ≤ 1 / 512 := by nlinarith
  have hδ : ∀ j, |(ddV s r m e j - ddV s r m e k) - ((dsZ s r m j - dsZ s r m k : ℤ) : ℝ)| ≤ η := by
    intro j
    have h1 : (ddV s r m e j - ddV s r m e k) - ((dsZ s r m j - dsZ s r m k : ℤ) : ℝ) = e j - e k := by
      unfold ddV; push_cast; ring
    rw [h1]
    have a1 := abs_le.mp (he j); have a2 := abs_le.mp (he k)
    have h2 : 2 * (1 / (512 * ((m : ℝ) + 1))) = η := by rw [hηdef]; field_simp; try ring
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  suffices H : ∃ t : ℝ, 0 < t ∧ ∀ j, j ≠ k → (8 : ℝ)⁻¹ ≤ circDist ((ddV s r m e j - ddV s r m e k) * t) by
    obtain ⟨t, ht, h⟩ := H
    exact ⟨t, ht, fun j hj => by rw [sep_eq]; exact h j hj⟩
  have hk8 := k.isLt
  by_cases hkr : (k : ℕ) = r
  · ---------------- the far member ----------------
    have hDk : dsZ s r m k = (s : ℤ) + 8 * m := by simp [dsZ, hkr]
    by_cases h49 : 49 ≤ 48 * m + 6 * s
    · obtain ⟨n0, hn0, hn0r, hn0max⟩ : ∃ n0 : ℕ, n0 < 8 ∧ n0 ≠ r ∧ ∀ j, j < 8 → j ≠ r → j ≤ n0 := by
        by_cases hr7 : r = 7
        · exact ⟨6, by norm_num, by omega, fun j hj hjr => by omega⟩
        · exact ⟨7, by norm_num, fun h => hr7 h.symm, fun j hj _ => by omega⟩
      have hn06 : 6 ≤ n0 := by
        by_cases hr7 : r = 7
        · have := hn0max 6 (by norm_num) (by omega); omega
        · have := hn0max 7 (by norm_num) (by omega); omega
      obtain ⟨X, hX⟩ : ∃ X : Fin 8, (X : ℕ) = n0 := ⟨⟨n0, hn0⟩, rfl⟩
      set W : ℤ := (s : ℤ) + 8 * m - n0 with hW
      have hXk : X ≠ k := fun h => hn0r (by rw [← hX, h, hkr])
      have hDX : dsZ s r m X - dsZ s r m k = -W := by
        rw [hDk, hW]; simp only [dsZ, hX, if_neg hn0r]; ring
      have hW2 : 2 ≤ W := by omega
      have hrest : ∀ j, j ≠ k → j ≠ X →
          -(W + 7) ≤ dsZ s r m j - dsZ s r m k ∧ dsZ s r m j - dsZ s r m k ≤ -(W + 1) := by
        intro j h1 h2
        have hjr : (j : ℕ) ≠ r := fun h => h1 (Fin.ext (h.trans hkr.symm))
        have hjn : (j : ℕ) ≠ n0 := fun h => h2 (Fin.ext (h.trans hX.symm))
        have := hn0max j j.isLt hjr
        rw [hDk]; simp only [dsZ, if_neg hjr]; constructor <;> omega
      have hWR : (2 : ℝ) ≤ W := by exact_mod_cast hW2
      refine ⟨(1 / (8 * (W : ℝ))) * ((dsZ s r m X - dsZ s r m k : ℤ) : ℝ) /
        (ddV s r m e X - ddV s r m e k), ?_, ?_⟩
      · have hDX1 : 1 ≤ |((dsZ s r m X - dsZ s r m k : ℤ) : ℝ)| := by
          rw [hDX]; push_cast; rw [abs_neg, abs_of_pos (show (0 : ℝ) < W by linarith)]; linarith
        exact pos_reloc (by positivity) (by linarith) (hδ X) hDX1
      · exact far_role (δ := fun j => ddV s r m e j - ddV s r m e k)
          (D := fun j => dsZ s r m j - dsZ s r m k) hXk hη0 (by linarith) hδ hDX hW2 hrest
    · have hm1 : m = 1 := by omega
      have hs0 : s = 0 := by omega
      subst hm1 hs0
      have hkeq : k = ⟨r, hr⟩ := Fin.ext hkr
      subst hkeq
      obtain ⟨t, ht, h⟩ := far_exc r (by omega) (by omega)
        (δ := fun j => ddV 0 r 1 e j - ddV 0 r 1 e ⟨r, hr⟩) hη0 hη1 (fun j => hδ j)
      exact ⟨t, ht, fun j hj => h j hj⟩
  by_cases hks : (k : ℕ) = s
  · ---------------- the home member ----------------
    have hDk : dsZ s r m k = (s : ℤ) := by simp [dsZ, hks, hsr]
    by_cases hint : (1 ≤ s ∧ s ≤ 6) ∨ (s = 0 ∧ r = 7) ∨ (s = 7 ∧ r = 0)
    · obtain ⟨X, hX⟩ : ∃ X : Fin 8, (X : ℕ) = r := ⟨⟨r, hr⟩, rfl⟩
      have hXk : X ≠ k := fun h => hkr (by rw [← h, hX])
      have hDX : dsZ s r m X - dsZ s r m k = 8 * m := by rw [hDk]; simp only [dsZ, hX, if_true]; ring
      have hrest : ∀ j, j ≠ k → j ≠ X →
          1 ≤ |dsZ s r m j - dsZ s r m k| ∧ |dsZ s r m j - dsZ s r m k| ≤ 6 := by
        intro j h1 h2
        have hjr : (j : ℕ) ≠ r := fun h => h2 (Fin.ext (h.trans hX.symm))
        have hjs : (j : ℕ) ≠ s := fun h => h1 (Fin.ext (h.trans hks.symm))
        have hj8 := j.isLt
        rw [hDk]; simp only [dsZ, if_neg hjr]
        constructor
        · rw [le_abs]; omega
        · rw [abs_le]; omega
      refine ⟨((8 * (m : ℝ) + 1) / (64 * m)) * ((dsZ s r m X - dsZ s r m k : ℤ) : ℝ) /
        (ddV s r m e X - ddV s r m e k), ?_, ?_⟩
      · have hDX1 : 1 ≤ |((dsZ s r m X - dsZ s r m k : ℤ) : ℝ)| := by
          rw [hDX]; push_cast; rw [abs_of_pos (show (0 : ℝ) < 8 * m by linarith)]; linarith
        exact pos_reloc (by positivity) (by linarith) (hδ X) hDX1
      · exact home_role (δ := fun j => ddV s r m e j - ddV s r m e k)
          (D := fun j => dsZ s r m j - dsZ s r m k) hm hXk hη0 hηm hδ hDX hrest
    · have hs' : s = 0 ∨ s = 7 := by omega
      have hkeq : k = ⟨s, hs⟩ := Fin.ext hks
      subst hkeq
      exact home_end s r m hs' (by omega) (by omega) hm hη0 hηm (fun j => hδ j)
  · ---------------- a runner outside the pair ----------------
    have hDk : dsZ s r m k = ((k : ℕ) : ℤ) := by simp [dsZ, hkr]
    have hW : ∀ j, |((dsZ s r m j - dsZ s r m k : ℤ) : ℝ)| ≤ 8 * m + 7 := by
      intro j
      have hj8 := j.isLt
      have h : |dsZ s r m j - dsZ s r m k| ≤ 8 * (m : ℤ) + 7 := by
        rw [hDk, abs_le]; simp only [dsZ]; split_ifs <;> constructor <;> omega
      have h' : ((|dsZ s r m j - dsZ s r m k| : ℤ) : ℝ) ≤ ((8 * (m : ℤ) + 7 : ℤ) : ℝ) := by exact_mod_cast h
      push_cast at h' ⊢; exact h'
    have hηW : η * (14 * (8 * (m : ℝ) + 7) + 21) ≤ 1 := by
      rw [hηdef, div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]; nlinarith
    have hDj : ∀ j : Fin 8, dsZ s r m j - dsZ s r m k =
        if (j : ℕ) = r then (s : ℤ) + 8 * m - (k : ℕ) else ((j : ℕ) : ℤ) - (k : ℕ) := by
      intro j; rw [hDk]; simp only [dsZ]; split_ifs <;> ring
    have hδ' : ∀ j, |(ddV s r m e j - ddV s r m e k) - ((dsZ s r m j - dsZ s r m k : ℤ) : ℝ)| ≤ η := hδ
    have hks' : (k : ℕ) ≠ s := hks
    have hkr' : (k : ℕ) ≠ r := hkr
    obtain ⟨p, q, hpq, hsp⟩ : ∃ p q : ℕ, (p = 1 ∧ q = 7 ∨ p = 3 ∧ q = 5) ∧
        (s ≠ ((k : ℕ) + p) % 8 ∧ s ≠ ((k : ℕ) + (8 - p)) % 8) := by
      by_cases hp : s = ((k : ℕ) + 1) % 8 ∨ s = ((k : ℕ) + 7) % 8
      · exact ⟨3, 5, Or.inr ⟨rfl, rfl⟩, by omega, by omega⟩
      · exact ⟨1, 7, Or.inl ⟨rfl, rfl⟩, by omega, by omega⟩
    obtain ⟨hsp1, hsp2⟩ := hsp
    rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- class 1, mirror 7
      obtain ⟨A, hA⟩ : ∃ A : Fin 8, (A : ℕ) = ((k : ℕ) + 1) % 8 := ⟨⟨_, Nat.mod_lt _ (by norm_num)⟩, rfl⟩
      obtain ⟨B, hB⟩ : ∃ B : Fin 8, (B : ℕ) = ((k : ℕ) + (8 - 1)) % 8 := ⟨⟨_, Nat.mod_lt _ (by norm_num)⟩, rfl⟩
      have hAk : A ≠ k := by intro h; have := congrArg Fin.val h; rw [hA] at this; omega
      have hBk : B ≠ k := by intro h; have := congrArg Fin.val h; rw [hB] at this; omega
      have hAB : A ≠ B := by intro h; have := congrArg Fin.val h; rw [hA, hB] at this; omega
      by_cases hAr : ((k : ℕ) + 1) % 8 = r
      · have hBr : ((k : ℕ) + (8 - 1)) % 8 ≠ r := by omega
        have hDB : dsZ s r m B - dsZ s r m k ≠ 0 := by rw [hDj, hB, if_neg hBr]; omega
        refine ⟨((1 : ℤ) : ℝ) * ((dsZ s r m B - dsZ s r m k : ℤ) : ℝ) / (8 * (ddV s r m e B - ddV s r m e k)),
          ?_, ?_⟩
        · exact pos_single (by norm_num) (sign_pair (by linarith) (hδ B) hDB)
        · exact readings_clear_single (δ := fun j => ddV s r m e j - ddV s r m e k)
            (D := fun j => dsZ s r m j - dsZ s r m k) (k := k) (X := B) (p := (1 : ℤ)) (sX := 7)
            (by norm_num) (by norm_num) hBk hη0 hηW hδ' hW
            (by beta_reduce; exact edge_res (v := 7) (by norm_num) (by rw [hDj, hB, if_neg hBr]; omega) (by norm_num)) (Or.inr rfl)
            (by
              intro j h1 h2
              have hj8 := j.isLt
              have h1' : (j : ℕ) ≠ (k : ℕ) := fun h => h1 (Fin.ext h)
              have h2' : (j : ℕ) ≠ ((k : ℕ) + (8 - 1)) % 8 := fun h => h2 (Fin.ext (h.trans hB.symm))
              beta_reduce; rw [hDj]; split_ifs with hjr <;>
                exact (rest_p 1 7 _ (Or.inl ⟨rfl, rfl⟩) (by omega) (by omega) (by omega)).1)
      by_cases hBr : ((k : ℕ) + (8 - 1)) % 8 = r
      · have hDA : dsZ s r m A - dsZ s r m k ≠ 0 := by rw [hDj, hA, if_neg hAr]; omega
        refine ⟨((1 : ℤ) : ℝ) * ((dsZ s r m A - dsZ s r m k : ℤ) : ℝ) / (8 * (ddV s r m e A - ddV s r m e k)),
          ?_, ?_⟩
        · exact pos_single (by norm_num) (sign_pair (by linarith) (hδ A) hDA)
        · exact readings_clear_single (δ := fun j => ddV s r m e j - ddV s r m e k)
            (D := fun j => dsZ s r m j - dsZ s r m k) (k := k) (X := A) (p := (1 : ℤ)) (sX := 1)
            (by norm_num) (by norm_num) hAk hη0 hηW hδ' hW
            (by beta_reduce; exact edge_res (v := 1) (by norm_num) (by rw [hDj, hA, if_neg hAr]; omega) (by norm_num)) (Or.inl rfl)
            (by
              intro j h1 h2
              have hj8 := j.isLt
              have h1' : (j : ℕ) ≠ (k : ℕ) := fun h => h1 (Fin.ext h)
              have h2' : (j : ℕ) ≠ ((k : ℕ) + 1) % 8 := fun h => h2 (Fin.ext (h.trans hA.symm))
              beta_reduce; rw [hDj]; split_ifs with hjr <;>
                exact (rest_p 1 7 _ (Or.inl ⟨rfl, rfl⟩) (by omega) (by omega) (by omega)).1)
      · have hDA : dsZ s r m A - dsZ s r m k ≠ 0 := by rw [hDj, hA, if_neg hAr]; omega
        have hDB : dsZ s r m B - dsZ s r m k ≠ 0 := by rw [hDj, hB, if_neg hBr]; omega
        refine ⟨gridTp ((1 : ℤ) : ℝ) ((7 : ℤ) : ℝ) (dsZ s r m A - dsZ s r m k) (dsZ s r m B - dsZ s r m k)
          (ddV s r m e A - ddV s r m e k) (ddV s r m e B - ddV s r m e k), ?_, ?_⟩
        · exact gridTp_pos (by norm_num) (by norm_num)
            (sign_pair (by linarith) (hδ A) hDA) (sign_pair (by linarith) (hδ B) hDB)
        · exact readings_clear_p (δ := fun j => ddV s r m e j - ddV s r m e k)
            (D := fun j => dsZ s r m j - dsZ s r m k) (k := k) (A := A) (B := B) (p := (1 : ℤ))
            (q := (7 : ℤ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hAk hBk hAB hη0 hηW hδ' hW
            (by beta_reduce; exact edge_res (v := 1) (by norm_num) (by rw [hDj, hA, if_neg hAr]; omega) (by norm_num))
            (by beta_reduce; exact edge_res (v := 7) (by norm_num) (by rw [hDj, hB, if_neg hBr]; omega) (by norm_num))
            (by beta_reduce; exact edge_res (v := 1) (by norm_num) (by rw [hDj, hA, if_neg hAr]; omega) (by norm_num))
            (by beta_reduce; exact edge_res (v := 7) (by norm_num) (by rw [hDj, hB, if_neg hBr]; omega) (by norm_num))
            (by
              intro j h1 h2 h3
              have hj8 := j.isLt
              have h1' : (j : ℕ) ≠ (k : ℕ) := fun h => h1 (Fin.ext h)
              have h2' : (j : ℕ) ≠ ((k : ℕ) + 1) % 8 := fun h => h2 (Fin.ext (h.trans hA.symm))
              have h3' : (j : ℕ) ≠ ((k : ℕ) + (8 - 1)) % 8 := fun h => h3 (Fin.ext (h.trans hB.symm))
              beta_reduce; rw [hDj]; split_ifs with hjr <;>
                exact rest_p 1 7 _ (Or.inl ⟨rfl, rfl⟩) (by omega) (by omega) (by omega))
    · -- class 3, mirror 5
      obtain ⟨A, hA⟩ : ∃ A : Fin 8, (A : ℕ) = ((k : ℕ) + 3) % 8 := ⟨⟨_, Nat.mod_lt _ (by norm_num)⟩, rfl⟩
      obtain ⟨B, hB⟩ : ∃ B : Fin 8, (B : ℕ) = ((k : ℕ) + (8 - 3)) % 8 := ⟨⟨_, Nat.mod_lt _ (by norm_num)⟩, rfl⟩
      have hAk : A ≠ k := by intro h; have := congrArg Fin.val h; rw [hA] at this; omega
      have hBk : B ≠ k := by intro h; have := congrArg Fin.val h; rw [hB] at this; omega
      have hAB : A ≠ B := by intro h; have := congrArg Fin.val h; rw [hA, hB] at this; omega
      by_cases hAr : ((k : ℕ) + 3) % 8 = r
      · have hBr : ((k : ℕ) + (8 - 3)) % 8 ≠ r := by omega
        have hDB : dsZ s r m B - dsZ s r m k ≠ 0 := by rw [hDj, hB, if_neg hBr]; omega
        refine ⟨((3 : ℤ) : ℝ) * ((dsZ s r m B - dsZ s r m k : ℤ) : ℝ) / (8 * (ddV s r m e B - ddV s r m e k)),
          ?_, ?_⟩
        · exact pos_single (by norm_num) (sign_pair (by linarith) (hδ B) hDB)
        · exact readings_clear_single (δ := fun j => ddV s r m e j - ddV s r m e k)
            (D := fun j => dsZ s r m j - dsZ s r m k) (k := k) (X := B) (p := (3 : ℤ)) (sX := 7)
            (by norm_num) (by norm_num) hBk hη0 hηW hδ' hW
            (by beta_reduce; exact edge_res (v := 5) (by norm_num) (by rw [hDj, hB, if_neg hBr]; omega) (by norm_num)) (Or.inr rfl)
            (by
              intro j h1 h2
              have hj8 := j.isLt
              have h1' : (j : ℕ) ≠ (k : ℕ) := fun h => h1 (Fin.ext h)
              have h2' : (j : ℕ) ≠ ((k : ℕ) + (8 - 3)) % 8 := fun h => h2 (Fin.ext (h.trans hB.symm))
              beta_reduce; rw [hDj]; split_ifs with hjr <;>
                exact (rest_p 3 5 _ (Or.inr ⟨rfl, rfl⟩) (by omega) (by omega) (by omega)).1)
      by_cases hBr : ((k : ℕ) + (8 - 3)) % 8 = r
      · have hDA : dsZ s r m A - dsZ s r m k ≠ 0 := by rw [hDj, hA, if_neg hAr]; omega
        refine ⟨((3 : ℤ) : ℝ) * ((dsZ s r m A - dsZ s r m k : ℤ) : ℝ) / (8 * (ddV s r m e A - ddV s r m e k)),
          ?_, ?_⟩
        · exact pos_single (by norm_num) (sign_pair (by linarith) (hδ A) hDA)
        · exact readings_clear_single (δ := fun j => ddV s r m e j - ddV s r m e k)
            (D := fun j => dsZ s r m j - dsZ s r m k) (k := k) (X := A) (p := (3 : ℤ)) (sX := 1)
            (by norm_num) (by norm_num) hAk hη0 hηW hδ' hW
            (by beta_reduce; exact edge_res (v := 3) (by norm_num) (by rw [hDj, hA, if_neg hAr]; omega) (by norm_num)) (Or.inl rfl)
            (by
              intro j h1 h2
              have hj8 := j.isLt
              have h1' : (j : ℕ) ≠ (k : ℕ) := fun h => h1 (Fin.ext h)
              have h2' : (j : ℕ) ≠ ((k : ℕ) + 3) % 8 := fun h => h2 (Fin.ext (h.trans hA.symm))
              beta_reduce; rw [hDj]; split_ifs with hjr <;>
                exact (rest_p 3 5 _ (Or.inr ⟨rfl, rfl⟩) (by omega) (by omega) (by omega)).1)
      · have hDA : dsZ s r m A - dsZ s r m k ≠ 0 := by rw [hDj, hA, if_neg hAr]; omega
        have hDB : dsZ s r m B - dsZ s r m k ≠ 0 := by rw [hDj, hB, if_neg hBr]; omega
        refine ⟨gridTp ((3 : ℤ) : ℝ) ((5 : ℤ) : ℝ) (dsZ s r m A - dsZ s r m k) (dsZ s r m B - dsZ s r m k)
          (ddV s r m e A - ddV s r m e k) (ddV s r m e B - ddV s r m e k), ?_, ?_⟩
        · exact gridTp_pos (by norm_num) (by norm_num)
            (sign_pair (by linarith) (hδ A) hDA) (sign_pair (by linarith) (hδ B) hDB)
        · exact readings_clear_p (δ := fun j => ddV s r m e j - ddV s r m e k)
            (D := fun j => dsZ s r m j - dsZ s r m k) (k := k) (A := A) (B := B) (p := (3 : ℤ))
            (q := (5 : ℤ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hAk hBk hAB hη0 hηW hδ' hW
            (by beta_reduce; exact edge_res (v := 3) (by norm_num) (by rw [hDj, hA, if_neg hAr]; omega) (by norm_num))
            (by beta_reduce; exact edge_res (v := 5) (by norm_num) (by rw [hDj, hB, if_neg hBr]; omega) (by norm_num))
            (by beta_reduce; exact edge_res (v := 3) (by norm_num) (by rw [hDj, hA, if_neg hAr]; omega) (by norm_num))
            (by beta_reduce; exact edge_res (v := 5) (by norm_num) (by rw [hDj, hB, if_neg hBr]; omega) (by norm_num))
            (by
              intro j h1 h2 h3
              have hj8 := j.isLt
              have h1' : (j : ℕ) ≠ (k : ℕ) := fun h => h1 (Fin.ext h)
              have h2' : (j : ℕ) ≠ ((k : ℕ) + 3) % 8 := fun h => h2 (Fin.ext (h.trans hA.symm))
              have h3' : (j : ℕ) ≠ ((k : ℕ) + (8 - 3)) % 8 := fun h => h3 (Fin.ext (h.trans hB.symm))
              beta_reduce; rw [hDj]; split_ifs with hjr <;>
                exact rest_p 3 5 _ (Or.inr ⟨rfl, rfl⟩) (by omega) (by omega) (by omega))

end LRC.DoubledNbhd
