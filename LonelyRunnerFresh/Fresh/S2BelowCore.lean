import Mathlib
import Fresh.Framework
import Fresh.Localisation
import Fresh.Cascade
import Fresh.OneMoverA
import Fresh.CascadeLanding
import Fresh.CascadeLandingG
import Fresh.CascadeLanding2
import Fresh.CascadeLanding2b
import Fresh.S2CleanLemmas

/-!
# Two movers, at least one at or below the least frozen reading: shared lemmas (S2Below)

Written 2026-10-23.  New file.  Frozen integer readings `S`, movers `d1, d2 > 0`.  Lonely at `t` means `FClear S t` and `Clear2 d1 d2 t`.
* `fclear_add_nat`, `fclear_lap`: `FClear S` is 1-periodic (integer readings), so a lonely piece of the frozen set recurs every lap.
* `ex_of_piece`: a common clear instant of the movers inside a lap-shifted copy `[l + n, r + n]` of a frozen piece `[l, r]` is a lonely instant.
* `isFirst_char`, `first_in_piece`, `landing_in_piece` (conditional landing at an ARBITRARY left end `L`): the first lonely instant `T` is the least
  `t` with `FClear S t` and `Clear2 d1 d2 t`; if no frozen-clear instant below `L` has the movers clear, and the frozen-clear interval `[L, R]` holds a
  common clear instant, then `T` lies in `[L, R]` and is the first common clear instant at or after `L`.  No periodicity or piece list is used.
* `exists_isFirst_of_lonely`, `landing_of_ex`: ONE lonely instant gives the cascade landing in the `Lands` form, started at `1/(8 min d1 d2)`.
* `run_lemma` **[PROVISIONAL: counting tool]**: if `K * distInt d >= 1/4`, among `K + 1` consecutive laps `n0, ..., n0 + K` some `d * (n + c)` is clear
  (an arithmetic progression of step `d` cannot stay within `1/8` of the integers for more than `K` steps unless `K * distInt d < 1/4`).
* `small_II`, `small_I_pos`, `small_I_neg`, `small_A`: the movers with `d1 <= 1/8`.  `small_II`: `distInt d2 >= d1/2` (run lemma at one frozen-clear
  point `tau0`, the laps fitting in the first clear window of `d1`).  `small_I_*`: `d2 = j + eps`, `|eps| <= d1/2`, `j >= 1`: the lap `n` that first
  brings `d1 (n + tau0)` to `1/8` moves the phase of `d2` from `j tau0` by at most `1/8`.  `small_A`: `4 d2 (r - l) >= 1` for a frozen-clear piece `[l, r]`
  (rule R1 inside the first clear window of `d1`).
Grades: [L].  `run_lemma` and `small_A` are [PROVISIONAL: counting tool].
-/

open Classical

namespace Fresh.OneMover

open Fresh

theorem fclear_add_nat (S : Finset ℕ) (σ : ℝ) (n : ℕ) (h : FClear S σ) : FClear S (σ + n) := by
  intro i hi
  have e : (i : ℝ) * (σ + n) = (i : ℝ) * σ + (((i * n : ℕ) : ℤ) : ℝ) := by push_cast; ring
  rw [e, Fresh.Localisation.distInt_add_int]
  exact h i hi

theorem fclear_lap (S : Finset ℕ) (s : ℝ) (n : ℕ) (h : FClear S (s - n)) : FClear S s := by
  have := fclear_add_nat S (s - n) n h
  simpa using this

/-- A common clear instant inside a lap-shifted frozen piece is a lonely instant. -/
theorem ex_of_piece {S : Finset ℕ} {l r L R : ℝ} (n : ℕ) (hl : 0 < l) (hL : L = l + n) (hR : R = r + n)
    (hP : ∀ s, l ≤ s → s ≤ r → FClear S s) {d1 d2 : ℝ}
    (h : ∃ t, L ≤ t ∧ t ≤ R ∧ Clear2 d1 d2 t) : ∃ t, 0 < t ∧ FClear S t ∧ Clear2 d1 d2 t := by
  obtain ⟨t, h1, h2, h3⟩ := h
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [hL] at h1
  rw [hR] at h2
  refine ⟨t, by linarith, ?_, h3⟩
  apply fclear_lap S t n
  exact hP (t - n) (by linarith) (by linarith)

theorem isFirst_char {S : Finset ℕ} {d1 d2 T : ℝ} (h : IsFirst (insert d1 (insert d2 (fset S))) T) :
    FClear S T ∧ Clear2 d1 d2 T ∧ ∀ s, 0 < s → FClear S s → Clear2 d1 d2 s → T ≤ s :=
  ⟨((lonely_insert2_iff S d1 d2 T).1 h.1).1, ((lonely_insert2_iff S d1 d2 T).1 h.1).2,
   fun s hs hF hC => h.2 s hs ((lonely_insert2_iff S d1 d2 s).2 ⟨hF, hC⟩)⟩

/-- The first lonely instant, read inside a frozen-clear interval `[L, R]` containing it. -/
theorem first_in_piece {S : Finset ℕ} {d1 d2 T L R : ℝ} (h : IsFirst (insert d1 (insert d2 (fset S))) T)
    (hL : 0 < L) (hP : ∀ s, L ≤ s → s ≤ R → FClear S s) (hT : L ≤ T ∧ T ≤ R) :
    Clear2 d1 d2 T ∧ ∀ s, L ≤ s → s ≤ R → Clear2 d1 d2 s → T ≤ s := by
  obtain ⟨_, hC, hmin⟩ := isFirst_char h
  exact ⟨hC, fun s h1 h2 h3 => hmin s (lt_of_lt_of_le hL h1) (hP s h1 h2) h3⟩

/-- **Conditional landing at an arbitrary left end `L`.**  If no instant below `L` that is clear for the frozen readings has both movers clear,
and the frozen-clear interval `[L, R]` holds a common clear instant, then the first lonely instant lies in `[L, R]` and is the first common clear
instant at or after `L`. -/
theorem landing_in_piece {S : Finset ℕ} {d1 d2 L R : ℝ} (hd1 : 0 < d1) (hd2 : 0 < d2) (hL : 0 < L)
    (hP : ∀ s, L ≤ s → s ≤ R → FClear S s)
    (hn : ∀ s, 0 < s → s < L → FClear S s → ¬ Clear2 d1 d2 s)
    (hex : ∃ t, L ≤ t ∧ t ≤ R ∧ Clear2 d1 d2 t) :
    ∃ T, IsFirst (insert d1 (insert d2 (fset S))) T ∧ L ≤ T ∧ T ≤ R ∧ Clear2 d1 d2 T ∧
      ∀ s, L ≤ s → s < T → ¬ Clear2 d1 d2 s := by
  obtain ⟨ts, hls, hrs, hcs⟩ := hex
  obtain ⟨T, hlT, hCT, hmin⟩ := first_two_clear hd1 hd2 hL ⟨ts, hls, hcs⟩
  have hTr : T ≤ R := le_trans (hmin ts hls hcs) hrs
  have hFT : FClear S T := hP T hlT hTr
  refine ⟨T, ⟨(lonely_insert2_iff S d1 d2 T).2 ⟨hFT, hCT⟩, ?_⟩, hlT, hTr, hCT,
    fun s hs hlt hc => absurd (hmin s hs hc) (not_le.2 hlt)⟩
  intro s hs hlon
  rw [lonely_insert2_iff] at hlon
  by_contra hlt
  push Not at hlt
  by_cases hsL : s < L
  · exact hn s hs hsL hlon.1 hlon.2
  · exact absurd (hmin s (not_lt.1 hsL) hlon.2) (not_le.2 hlt)

theorem exists_isFirst_of_lonely {E : Finset ℝ} (hpos : ∀ d ∈ E, 0 < d) {a : ℝ} (ha : a ∈ E) {t : ℝ} (ht : 0 < t)
    (hl : Fresh.Cascade.LonelyAt E t) : ∃ T, 0 < T ∧ IsFirst E T := by
  have hapos := hpos a ha
  have hb : 1 / (8 * a) ≤ t := lonely_geG ha hapos ht hl
  have hb0 : 0 < 1 / (8 * a) := by positivity
  obtain ⟨N, hN⟩ := Fresh.Cascade.exists_fixed_of_lonely hpos hb0 hl hb
  have hmv : ∀ n, IsMove E (Fresh.Cascade.cascadeSeq E (1 / (8 * a)) n) (Fresh.Cascade.cascadeSeq E (1 / (8 * a)) (n + 1)) :=
    Fresh.Cascade.cascadeSeq_isMove _ _
  have h0 : Fresh.Cascade.cascadeSeq E (1 / (8 * a)) 0 = 1 / (8 * a) := Fresh.Cascade.cascadeSeq_zero _ _
  obtain ⟨hlon, hmin⟩ := Fresh.Cascade.fixed_is_first_isolation hpos ha h0 hmv hN
  have hge := Fresh.Cascade.start_le_seq hpos hmv N
  exact ⟨_, lt_of_lt_of_le (by rw [h0]; exact hb0) hge, hlon, fun s hs hls => hmin s hs hls⟩

/-- **One lonely instant gives the landing**, in the `Lands` form, started at `1/(8 min d1 d2)`. -/
theorem landing_of_ex {S : Finset ℕ} (hS : ∀ i ∈ S, 1 ≤ i) {d1 d2 : ℝ} (hd1 : 0 < d1) (hd2 : 0 < d2)
    (hex : ∃ t, 0 < t ∧ FClear S t ∧ Clear2 d1 d2 t) :
    ∃ T : ℝ, 1 / (8 * min d1 d2) ≤ T ∧ IsFirst (insert d1 (insert d2 (fset S))) T ∧
      (∃ seq : ℕ → ℝ, seq 0 = 1 / (8 * min d1 d2) ∧
        (∀ n, IsMove (insert d1 (insert d2 (fset S))) (seq n) (seq (n + 1))) ∧ ∃ N, seq (N + 1) = seq N) ∧
      ∀ seq : ℕ → ℝ, seq 0 = 1 / (8 * min d1 d2) →
        (∀ n, IsMove (insert d1 (insert d2 (fset S))) (seq n) (seq (n + 1))) → ∀ N, seq (N + 1) = seq N → seq N = T := by
  have hpos := pos_insert2 hS hd1 hd2
  have hamem : min d1 d2 ∈ insert d1 (insert d2 (fset S)) := by
    rcases min_choice d1 d2 with h | h
    · rw [h]; exact Finset.mem_insert_self _ _
    · rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  obtain ⟨t, ht, hF, hC⟩ := hex
  have hl := (lonely_insert2_iff S d1 d2 t).2 ⟨hF, hC⟩
  obtain ⟨T, hT, hf⟩ := exists_isFirst_of_lonely hpos hamem ht hl
  have hb : 1 / (8 * min d1 d2) ≤ T := Fresh.Cascade.bound_le_of_lonely hamem (hpos _ hamem) hf.1 hT
  have := cascade_landsG hpos hamem hT hf
  exact ⟨T, hb, hf, this.1, this.2⟩

/-- **Run lemma** [PROVISIONAL: counting tool].  An arithmetic progression of step `d` that stays within `1/8` of the integers for `K + 1` consecutive
terms has `K * distInt d < 1/4`. -/
theorem run_lemma {d c : ℝ} {K : ℕ} (hK : (1 : ℝ) / 4 ≤ K * distInt d) (n0 : ℕ) :
    ∃ i : ℕ, i ≤ K ∧ (1 / 8 : ℝ) ≤ distInt (d * (((n0 + i : ℕ) : ℝ) + c)) := by
  by_contra hcon
  push Not at hcon
  have hK1 : 1 ≤ K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · subst h; norm_num at hK
    · exact h
  obtain ⟨X, hXdef⟩ : ∃ X : ℕ → ℝ, ∀ i, X i = d * (((n0 + i : ℕ) : ℝ) + c) := ⟨_, fun i => rfl⟩
  have hX : ∀ i, X (i + 1) = X i + d := by
    intro i; rw [hXdef, hXdef]; push_cast; ring
  have hXK : ∀ i : ℕ, X i = X 0 + i * d := by
    intro i; rw [hXdef, hXdef]; push_cast; ring
  obtain ⟨z, hzdef⟩ : ∃ z : ℕ → ℤ, ∀ i, z i = round (X i) := ⟨fun i => round (X i), fun i => rfl⟩
  have he : ∀ i, i ≤ K → |X i - (z i : ℝ)| < 1 / 8 := by
    intro i hi
    rw [hzdef, hXdef]
    exact hcon i hi
  have hm : ∀ i, i + 1 ≤ K → |d - ((z (i + 1) : ℝ) - (z i : ℝ))| < 1 / 4 := by
    intro i hi
    obtain ⟨a1, a2⟩ := abs_lt.mp (he (i + 1) hi)
    obtain ⟨b1, b2⟩ := abs_lt.mp (he i (by omega))
    have := hX i
    rw [abs_lt]; constructor <;> linarith
  have hm0 := hm 0 (by omega)
  rw [Nat.zero_add] at hm0
  have hzlin : ∀ i, i ≤ K → (z i : ℝ) = (z 0 : ℝ) + i * ((z 1 : ℝ) - (z 0 : ℝ)) := by
    intro i
    induction i with
    | zero => intro _; simp
    | succ i ih =>
      intro hi
      have ih' := ih (by omega)
      obtain ⟨a1, a2⟩ := abs_lt.mp (hm i hi)
      obtain ⟨b1, b2⟩ := abs_lt.mp hm0
      have h1 : ((z (i + 1) - z i - (z 1 - z 0) : ℤ) : ℝ) < 1 := by push_cast; linarith
      have h2 : (-1 : ℝ) < ((z (i + 1) - z i - (z 1 - z 0) : ℤ) : ℝ) := by push_cast; linarith
      have h1' : z (i + 1) - z i - (z 1 - z 0) < 1 := by exact_mod_cast h1
      have h2' : -1 < z (i + 1) - z i - (z 1 - z 0) := by exact_mod_cast h2
      have h3 : z (i + 1) - z i = z 1 - z 0 := by omega
      have h4 : ((z (i + 1) - z i : ℤ) : ℝ) = ((z 1 - z 0 : ℤ) : ℝ) := by rw [h3]
      push_cast at h4 ⊢
      linarith
  have hzK := hzlin K le_rfl
  have eK := abs_lt.mp (he K le_rfl)
  have e0 := abs_lt.mp (he 0 (by omega))
  have hxK := hXK K
  have hlt1 : (K : ℝ) * (d - ((z 1 : ℝ) - (z 0 : ℝ))) < 1 / 4 := by nlinarith [eK.1, eK.2, e0.1, e0.2]
  have hlt2 : -(1 / 4 : ℝ) < (K : ℝ) * (d - ((z 1 : ℝ) - (z 0 : ℝ))) := by nlinarith [eK.1, eK.2, e0.1, e0.2]
  have habs : (K : ℝ) * |d - ((z 1 : ℝ) - (z 0 : ℝ))| < 1 / 4 := by
    rcases abs_cases (d - ((z 1 : ℝ) - (z 0 : ℝ))) with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]; exact hlt1
    · rw [h]; linarith
  have hdi : distInt d ≤ |d - ((z 1 - z 0 : ℤ) : ℝ)| := Fresh.Localisation.distInt_le d (z 1 - z 0)
  push_cast at hdi
  have hKn : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have := mul_le_mul_of_nonneg_left hdi hKn
  linarith

theorem small_II {S : Finset ℕ} {τ0 : ℝ} (hτ0 : 0 < τ0) (hτ1 : τ0 ≤ 1) (hτ : FClear S τ0) {d1 d2 : ℝ}
    (hd1 : 0 < d1) (hd18 : d1 ≤ 1 / 8) (hfar : d1 / 2 ≤ distInt d2) :
    ∃ t, 0 < t ∧ FClear S t ∧ Clear2 d1 d2 t := by
  have hpos : 0 < distInt d2 := by linarith
  have h18 : (1 : ℝ) ≤ 1 / (8 * d1) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have hA0 : (0 : ℝ) ≤ 1 / (8 * d1) - τ0 := by linarith
  obtain ⟨n0, hn0⟩ : ∃ n0 : ℕ, n0 = ⌈1 / (8 * d1) - τ0⌉₊ := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℕ, K = ⌈1 / (4 * distInt d2)⌉₊ := ⟨_, rfl⟩
  have hn1 : 1 / (8 * d1) - τ0 ≤ (n0 : ℝ) := by rw [hn0]; exact Nat.le_ceil _
  have hn2 : (n0 : ℝ) < 1 / (8 * d1) - τ0 + 1 := by rw [hn0]; exact Nat.ceil_lt_add_one hA0
  have hK1 : 1 / (4 * distInt d2) ≤ (K : ℝ) := by rw [hK]; exact Nat.le_ceil _
  have hK2 : (K : ℝ) < 1 / (4 * distInt d2) + 1 := by
    rw [hK]; exact Nat.ceil_lt_add_one (by positivity)
  have hKm : (1 : ℝ) / 4 ≤ K * distInt d2 := by
    have e : 1 / (4 * distInt d2) * distInt d2 = 1 / 4 := by field_simp
    calc (1 : ℝ) / 4 = 1 / (4 * distInt d2) * distInt d2 := e.symm
      _ ≤ K * distInt d2 := mul_le_mul_of_nonneg_right hK1 hpos.le
  have hK3 : 1 / (4 * distInt d2) ≤ 1 / (2 * d1) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  obtain ⟨i, hiK, hi⟩ := run_lemma (c := τ0) hKm n0
  have hiR : (i : ℝ) ≤ K := by exact_mod_cast hiK
  have hd1e : d1 * (1 / (8 * d1)) = 1 / 8 := by field_simp
  have hd2e : d1 * (1 / (2 * d1)) = 1 / 2 := by field_simp
  have hlo : (0 : ℝ) + 1 / 8 ≤ d1 * (((n0 + i : ℕ) : ℝ) + τ0) := by
    have h1 : 1 / (8 * d1) ≤ (n0 : ℝ) + τ0 := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hd1.le
    have h3 : (0 : ℝ) ≤ d1 * i := by positivity
    push_cast
    nlinarith
  have hhi : d1 * (((n0 + i : ℕ) : ℝ) + τ0) ≤ (0 : ℝ) + 7 / 8 := by
    have h1 : (n0 : ℝ) + i + τ0 ≤ 1 / (8 * d1) + 1 + (1 / (2 * d1) + 1) := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hd1.le
    push_cast
    nlinarith
  refine ⟨((n0 + i : ℕ) : ℝ) + τ0, by positivity, ?_, ?_, hi⟩
  · have := fclear_add_nat S τ0 (n0 + i) hτ
    rwa [add_comm] at this
  · exact Fresh.Localisation.clear_of_window 0 (by push_cast at hlo ⊢; linarith) (by push_cast at hhi ⊢; linarith)

theorem small_I_pos {S : Finset ℕ} {τ0 : ℝ} (hτ0 : 0 < τ0) (hτ1 : τ0 ≤ 1) (hτ : FClear S τ0) (j : ℕ) (N : ℤ)
    (hlo : (N : ℝ) + 1 / 8 ≤ j * τ0) (hhi : (j : ℝ) * τ0 ≤ (N : ℝ) + 3 / 4) {d1 d2 : ℝ}
    (hd1 : 0 < d1) (hd18 : d1 ≤ 1 / 8) (he0 : (j : ℝ) ≤ d2) (he1 : d2 ≤ j + d1 / 2) :
    ∃ t, 0 < t ∧ FClear S t ∧ Clear2 d1 d2 t := by
  have h18 : (1 : ℝ) ≤ 1 / (8 * d1) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have hA0 : (0 : ℝ) ≤ 1 / (8 * d1) - τ0 := by linarith
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = ⌈1 / (8 * d1) - τ0⌉₊ := ⟨_, rfl⟩
  have hn1 : 1 / (8 * d1) - τ0 ≤ (n : ℝ) := by rw [hn]; exact Nat.le_ceil _
  have hn2 : (n : ℝ) < 1 / (8 * d1) - τ0 + 1 := by rw [hn]; exact Nat.ceil_lt_add_one hA0
  have hd1e : d1 * (1 / (8 * d1)) = 1 / 8 := by field_simp
  have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have ht0 : 0 < (n : ℝ) + τ0 := by positivity
  have hlo1 : (1 : ℝ) / 8 ≤ d1 * ((n : ℝ) + τ0) := by
    have h1 : 1 / (8 * d1) ≤ (n : ℝ) + τ0 := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hd1.le
    linarith
  have hhi1 : d1 * ((n : ℝ) + τ0) ≤ 7 / 8 := by
    have h1 : (n : ℝ) + τ0 ≤ 1 / (8 * d1) + 1 := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hd1.le
    nlinarith
  -- phase of d2
  have hε : (d2 - j) * ((n : ℝ) + τ0) ≤ 1 / 8 := by
    have h1 : (n : ℝ) + τ0 ≤ 1 / (8 * d1) + 1 := by linarith
    have h2 : (d2 - j) * ((n : ℝ) + τ0) ≤ (d1 / 2) * (1 / (8 * d1) + 1) := by
      apply mul_le_mul (by linarith) h1 ht0.le (by positivity)
    have h3 : (d1 / 2) * (1 / (8 * d1) + 1) = 1 / 16 + d1 / 2 := by field_simp; ring
    linarith
  have hε0 : 0 ≤ (d2 - j) * ((n : ℝ) + τ0) := mul_nonneg (by linarith) ht0.le
  have e : d2 * ((n : ℝ) + τ0) = (((j * n : ℕ) : ℤ) : ℝ) + ((j : ℝ) * τ0 + (d2 - j) * ((n : ℝ) + τ0)) := by
    push_cast; ring
  refine ⟨(n : ℝ) + τ0, ht0, ?_, ?_, ?_⟩
  · have := fclear_add_nat S τ0 n hτ
    rwa [add_comm] at this
  · exact Fresh.Localisation.clear_of_window 0 (by linarith) (by linarith)
  · apply Fresh.Localisation.clear_of_window (N + ((j * n : ℕ) : ℤ))
    · rw [e]; push_cast; linarith
    · rw [e]; push_cast; linarith

theorem small_I_neg {S : Finset ℕ} {τ0 : ℝ} (hτ0 : 0 < τ0) (hτ1 : τ0 ≤ 1) (hτ : FClear S τ0) (j : ℕ) (N : ℤ)
    (hlo : (N : ℝ) + 1 / 4 ≤ j * τ0) (hhi : (j : ℝ) * τ0 ≤ (N : ℝ) + 7 / 8) {d1 d2 : ℝ}
    (hd1 : 0 < d1) (hd18 : d1 ≤ 1 / 8) (he0 : d2 ≤ (j : ℝ)) (he1 : (j : ℝ) - d1 / 2 ≤ d2) :
    ∃ t, 0 < t ∧ FClear S t ∧ Clear2 d1 d2 t := by
  have h18 : (1 : ℝ) ≤ 1 / (8 * d1) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have hA0 : (0 : ℝ) ≤ 1 / (8 * d1) - τ0 := by linarith
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = ⌈1 / (8 * d1) - τ0⌉₊ := ⟨_, rfl⟩
  have hn1 : 1 / (8 * d1) - τ0 ≤ (n : ℝ) := by rw [hn]; exact Nat.le_ceil _
  have hn2 : (n : ℝ) < 1 / (8 * d1) - τ0 + 1 := by rw [hn]; exact Nat.ceil_lt_add_one hA0
  have hd1e : d1 * (1 / (8 * d1)) = 1 / 8 := by field_simp
  have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have ht0 : 0 < (n : ℝ) + τ0 := by positivity
  have hlo1 : (1 : ℝ) / 8 ≤ d1 * ((n : ℝ) + τ0) := by
    have h1 : 1 / (8 * d1) ≤ (n : ℝ) + τ0 := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hd1.le
    linarith
  have hhi1 : d1 * ((n : ℝ) + τ0) ≤ 7 / 8 := by
    have h1 : (n : ℝ) + τ0 ≤ 1 / (8 * d1) + 1 := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hd1.le
    nlinarith
  have hε : -(1 / 8 : ℝ) ≤ (d2 - j) * ((n : ℝ) + τ0) := by
    have h1 : (n : ℝ) + τ0 ≤ 1 / (8 * d1) + 1 := by linarith
    have h2 : (j - d2) * ((n : ℝ) + τ0) ≤ (d1 / 2) * (1 / (8 * d1) + 1) := by
      apply mul_le_mul (by linarith) h1 ht0.le (by positivity)
    have h3 : (d1 / 2) * (1 / (8 * d1) + 1) = 1 / 16 + d1 / 2 := by field_simp; ring
    nlinarith
  have hε0 : (d2 - j) * ((n : ℝ) + τ0) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) ht0.le
  have e : d2 * ((n : ℝ) + τ0) = (((j * n : ℕ) : ℤ) : ℝ) + ((j : ℝ) * τ0 + (d2 - j) * ((n : ℝ) + τ0)) := by
    push_cast; ring
  refine ⟨(n : ℝ) + τ0, ht0, ?_, ?_, ?_⟩
  · have := fclear_add_nat S τ0 n hτ
    rwa [add_comm] at this
  · exact Fresh.Localisation.clear_of_window 0 (by linarith) (by linarith)
  · apply Fresh.Localisation.clear_of_window (N + ((j * n : ℕ) : ℤ))
    · rw [e]; push_cast; linarith
    · rw [e]; push_cast; linarith

theorem small_A {S : Finset ℕ} {l r : ℝ} (hl : 0 < l) (hlr : l ≤ r) (hr1 : r ≤ 1)
    (hP : ∀ s, l ≤ s → s ≤ r → FClear S s) {d1 d2 : ℝ}
    (hd1 : 0 < d1) (hd18 : d1 ≤ 1 / 8) (hd2 : 1 ≤ 4 * d2 * (r - l)) :
    ∃ t, 0 < t ∧ FClear S t ∧ Clear2 d1 d2 t := by
  have hd2p : 0 < d2 := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have h18 : (1 : ℝ) ≤ 1 / (8 * d1) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have hA0 : (0 : ℝ) ≤ 1 / (8 * d1) - l := by linarith
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = ⌈1 / (8 * d1) - l⌉₊ := ⟨_, rfl⟩
  have hn1 : 1 / (8 * d1) - l ≤ (n : ℝ) := by rw [hn]; exact Nat.le_ceil _
  have hn2 : (n : ℝ) < 1 / (8 * d1) - l + 1 := by rw [hn]; exact Nat.ceil_lt_add_one hA0
  have hd1e : d1 * (1 / (8 * d1)) = 1 / 8 := by field_simp
  have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hp : (0 : ℝ) + 1 / 8 ≤ d1 * ((n : ℝ) + l) := by
    have h1 : 1 / (8 * d1) ≤ (n : ℝ) + l := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hd1.le
    linarith
  have hq : d1 * ((n : ℝ) + r) ≤ (0 : ℝ) + 7 / 8 := by
    have h1 : (n : ℝ) + r ≤ 1 / (8 * d1) + 2 := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hd1.le
    nlinarith
  have hw : 1 ≤ 4 * d2 * (((n : ℝ) + r) - ((n : ℝ) + l)) := by
    have : ((n : ℝ) + r) - ((n : ℝ) + l) = r - l := by ring
    rw [this]; exact hd2
  obtain ⟨t, h1, h2, h3⟩ := r1_rect (n := 0) (l := (n : ℝ) + l) (r := (n : ℝ) + r) (p := (n : ℝ) + l) (q := (n : ℝ) + r)
    hd1 hd2p le_rfl le_rfl (by push_cast at hp ⊢; linarith) (by push_cast at hq ⊢; linarith) hw
  refine ⟨t, by linarith, ?_, h3⟩
  apply fclear_lap S t n
  exact hP (t - n) (by linarith) (by linarith)

/-- If `d2` is within `d1/2` of an integer, that integer is at least `1` and at most `D` (when `d2 < D`). -/
theorem near_int {d1 d2 : ℝ} {D : ℕ} (hd1 : 0 < d1) (hd18 : d1 ≤ 1 / 8) (hd : d1 ≤ d2) (hD : d2 < D)
    (hfar : distInt d2 < d1 / 2) : ∃ j : ℕ, 1 ≤ j ∧ j ≤ D ∧ |d2 - j| < d1 / 2 := by
  have h1 : |d2 - (round d2 : ℝ)| < d1 / 2 := hfar
  obtain ⟨a1, a2⟩ := abs_lt.mp h1
  have hpos : (0 : ℝ) < (round d2 : ℝ) := by linarith
  have hpos' : 0 < round d2 := by exact_mod_cast hpos
  have hlt : (round d2 : ℝ) < (D : ℝ) + 1 := by linarith
  have hlt' : round d2 < (D : ℤ) + 1 := by exact_mod_cast hlt
  refine ⟨(round d2).toNat, ?_, ?_, ?_⟩
  · omega
  · omega
  · have : ((round d2).toNat : ℝ) = (round d2 : ℝ) := by
      have h := Int.toNat_of_nonneg hpos'.le
      exact_mod_cast congrArg (Int.cast : ℤ → ℝ) h
    rw [this]; exact h1

#print axioms fclear_add_nat
#print axioms fclear_lap
#print axioms ex_of_piece
#print axioms isFirst_char
#print axioms first_in_piece
#print axioms landing_in_piece
#print axioms exists_isFirst_of_lonely
#print axioms landing_of_ex
#print axioms run_lemma
#print axioms small_II
#print axioms small_I_pos
#print axioms small_I_neg
#print axioms small_A
#print axioms near_int

end Fresh.OneMover
