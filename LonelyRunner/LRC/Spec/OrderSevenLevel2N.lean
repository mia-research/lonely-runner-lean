import LonelyRunner.LRC.Spec.OrderSevenGridN

/-!
# Order seven at level 2: at most four speeds prime to 7, the rest of 7-adic valuation 1

`table2` (kernel-checked): for all units `u2, u3, u4 mod 49` there is a unit `k mod 49` with `1, u2, u3, u4` all in band
at `k/49`.  Scaling by the inverse of `u1` extends it to any four units.  Speeds `7 d'` with `7 ∤ d'` are automatically
in band at level 2 (`gridOK_two_val1`).

`lonely_level_two`: a set whose speeds prime to 7 number at most four, and whose other speeds are `7 d'` with `7 ∤ d'`,
is lonely at some `k/49`.  (experiments/n7_native log E19.)

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.O7Grid

def unit7 (u : ℕ) : Bool := u % 7 != 0

def ok2 (k u : ℕ) : Bool := decide (GridOK 2 k u)

/-- The normalised level-2 table. -/
def table2 : Bool :=
  (List.range 49).all fun u2 => !unit7 u2 ||
  (List.range 49).all fun u3 => !unit7 u3 ||
  (List.range 49).all fun u4 => !unit7 u4 ||
  (List.range 49).any fun k => unit7 k && ok2 k 1 && ok2 k u2 && ok2 k u3 && ok2 k u4

theorem table2_ok : table2 = true := by decide +kernel

theorem table2_spec {u2 u3 u4 : ℕ} (h2 : u2 < 49) (h3 : u3 < 49) (h4 : u4 < 49) (n2 : u2 % 7 ≠ 0)
    (n3 : u3 % 7 ≠ 0) (n4 : u4 % 7 ≠ 0) :
    ∃ k, k % 7 ≠ 0 ∧ GridOK 2 k 1 ∧ GridOK 2 k u2 ∧ GridOK 2 k u3 ∧ GridOK 2 k u4 := by
  have h := table2_ok
  simp only [table2, List.all_eq_true, List.mem_range, List.any_eq_true, Bool.or_eq_true, Bool.not_eq_true',
    unit7, ok2, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
  rcases h u2 h2 with h | h
  · exact absurd h (by simpa using n2)
  rcases h u3 h3 with h | h
  · exact absurd h (by simpa using n3)
  rcases h u4 h4 with h | h
  · exact absurd h (by simpa using n4)
  obtain ⟨k, -, ⟨⟨⟨⟨hk, a⟩, b⟩, c⟩, d⟩⟩ := h
  exact ⟨k, by simpa using hk, a, b, c, d⟩

theorem inv49 : ∀ u, u < 49 → u % 7 ≠ 0 → ∃ c, c < 49 ∧ c * u % 49 = 1 := by decide

theorem not7_iff {x : ℕ} : ¬ 7 ∣ x ↔ x % 7 ≠ 0 := by
  rw [Nat.dvd_iff_mod_eq_zero]

theorem four_units {u1 u2 u3 u4 : ℕ} (h1 : ¬ 7 ∣ u1) (h2 : ¬ 7 ∣ u2) (h3 : ¬ 7 ∣ u3) (h4 : ¬ 7 ∣ u4) :
    ∃ k, ¬ 7 ∣ k ∧ GridOK 2 k u1 ∧ GridOK 2 k u2 ∧ GridOK 2 k u3 ∧ GridOK 2 k u4 := by
  have hm : ∀ {x}, ¬ 7 ∣ x → (x % 49) % 7 ≠ 0 := fun {x} hx => by
    rw [show (49 : ℕ) = 7 * 7 by norm_num, Nat.mod_mul_right_mod]; exact not7_iff.mp hx
  obtain ⟨c, hc, hcu⟩ := inv49 (u1 % 49) (Nat.mod_lt _ (by norm_num)) (hm h1)
  have hc7 : ¬ 7 ∣ c := by
    intro hd
    have : 7 ∣ c * (u1 % 49) % 49 := by
      rw [show (49 : ℕ) = 7 * 7 by norm_num]
      exact (Nat.dvd_mod_iff (dvd_mul_left 7 7)).mpr (dvd_mul_of_dvd_left hd _)
    rw [hcu] at this; norm_num at this
  have hv : ∀ {x}, ¬ 7 ∣ x → (c * x % 49) % 7 ≠ 0 := fun {x} hx => by
    rw [show (49 : ℕ) = 7 * 7 by norm_num, Nat.mod_mul_right_mod]
    exact not7_iff.mp (fun hd => ((Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp hd).elim hc7 hx)
  have hv1 : c * u1 % 49 = 1 := by rw [Nat.mul_mod, Nat.mod_eq_of_lt hc] at hcu ⊢; simpa [Nat.mul_mod] using hcu
  obtain ⟨k, hk, a1, a2, a3, a4⟩ := table2_spec (Nat.mod_lt (c * u2) (by norm_num)) (Nat.mod_lt (c * u3) (by norm_num))
    (Nat.mod_lt (c * u4) (by norm_num)) (hv h2) (hv h3) (hv h4)
  have tr : ∀ {x}, GridOK 2 k (c * x % 49) → GridOK 2 (c * k) x := fun {x} hx => by
    rw [gridOK_scale, gridOK_mod]; exact hx
  refine ⟨c * k, fun hd => ((Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp hd).elim hc7 (not7_iff.mpr hk),
    tr (by rw [hv1]; exact a1), tr a2, tr a3, tr a4⟩

/-- At most four units: one unit instant of level 2 puts all of them in band. -/
theorem units_level_two {U : Finset ℕ} (hc : U.card ≤ 4) (hu : ∀ u ∈ U, ¬ 7 ∣ u) :
    ∃ k, ¬ 7 ∣ k ∧ ∀ u ∈ U, GridOK 2 k u := by
  have hl : U.toList.length ≤ 4 := by rw [Finset.length_toList]; exact hc
  have hmem : ∀ u, u ∈ U ↔ u ∈ U.toList := fun u => (Finset.mem_toList).symm
  have hu' : ∀ u ∈ U.toList, ¬ 7 ∣ u := fun u h => hu u ((hmem u).mpr h)
  generalize U.toList = l at hl hmem hu'
  match l, hl, hmem, hu' with
  | [], _, hmem, _ => exact ⟨1, by norm_num, fun u h => by simp [hmem] at h⟩
  | [a], _, hmem, hu' =>
    obtain ⟨k, hk, x, -, -, -⟩ := four_units (hu' a (by simp)) (hu' a (by simp)) (hu' a (by simp)) (hu' a (by simp))
    exact ⟨k, hk, fun u h => by simp only [hmem, List.mem_singleton] at h; subst h; exact x⟩
  | [a, b], _, hmem, hu' =>
    obtain ⟨k, hk, x, y, -, -⟩ := four_units (hu' a (by simp)) (hu' b (by simp)) (hu' a (by simp)) (hu' a (by simp))
    exact ⟨k, hk, fun u h => by
      simp only [hmem, List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl <;> assumption⟩
  | [a, b, c], _, hmem, hu' =>
    obtain ⟨k, hk, x, y, z, -⟩ := four_units (hu' a (by simp)) (hu' b (by simp)) (hu' c (by simp)) (hu' a (by simp))
    exact ⟨k, hk, fun u h => by
      simp only [hmem, List.mem_cons, List.not_mem_nil, or_false] at h; rcases h with rfl | rfl | rfl <;> assumption⟩
  | [a, b, c, d], _, hmem, hu' =>
    obtain ⟨k, hk, x, y, z, w⟩ := four_units (hu' a (by simp)) (hu' b (by simp)) (hu' c (by simp)) (hu' d (by simp))
    exact ⟨k, hk, fun u h => by
      simp only [hmem, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl <;> assumption⟩
  | _ :: _ :: _ :: _ :: _ :: _, hl, _, _ => simp at hl; omega

/-- **Order seven at level 2.**  At most four speeds prime to 7, every other speed `7 d'` with `7 ∤ d'`: lonely at some
`k/49`. -/
theorem lonely_level_two {S : Finset ℕ} (hU : (S.filter (fun d => ¬ 7 ∣ d)).card ≤ 4)
    (hM : ∀ d ∈ S, 7 ∣ d → ¬ 49 ∣ d) :
    ∃ t : ℝ, ∀ d ∈ S, (1 : ℝ) / 7 ≤ circDist ((d : ℝ) * t) := by
  obtain ⟨k, hk, hkU⟩ := units_level_two hU (fun u hu => (Finset.mem_filter.mp hu).2)
  refine lonely_of_gridOK (a := 2) (k := k) (by norm_num) (fun d hd => ?_)
  by_cases h7 : 7 ∣ d
  · obtain ⟨d', rfl⟩ := h7
    have hd' : ¬ 7 ∣ d' := fun ⟨e, he⟩ => hM _ hd (dvd_mul_right 7 d') ⟨e, by rw [he]; ring⟩
    exact gridOK_two_val1 hd' hk
  · exact hkU d (Finset.mem_filter.mpr ⟨hd, h7⟩)

end LRC.O7Grid
