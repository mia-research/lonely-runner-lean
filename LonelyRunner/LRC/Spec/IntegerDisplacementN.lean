import LonelyRunner.LRC.Spec.SeparationN
import LonelyRunner.LRC.Spec.IntegerGridN
import LonelyRunner.LRC.Spec.PinchOpenN

/-!
# The displacement of the isolation at an integer arrangement, in slot residue and shift

2026-10-02 (running log E299).  An integer arrangement is on the grid `D = 1`, no deviation.  At the grid instant
`t₀ = a/8` (`a` a positive integer) reading `x` sits in slot `ρ_x = a·x mod 8`.  A reading `c` with `8 ∣ c` sits in the
subject's slot (`ρ = 0`).  The isolation is displaced to `t₁ = a/8 + 1/(8c) = (8K+1)/(8c)`, `K = a·c/8`: the leaving edge
of `c`.  Every other reading `x` has moved by `x/c` eighths of a lap.

* `lonely_of_displacement`: if every other reading has slot `ρ ≥ 1` and `ρ + x/c ≤ 7`, all readings are clear at `t₁`.
* `slower_clear_iff`: a reading `x < c` is clear at `t₁` exactly when its slot is `1 … 6`: the slower obstruction is
  exactly slot `7` (edge push) or slot `0`.
* `clear_at_exit_iff`: for every reading, clear at `t₁` iff `∀ z, c ≤ |x·(a·c+1) − 8·c·z|`.
* `inWay_at_grid_iff`: at the grid instant `a/8`, `a` odd, a reading is in the way exactly when `8 ∣ x`.
* `inWay_at_exit_iff`: the readings in the way at that next instant, exactly.
* `nextOpening_at_grid`, `move_at_grid`: the cascade's move from `a/8` is `a/8 + 1/(8c)`, `c` the slowest multiple of `8`.
* `lonely8_example`: the arrangement with readings `1,2,3,4,5,7,8` (speeds 1,2,3,4,5,6,8,9 for subject speed `s = 1`; any `s > 0` gives the same) is lonely at `9/56`,
  the leaving edge of the reading `7`, where the slot-`7` reading `7` was carried by the first displacement.

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.IntegerDisplacement

open LRC.Order8Skeleton LRC.IntegerGrid

theorem lonely_of_displacement (S : Finset ℕ) {c : ℕ} (hc8 : 8 ∣ c) (hc : 0 < c) (a : ℕ)
    (hres : ∀ x ∈ S, x ≠ c → 1 ≤ (a * x) % 8 ∧ (((a * x) % 8 : ℕ) : ℝ) + (x : ℝ) / c ≤ 7) :
    ∀ x ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((x : ℝ) * ((a : ℝ) / 8 + 1 / (8 * (c : ℝ)))) := by
  obtain ⟨c', hc'⟩ := hc8
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hK : ((c : ℕ) : ℝ) * ((a : ℝ) / 8) = (((c' * a : ℕ) : ℤ) : ℝ) := by
    rw [hc']; push_cast; ring
  have key := LRC.Separation.lonely_of_separation S (fun i : ℕ => (i : ℝ)) (c := c) (t0 := (a : ℝ) / 8)
    (K := ((c' * a : ℕ) : ℤ)) hcR hK (fun i _ => Nat.cast_nonneg i) (by
      intro x hx hxc
      obtain ⟨h1, h2⟩ := hres x hx hxc
      refine ⟨(((a * x) / 8 : ℕ) : ℤ), ?_, ?_⟩
      · have hd : ((a * x : ℕ) : ℝ) = 8 * (((a * x) / 8 : ℕ) : ℝ) + (((a * x) % 8 : ℕ) : ℝ) := by
          exact_mod_cast (Nat.div_add_mod (a * x) 8).symm
        have h1' : (1 : ℝ) ≤ (((a * x) % 8 : ℕ) : ℝ) := by exact_mod_cast h1
        have e : (x : ℝ) * ((a : ℝ) / 8) = ((a * x : ℕ) : ℝ) / 8 := by push_cast; ring
        simp only [Int.cast_natCast]
        rw [e]; linarith
      · have hd : ((a * x : ℕ) : ℝ) = 8 * (((a * x) / 8 : ℕ) : ℝ) + (((a * x) % 8 : ℕ) : ℝ) := by
          exact_mod_cast (Nat.div_add_mod (a * x) 8).symm
        have e : (x : ℝ) * ((a : ℝ) / 8) = ((a * x : ℕ) : ℝ) / 8 := by push_cast; ring
        have e2 : (x : ℝ) / (8 * (c : ℝ)) = ((x : ℝ) / c) / 8 := by field_simp
        simp only [Int.cast_natCast]
        rw [e, e2]; linarith)
  exact key

theorem slower_clear_iff {x c a : ℕ} (hx : 0 < x) (hxc : x < c) (hc : 0 < c) :
    (8 : ℝ)⁻¹ ≤ circDist ((x : ℝ) * ((a : ℝ) / 8 + 1 / (8 * (c : ℝ)))) ↔
      1 ≤ (a * x) % 8 ∧ (a * x) % 8 ≤ 6 := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  set N : ℤ := (((a * x) / 8 : ℕ) : ℤ) with hN
  set ρ : ℕ := (a * x) % 8 with hρ
  have hρ8 : ρ < 8 := Nat.mod_lt _ (by norm_num)
  have hd : ((a * x : ℕ) : ℝ) = 8 * (((a * x) / 8 : ℕ) : ℝ) + (ρ : ℝ) := by
    exact_mod_cast (Nat.div_add_mod (a * x) 8).symm
  set δ : ℝ := (x : ℝ) / (8 * (c : ℝ)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ < 1 / 8 := by
    rw [hδ, div_lt_div_iff₀ (by positivity) (by norm_num)]
    have : (x : ℝ) < c := by exact_mod_cast hxc
    nlinarith
  have e : (x : ℝ) * ((a : ℝ) / 8 + 1 / (8 * (c : ℝ))) = ((ρ : ℝ) / 8 + δ) + (N : ℝ) := by
    have e1 : (x : ℝ) * ((a : ℝ) / 8) = ((a * x : ℕ) : ℝ) / 8 := by push_cast; ring
    have e2 : (x : ℝ) * (1 / (8 * (c : ℝ))) = δ := by rw [hδ]; ring
    have hNR : (N : ℝ) = (((a * x) / 8 : ℕ) : ℝ) := by rw [hN]; exact Int.cast_natCast _
    rw [mul_add, e1, e2, hd, hNR]; ring
  rw [e, LRC.PinchOpen.circDist_add_int_po]
  have hρR : (ρ : ℝ) ≤ 7 := by exact_mod_cast (by omega : ρ ≤ 7)
  constructor
  · intro h
    by_contra hn
    have hcase : ρ = 0 ∨ ρ = 7 := by omega
    rcases hcase with h0 | h7
    · have hρ0 : (ρ : ℝ) = 0 := by exact_mod_cast h0
      have key := ConstructionN.circDist_le_abs_sub_int ((ρ : ℝ) / 8 + δ) 0
      rw [hρ0] at key h
      have e0 : |(0 : ℝ) / 8 + δ - ((0 : ℤ) : ℝ)| = δ := by
        rw [abs_of_pos (by push_cast; linarith)]; push_cast; ring
      have e00 : (0 : ℝ) / 8 + δ = δ := by ring
      rw [e00] at h
      rw [e0] at key
      rw [e00] at key
      linarith
    · have hρ7 : (ρ : ℝ) = 7 := by exact_mod_cast h7
      have key := ConstructionN.circDist_le_abs_sub_int ((ρ : ℝ) / 8 + δ) 1
      rw [hρ7] at key h
      have e1 : |(7 : ℝ) / 8 + δ - ((1 : ℤ) : ℝ)| = 1 / 8 - δ := by
        rw [abs_of_neg (by push_cast; linarith)]; push_cast; ring
      linarith
  · intro ⟨h1, h6⟩
    have h1' : (1 : ℝ) ≤ ρ := by exact_mod_cast h1
    have h6' : (ρ : ℝ) ≤ 6 := by exact_mod_cast h6
    exact LRC.TwoPinner.clear_of_band (N := 0) (by push_cast; linarith) (by push_cast; linarith)

theorem clear_at_exit_iff {c a x : ℕ} (hc : 0 < c) :
    (8 : ℝ)⁻¹ ≤ circDist ((x : ℝ) * ((a : ℝ) / 8 + 1 / (8 * (c : ℝ)))) ↔
      ∀ z : ℤ, (c : ℤ) ≤ |(x : ℤ) * ((a : ℤ) * c + 1) - 8 * c * z| := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have e : (x : ℝ) * ((a : ℝ) / 8 + 1 / (8 * (c : ℝ))) =
      ((x : ℤ) : ℝ) * ((((a : ℤ) * c + 1 : ℤ) : ℝ) / (8 * (c : ℝ))) := by
    push_cast; field_simp
  rw [e]
  exact clear_rational_iff hc _ _

theorem lonely8_example : Lonely8 ({1, 2, 3, 4, 5, 7, 8} : Finset ℕ) := by
  refine ⟨9 / 56, by norm_num, fun d hd => ?_⟩
  have e : (d : ℝ) * (9 / 56) = ((d : ℤ) : ℝ) * (((9 : ℤ) : ℝ) / (8 * ((7 : ℕ) : ℝ))) := by
    push_cast; ring
  rw [e, clear_rational_iff (by norm_num)]
  intro z
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (rw [le_abs]; push_cast; omega)

open MomentIterationN in
/-- At `t₁ = a/8 + 1/(8c)` a reading is in the way exactly when `c > |x(ac+1) − 8cz|` for some `z`. -/
theorem inWay_at_exit_iff {c a x : ℕ} (hc : 0 < c) :
    inWay 8 (x : ℝ) ((a : ℝ) / 8 + 1 / (8 * (c : ℝ))) ↔
      ∃ z : ℤ, |(x : ℤ) * ((a : ℤ) * c + 1) - 8 * c * z| < (c : ℤ) := by
  unfold inWay
  have h := clear_at_exit_iff (c := c) (a := a) (x := x) hc
  have h8 : (((8 : ℕ) : ℝ))⁻¹ = (8 : ℝ)⁻¹ := by norm_num
  rw [h8, ← not_le, h]
  push Not
  rfl

open MomentIterationN in
theorem inWay_at_grid_iff {a x : ℕ} (ha : Odd a) :
    inWay 8 (x : ℝ) ((a : ℝ) / 8) ↔ 8 ∣ x := by
  have hcop : Nat.Coprime 8 a := by
    have := Nat.Coprime.pow_left 3 (Nat.coprime_two_left.mpr ha)
    simpa using this
  have e : (x : ℝ) * ((a : ℝ) / 8) = (((a * x : ℕ) : ℤ) : ℝ) / ((8 : ℕ) : ℝ) := by push_cast; ring
  unfold inWay
  rw [e]
  constructor
  · intro h
    by_contra hn
    have hn' : ¬ 8 ∣ a * x := fun hd => hn (hcop.dvd_of_dvd_mul_left hd)
    have := ConstructionN.circDist_int_div (n := 8) (by norm_num) (c := ((a * x : ℕ) : ℤ))
      (by exact_mod_cast hn')
    simp only [Nat.cast_ofNat] at this h
    linarith
  · intro h
    have h' : (8 : ℤ) ∣ ((a * x : ℕ) : ℤ) := by exact_mod_cast Dvd.dvd.mul_left h a
    have := ConstructionN.circDist_int_div_of_dvd (n := 8) (by norm_num) h'
    rw [this]; norm_num

open MomentIterationN in
theorem nextOpening_at_grid {a x : ℕ} (hx : 0 < x) (hx8 : 8 ∣ x) :
    nextOpening 8 (x : ℝ) ((a : ℝ) / 8) = (a : ℝ) / 8 + 1 / (8 * (x : ℝ)) := by
  letI : Fact (2 ≤ 8) := ⟨by norm_num⟩
  obtain ⟨x', hx'⟩ := hx8
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hK : (x : ℝ) * ((a : ℝ) / 8) = (((x' * a : ℕ) : ℤ) : ℝ) := by rw [hx']; push_cast; ring
  rw [nextOpening_eq (n := 8) hxR (k := ((x' * a : ℕ) : ℤ))]
  · rw [← hK]; push_cast; field_simp
  · rw [hK]; simp

open MomentIterationN in
theorem move_at_grid (S : Finset ℕ) {c : ℕ} (hcS : c ∈ S) (hc8 : 8 ∣ c) (hc : 0 < c)
    (hmin : ∀ x ∈ S, 8 ∣ x → c ≤ x) (hpos : ∀ x ∈ S, 0 < x) {a : ℕ} (ha : Odd a) :
    move 8 (S.image (fun x : ℕ => (x : ℝ))) ((a : ℝ) / 8) = (a : ℝ) / 8 + 1 / (8 * (c : ℝ)) := by
  letI : Fact (2 ≤ 8) := ⟨by norm_num⟩
  classical
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hle : (a : ℝ) / 8 ≤ (a : ℝ) / 8 + 1 / (8 * (c : ℝ)) := by
    have : 0 < 1 / (8 * (c : ℝ)) := by positivity
    linarith
  apply le_antisymm
  · unfold move
    rw [Finset.fold_max_le]
    refine ⟨hle, ?_⟩
    intro d hd
    obtain ⟨x, hxS, rfl⟩ := Finset.mem_image.mp hd
    split_ifs with h
    · have hx8 := (inWay_at_grid_iff ha).mp h
      rw [nextOpening_at_grid (hpos x hxS) hx8]
      have hxR : (0 : ℝ) < x := by exact_mod_cast hpos x hxS
      have hcx : (c : ℝ) ≤ x := by exact_mod_cast hmin x hxS hx8
      have : 1 / (8 * (x : ℝ)) ≤ 1 / (8 * (c : ℝ)) := by
        apply one_div_le_one_div_of_le (by positivity)
        linarith
      linarith
    · exact hle
  · have hw : inWay 8 (c : ℝ) ((a : ℝ) / 8) := (inWay_at_grid_iff ha).mpr hc8
    have hmem : (c : ℝ) ∈ S.image (fun x : ℕ => (x : ℝ)) := Finset.mem_image.mpr ⟨c, hcS, rfl⟩
    have := nextOpening_le_move hmem hw
    rwa [nextOpening_at_grid hc hc8] at this

end LRC.IntegerDisplacement
