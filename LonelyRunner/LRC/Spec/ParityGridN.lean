import LonelyRunner.LRC.Spec.ParityCoverN

set_option linter.style.longLine false

/-!
# The grid lemma and the reduction points (order eight)

2026-10-06 (running log E403).  The isolation is taken at the eight shifts `k/8`, displaced by
`τ/8` (`Blocked`).  The offset `τ` is a grid point `m/w` of an odd non-multiple `w`: there `w`
reads `w·τ/8 + w·k/8 = (m + w·k)/8`, a whole number of eighths, so `w` stands exactly at the edge
of the subject's slot and is in the way at a shift `k` only when `8 ∣ m + w·k`.  Since `w` is odd,
one `k` mod 8 does this, and `w` blocks at most one shift instead of two
(`odd_blocked_le_one_at_grid`).

**The grid lemma** (`grid_point`).  For odd `w` and at most three numbers `c`, none divisible by
`w`, some grid point `m/w` (`m < w`) has `‖c·m/w‖ ≥ 1/8` for all of them.  At `m/w` the reading
`c` stands at the residue `c·m mod w` (`clear_of_not_gridNear`, from `RationalN.lonely_of_ratWorks`).
With `g = gcd(c, w)` and `q = w/g` (odd, at least `3`), `m ↦ (m / q, (c/g)·m mod q)` is injective
on the points where `c` is near the lap line and lands in `range g × N_q`, `N_q` the residues `s < q`
with `8s < q` or `8(q − s) < q`; `#N_q ≤ 2⌊(q − 1)/8⌋ + 1`, so `3·#(near points of c) ≤ g·q = w`
(`three_mul_card_gridBad_le`).  Every `c` is near the lap line at `m = 0`, so three of them are near
at most `w − 3` of the points `m ∈ [1, w − 1]` (`grid_point_Ico`).  A count over the grid points,
used as a tool.

**The reduction-point corollary** (`lonely_eight_of_grid`).  A set with at most three multiples of
`8` and at most four non-multiples, none `≡ 4 (mod 8)`, one of them an odd `w` dividing no cofactor
of a multiple: `grid_point` on the cofactors gives `m`, and `τ = (m + w)/w` clears every cofactor
(a whole number of laps from `m/w`).  There `w` blocks at most one shift and each other non-multiple,
odd or `≡ 2 (mod 4)`, at most two (`card_blocked_le_two_of_not_four`, from `card_bad_le`), so at most
`7` of the `8` shifts are blocked and the set is lonely at `(τ + k)/8` (`lonely_eight_of_free_at`,
the pattern of `lonely_eight_of_eighth_free` at one fixed offset).  A count over the shifts, used
as a tool.

Everything here is proved; no `sorry`, no `native_decide`.
-/


namespace LRC.ParityDescent

open ConstructionN LRC.Descent

/-! ## Residues near the lap line -/

/-- The residue `s` of a reading over the modulus `q` is **near the lap line** when `8s < q` or
`8(q − s) < q`, written `7q < 8s`. -/
def NearEdge (q s : ℕ) : Prop := 8 * s < q ∨ 7 * q < 8 * s

instance (q s : ℕ) : Decidable (NearEdge q s) := by unfold NearEdge; infer_instance

/-- Scaling modulus and residue by `g > 0` does not change nearness. -/
theorem nearEdge_mul_iff {g q s : ℕ} (hg : 0 < g) : NearEdge (g * q) (g * s) ↔ NearEdge q s := by
  unfold NearEdge
  have e1 : 8 * (g * s) = g * (8 * s) := by ring
  have e2 : 7 * (g * q) = g * (7 * q) := by ring
  rw [e1, e2, Nat.mul_lt_mul_left hg, Nat.mul_lt_mul_left hg]

/-- **At most `2⌊(q − 1)/8⌋ + 1` residues mod `q` are near the lap line.** -/
theorem card_nearEdge_le (q : ℕ) :
    ((Finset.range q).filter (fun s => NearEdge q s)).card ≤ 2 * ((q - 1) / 8) + 1 := by
  classical
  have hsub : (Finset.range q).filter (fun s => NearEdge q s) ⊆
      Finset.range ((q - 1) / 8 + 1) ∪ Finset.Ico (q - (q - 1) / 8) q := by
    intro s hs
    simp only [Finset.mem_filter, Finset.mem_range, NearEdge] at hs
    simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
    omega
  calc ((Finset.range q).filter (fun s => NearEdge q s)).card
      ≤ (Finset.range ((q - 1) / 8 + 1) ∪ Finset.Ico (q - (q - 1) / 8) q).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.range ((q - 1) / 8 + 1)).card + (Finset.Ico (q - (q - 1) / 8) q).card :=
        Finset.card_union_le _ _
    _ = ((q - 1) / 8 + 1) + (q - (q - (q - 1) / 8)) := by rw [Finset.card_range, Nat.card_Ico]
    _ ≤ 2 * ((q - 1) / 8) + 1 := by omega

/-! ## The grid points `m/w` -/

/-- At the grid point `m/w` the reading `c` stands at the residue `c·m mod w`; it is **near the lap
line** there when that residue is. -/
def GridNear (w c m : ℕ) : Prop := NearEdge w (c * m % w)

instance (w c m : ℕ) : Decidable (GridNear w c m) := by unfold GridNear; infer_instance

/-- **A reading off the lap line at a grid point clears `1/8`.** -/
theorem clear_of_not_gridNear {w c m : ℕ} (hw : 0 < w) (h : ¬ GridNear w c m) :
    (8 : ℝ)⁻¹ ≤ circDist ((c : ℝ) * m / w) := by
  haveI : Fact (2 ≤ 8) := ⟨by norm_num⟩
  unfold GridNear NearEdge at h
  push Not at h
  have hr : LRC.RationalN.ratWorks 8 [c] m w = true := by
    simp only [LRC.RationalN.ratWorks, List.all_cons, List.all_nil, Bool.and_true,
      Bool.and_eq_true, decide_eq_true_eq]
    omega
  have h8 := LRC.RationalN.lonely_of_ratWorks (n := 8) [c] m w hw hr c (by simp)
  rw [mul_div_assoc]
  exact_mod_cast h8

/-- The grid points `m < w` at which `c` is near the lap line. -/
def gridBad (w c : ℕ) : Finset ℕ := (Finset.range w).filter (fun m => GridNear w c m)

theorem zero_mem_gridBad {w : ℕ} (hw : 0 < w) (c : ℕ) : 0 ∈ gridBad w c := by
  simp only [gridBad, GridNear, NearEdge, Finset.mem_filter, Finset.mem_range]
  simp only [mul_zero, Nat.zero_mod]
  omega

/-- **A reading `c` with `w ∤ c` is near the lap line at no more than a third of the grid
points.**  With `g = gcd(c, w)`, `q = w/g ≥ 3` and `c' = c/g` coprime to `q`, the map
`m ↦ (m / q, c'·m mod q)` is injective on the near points and lands in `range g × N_q`. -/
theorem three_mul_card_gridBad_le {w c : ℕ} (hw : ¬ 2 ∣ w) (hc : ¬ w ∣ c) :
    3 * (gridBad w c).card ≤ w := by
  classical
  have hw0 : 0 < w := by omega
  set g := Nat.gcd c w with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right c hw0
  set q := w / g with hq
  set c' := c / g with hc'
  have hwq : w = g * q := (Nat.mul_div_cancel' (Nat.gcd_dvd_right c w)).symm
  have hcc : c = g * c' := (Nat.mul_div_cancel' (Nat.gcd_dvd_left c w)).symm
  have hcop : Nat.Coprime c' q := Nat.coprime_div_gcd_div_gcd hg0
  clear_value c' q
  have hq3 : 3 ≤ q := by
    have h0 : q ≠ 0 := by
      intro h; rw [h, mul_zero] at hwq; omega
    have h1 : q ≠ 1 := by
      intro h
      rw [h, mul_one] at hwq
      exact hc (hwq ▸ Nat.gcd_dvd_left c w)
    have h2 : q ≠ 2 := by
      intro h
      rw [h] at hwq
      exact hw ⟨g, by rw [hwq]; ring⟩
    omega
  set N := (Finset.range q).filter (fun s => NearEdge q s) with hN
  have hres : ∀ m, c * m % w = g * (c' * m % q) := by
    intro m
    rw [hcc, hwq, mul_assoc, Nat.mul_mod_mul_left]
  have hmaps : Set.MapsTo (fun m => (m / q, c' * m % q)) (gridBad w c : Set ℕ)
      (Finset.range g ×ˢ N : Finset (ℕ × ℕ)) := by
    intro m hm
    simp only [gridBad, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hm
    obtain ⟨hmw, hnear⟩ := hm
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range, hN,
      Finset.mem_filter]
    refine ⟨Nat.div_lt_of_lt_mul (by rw [mul_comm]; rw [← hwq]; exact hmw),
      Nat.mod_lt _ (by omega), ?_⟩
    unfold GridNear at hnear
    rw [hres, hwq] at hnear
    exact (nearEdge_mul_iff hg0).mp hnear
  have hinj : Set.InjOn (fun m => (m / q, c' * m % q)) (gridBad w c : Set ℕ) := by
    intro a _ b _ hab
    simp only [Prod.mk.injEq] at hab
    obtain ⟨h1, h2⟩ := hab
    have hmod : a ≡ b [MOD q] := Nat.ModEq.cancel_left_of_coprime (Nat.coprime_comm.mp hcop) h2
    rw [← Nat.div_add_mod a q, ← Nat.div_add_mod b q, h1, hmod]
  have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Finset.card_product, Finset.card_range] at hcard
  have hNc := card_nearEdge_le q
  rw [← hN] at hNc
  have h3 : 3 * N.card ≤ q := by omega
  calc 3 * (gridBad w c).card ≤ 3 * (g * N.card) := Nat.mul_le_mul_left 3 hcard
    _ = g * (3 * N.card) := by ring
    _ ≤ g * q := Nat.mul_le_mul_left g h3
    _ = w := hwq.symm

/-- **The grid lemma, with `m ∈ [1, w − 1]`.** -/
theorem grid_point_Ico {w : ℕ} (hw : ¬ 2 ∣ w) (C : Finset ℕ) (hC : C.card ≤ 3)
    (hnd : ∀ c ∈ C, ¬ w ∣ c) (hne : C.Nonempty) :
    ∃ m : ℕ, 1 ≤ m ∧ m < w ∧ ∀ c ∈ C, (8 : ℝ)⁻¹ ≤ circDist ((c : ℝ) * m / w) := by
  classical
  obtain ⟨c₀, hc₀⟩ := hne
  have hw3 : 3 ≤ w := by
    have h1 : w ≠ 1 := fun h => hnd c₀ hc₀ (h ▸ one_dvd c₀)
    have h0 : w ≠ 0 := fun h => hw ⟨0, by omega⟩
    have h2 : w ≠ 2 := fun h => hw ⟨1, by omega⟩
    omega
  have hw0 : 0 < w := by omega
  set T := C.biUnion (fun c => (gridBad w c).erase 0) with hT
  have hTe : ∀ c ∈ C, 3 * ((gridBad w c).erase 0).card ≤ w - 3 := by
    intro c hc
    rw [Finset.card_erase_of_mem (zero_mem_gridBad hw0 c)]
    have h1 := three_mul_card_gridBad_le hw (hnd c hc)
    have h2 : 1 ≤ (gridBad w c).card := Finset.card_pos.mpr ⟨0, zero_mem_gridBad hw0 c⟩
    omega
  have hTc : 3 * T.card ≤ 3 * (w - 3) := by
    calc 3 * T.card ≤ 3 * ∑ c ∈ C, ((gridBad w c).erase 0).card :=
          Nat.mul_le_mul_left 3 Finset.card_biUnion_le
      _ = ∑ c ∈ C, 3 * ((gridBad w c).erase 0).card := by rw [Finset.mul_sum]
      _ ≤ ∑ _c ∈ C, (w - 3) := Finset.sum_le_sum hTe
      _ = C.card * (w - 3) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ 3 * (w - 3) := Nat.mul_le_mul_right _ hC
  have hlt : T.card < (Finset.Ico 1 w).card := by rw [Nat.card_Ico]; omega
  obtain ⟨m, hm, hmT⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  rw [Finset.mem_Ico] at hm
  refine ⟨m, hm.1, hm.2, fun c hc => clear_of_not_gridNear hw0 fun hnear => hmT ?_⟩
  exact Finset.mem_biUnion.mpr ⟨c, hc, Finset.mem_erase.mpr ⟨by omega,
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hm.2, hnear⟩⟩⟩

/-- **Grid lemma.**  For odd `w` and at most three numbers `c`, none divisible by `w`, some grid
point `m/w` with `m < w` has `‖c·m/w‖ ≥ 1/8` for every `c`. -/
theorem grid_point {w : ℕ} (hw : ¬ 2 ∣ w) (C : Finset ℕ) (hC : C.card ≤ 3) (hnd : ∀ c ∈ C, ¬ w ∣ c) :
    ∃ m : ℕ, m < w ∧ ∀ c ∈ C, (8 : ℝ)⁻¹ ≤ circDist ((c : ℝ) * m / w) := by
  rcases C.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, by omega, by simp⟩
  · obtain ⟨m, -, hm, h⟩ := grid_point_Ico hw C hC hnd hne
    exact ⟨m, hm, h⟩

/-! ## The odd reading at its own grid point -/

/-- At `τ = m/w`, the reading `w` is in the way at shift `k` only when `8 ∣ m + w·k`. -/
theorem eight_dvd_of_blocked_at_grid {w : ℕ} (hw0 : 0 < w) (m k : ℕ)
    (h : Blocked ((m : ℝ) / w) w k) : 8 ∣ m + w * k := by
  by_contra hnd
  have hnd' : ¬ ((8 : ℕ) : ℤ) ∣ ((m + w * k : ℕ) : ℤ) := by exact_mod_cast hnd
  have hc := circDist_int_div (n := 8) (by norm_num) hnd'
  unfold Blocked at h
  have hw' : (w : ℝ) ≠ 0 := by exact_mod_cast hw0.ne'
  have heq : (w : ℝ) * ((m : ℝ) / w) / 8 + (w : ℝ) * (k : ℝ) / 8 =
      (((m + w * k : ℕ) : ℤ) : ℝ) / ((8 : ℕ) : ℝ) := by
    push_cast; field_simp
  rw [heq] at h
  have h8 : ((8 : ℕ) : ℝ)⁻¹ = (8 : ℝ)⁻¹ := by norm_num
  rw [h8] at hc
  linarith

/-- **At `τ = m/w` an odd reading `w` blocks at most one of the eight shifts.** -/
theorem odd_blocked_le_one_at_grid {w : ℕ} (hw : ¬ 2 ∣ w) (m : ℕ) :
    ((Finset.range 8).filter (fun k => Blocked ((m : ℝ) / w) w k)).card ≤ 1 := by
  have hw0 : 0 < w := by omega
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_range] at ha hb
  have h1 : (8 : ℤ) ∣ ((m + w * a : ℕ) : ℤ) := by
    exact_mod_cast eight_dvd_of_blocked_at_grid hw0 m a ha.2
  have h2 : (8 : ℤ) ∣ ((m + w * b : ℕ) : ℤ) := by
    exact_mod_cast eight_dvd_of_blocked_at_grid hw0 m b hb.2
  have hd : (8 : ℤ) ∣ (w : ℤ) * ((a : ℤ) - b) := by
    have := dvd_sub h1 h2
    convert this using 1
    push_cast; ring
  have hw' : ¬ (2 : ℤ) ∣ (w : ℤ) := by exact_mod_cast hw
  have := (isCoprime_eight_of_odd hw').dvd_of_dvd_mul_left hd
  omega

/-- **A reading not divisible by `4` blocks at most two of the eight shifts** (`card_bad_le`,
with `gcd e 8 ≤ 2`). -/
theorem card_blocked_le_two_of_not_four (τ : ℝ) {e : ℕ} (he : ¬ 4 ∣ e) :
    ((Finset.range 8).filter (fun k => Blocked τ e k)).card ≤ 2 := by
  classical
  have h := card_bad_le (n := 8) (by norm_num) ((e : ℝ) * τ / 8) e
  have hg : Nat.gcd e 8 ≤ 2 := by
    have h1 : Nat.gcd e 8 = Nat.gcd (e % 8) 8 := by
      rw [Nat.gcd_comm, Nat.gcd_rec]
    have h2 : e % 8 < 8 := Nat.mod_lt _ (by norm_num)
    have h3 : e % 8 ≠ 0 := by omega
    have h4 : e % 8 ≠ 4 := by omega
    rw [h1]
    generalize e % 8 = r at h2 h3 h4
    interval_cases r <;> simp_all
  have hm : max 2 (Nat.gcd e 8) = 2 := max_eq_left hg
  rw [hm] at h
  convert h using 3

end LRC.ParityDescent

namespace LRC.OrderEightN

open ConstructionN LRC.Descent LRC.ParityDescent

/-- **The eighth level at one offset.**  If `τ > 0` clears the cofactors of the multiples of `8` at
`1/8` and the shift `k` is free for every non-multiple at `τ`, the set is lonely at `(τ + k)/8`. -/
theorem lonely_eight_of_free_at {S : Finset ℕ} {τ : ℝ} (hτ : 0 < τ) {k : ℕ}
    (hM : ∀ d ∈ S, 8 ∣ d → (8 : ℝ)⁻¹ ≤ circDist (((d / 8 : ℕ) : ℝ) * τ))
    (hk : ∀ e ∈ S, ¬ 8 ∣ e → ¬ Blocked τ e k) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  refine ⟨(τ + k) / 8, by positivity, fun d hd => ?_⟩
  by_cases h8 : 8 ∣ d
  · obtain ⟨c, rfl⟩ := h8
    have hc := hM (8 * c) hd (dvd_mul_right 8 c)
    rw [show 8 * c / 8 = c by omega] at hc
    have heq : ((8 * c : ℕ) : ℝ) * ((τ + k) / 8) = (c : ℝ) * τ + (((c * k : ℕ) : ℤ) : ℝ) := by
      push_cast; ring
    rw [heq, circDist_add_int]; exact hc
  · have hb := hk d hd h8
    unfold Blocked at hb
    push Not at hb
    have heq : (d : ℝ) * ((τ + k) / 8) = (d : ℝ) * τ / 8 + (d : ℝ) * (k : ℝ) / 8 := by ring
    rw [heq]; exact hb

/-- **The reduction-point corollary.**  At most three multiples of `8`, at most four non-multiples,
none divisible by `4`, one of them an odd `w` dividing no cofactor `m/8` of a multiple: the set is
lonely at `1/8`.  The offset is `τ = (m + w)/w` for the grid point `m` of `grid_point`.  No
positivity hypothesis is needed: `hnd` already rules out `0 ∈ S` (its cofactor `0` is divisible by
`w`). -/
theorem lonely_eight_of_grid {S : Finset ℕ}
    (hM : (S.filter (fun d => 8 ∣ d)).card ≤ 3)
    (hN : (S.filter (fun d => ¬ 8 ∣ d)).card ≤ 4)
    (hty : ∀ d ∈ S, ¬ 8 ∣ d → ¬ 4 ∣ d)
    {w : ℕ} (hwS : w ∈ S) (hw : ¬ 2 ∣ w) (hnd : ∀ m ∈ S, 8 ∣ m → ¬ w ∣ m / 8) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  classical
  have hw0 : 0 < w := by omega
  set C := (S.filter (fun d => 8 ∣ d)).image (fun d => d / 8) with hCdef
  have hC : C.card ≤ 3 := le_trans Finset.card_image_le hM
  have hCnd : ∀ c ∈ C, ¬ w ∣ c := by
    intro c hc
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
    obtain ⟨hdS, hd8⟩ := Finset.mem_filter.mp hd
    exact hnd d hdS hd8
  obtain ⟨m, -, hm⟩ := grid_point hw C hC hCnd
  set τ : ℝ := ((m + w : ℕ) : ℝ) / w with hτdef
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw0
  have hτ : 0 < τ := div_pos (by exact_mod_cast (by omega : 0 < m + w)) hw'
  -- the cofactors are clear at `τ`, a whole number of laps from `m/w`
  have hMτ : ∀ d ∈ S, 8 ∣ d → (8 : ℝ)⁻¹ ≤ circDist (((d / 8 : ℕ) : ℝ) * τ) := by
    intro d hd h8
    have hc := hm (d / 8) (Finset.mem_image.mpr ⟨d, Finset.mem_filter.mpr ⟨hd, h8⟩, rfl⟩)
    generalize d / 8 = c at hc ⊢
    have heq : (c : ℝ) * τ = (c : ℝ) * m / w + ((c : ℤ) : ℝ) := by
      rw [hτdef]; push_cast; field_simp
    rw [heq, circDist_add_int]; exact hc
  -- at most seven of the eight shifts are blocked
  set E := S.filter (fun d => ¬ 8 ∣ d) with hEdef
  have hwE : w ∈ E := Finset.mem_filter.mpr ⟨hwS, by omega⟩
  set Bad : ℕ → Finset ℕ := fun e => (Finset.range 8).filter (fun k => Blocked τ e k) with hBad
  have hBw : (Bad w).card ≤ 1 := odd_blocked_le_one_at_grid hw (m + w)
  have hB2 : ∀ e ∈ E.erase w, (Bad e).card ≤ 2 := by
    intro e he
    obtain ⟨-, heE⟩ := Finset.mem_erase.mp he
    obtain ⟨heS, he8⟩ := Finset.mem_filter.mp heE
    exact card_blocked_le_two_of_not_four τ (hty e heS he8)
  have hEc : (E.erase w).card ≤ 3 := by rw [Finset.card_erase_of_mem hwE]; omega
  have hU : (E.biUnion Bad).card < (Finset.range 8).card := by
    rw [Finset.card_range]
    calc (E.biUnion Bad).card ≤ ∑ e ∈ E, (Bad e).card := Finset.card_biUnion_le
      _ = (Bad w).card + ∑ e ∈ E.erase w, (Bad e).card := (Finset.add_sum_erase E _ hwE).symm
      _ ≤ 1 + ∑ _e ∈ E.erase w, 2 := Nat.add_le_add hBw (Finset.sum_le_sum hB2)
      _ = 1 + (E.erase w).card * 2 := by rw [Finset.sum_const, smul_eq_mul]
      _ < 8 := by omega
  obtain ⟨k, hk, hkU⟩ := Finset.exists_mem_notMem_of_card_lt_card hU
  refine lonely_eight_of_free_at (k := k) hτ hMτ fun e he h8 hb => hkU ?_
  exact Finset.mem_biUnion.mpr ⟨e, Finset.mem_filter.mpr ⟨he, h8⟩, Finset.mem_filter.mpr ⟨hk, hb⟩⟩

end LRC.OrderEightN
