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

/-! ## §7c / L1 — the dead steps are a divisor-closed set

A step `D` is **dead** for a difference `d` when `n·D ∣ d`, since then no multiplier can move
that runner off the lap line.  Two facts make the dead set computable: the divisibility factors
through `n`, so only the differences divisible by `n` can contribute; and the dead set is closed
downwards under division, so it is exactly the set of divisors of `{ d/n : n ∣ d }`.
-/

/-- `n·D ∣ d` iff `d` is `n` times something that `D` divides.  So only the differences
divisible by `n` can make a step dead, and what they contribute is the divisors of `d/n`. -/
theorem dead_iff {n D d : ℕ} : n * D ∣ d ↔ ∃ k, d = n * k ∧ D ∣ k := by
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨D * m, by ring, ⟨m, rfl⟩⟩
  · rintro ⟨k, rfl, m, rfl⟩
    exact ⟨m, by ring⟩

/-- The dead steps are closed downwards under divisibility: a divisor of a dead step is dead. -/
theorem dead_downward {n D D' d : ℕ} (hdvd : D' ∣ D) (h : n * D ∣ d) : n * D' ∣ d :=
  dvd_trans (mul_dvd_mul_left n hdvd) h

/-- A live step always exists: the dead set is bounded by the largest difference, so any step
past it is live.  This is what makes `L₀`, the least live step, well defined. -/
theorem exists_live {n : ℕ} (hn : 0 < n) (ds : Finset ℕ) (hpos : ∀ d ∈ ds, 0 < d) :
    ∃ D, 0 < D ∧ ∀ d ∈ ds, ¬ (n * D ∣ d) := by
  classical
  set B := ds.sup id with hBdef
  refine ⟨B + 1, Nat.succ_pos B, ?_⟩
  intro d hd hdvd
  have hdB : d ≤ B := Finset.le_sup (f := id) hd
  have hd0 : 0 < d := hpos d hd
  have h1 : n * (B + 1) ≤ d := Nat.le_of_dvd hd0 hdvd
  have h2 : B + 1 ≤ n * (B + 1) := Nat.le_mul_of_pos_left _ hn
  omega

/-! ## L3 — the reading is complete

`docs/n8/LEMMA_L3_v1.md` proves completeness by closedness and compactness.  The same fact has
an elementary proof, which is what is formalised here: if a runner stands clear of `d` at `t`,
then it stands clear of `d` everywhere between `t` and the **opening** of the stretch `t` sits
in.  Taking the largest such opening over all the differences produces an opening that is
itself an isolation instant and no later than `t` — which is completeness, with no topology.
-/

/-- The opening of the clear stretch that `t` lies in, for the difference `d`. -/
noncomputable def opening (n : ℕ) (d t : ℝ) : ℝ := ((⌊d * t⌋ : ℝ) + (n : ℝ)⁻¹) / d

/-- **Clear back to the opening.**  If the runner at difference `d` stands clear at `t`, it
stands clear at every `s` between that stretch's opening and `t`. -/
theorem clear_on_left {n : ℕ} (hn : 0 < n) {d t s : ℝ} (hd : 0 < d)
    (ht : (n : ℝ)⁻¹ ≤ circDist (d * t))
    (hs1 : opening n d t ≤ s) (hs2 : s ≤ t) :
    (n : ℝ)⁻¹ ≤ circDist (d * s) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hni : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.mpr hn'
  have hn1 : (n : ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]; right; exact_mod_cast hn
  set q : ℤ := ⌊d * t⌋ with hq
  have hfr : Int.fract (d * t) = d * t - q := (Int.self_sub_floor (d * t)).symm
  -- the threshold at t, read on the fractional part
  have hlow : (n : ℝ)⁻¹ ≤ Int.fract (d * t) := le_trans (le_min_iff.mp ht).1 (le_refl _)
  have hhigh : Int.fract (d * t) ≤ 1 - (n : ℝ)⁻¹ := by
    have := (le_min_iff.mp ht).2
    linarith
  -- d*s is caught between q + 1/n and d*t
  have hds1 : (q : ℝ) + (n : ℝ)⁻¹ ≤ d * s := by
    have : ((q : ℝ) + (n : ℝ)⁻¹) / d * d ≤ s * d := by
      exact mul_le_mul_of_nonneg_right hs1 (le_of_lt hd)
    rw [div_mul_cancel₀ _ (ne_of_gt hd)] at this
    linarith [this, mul_comm d s]
  have hds2 : d * s ≤ d * t := mul_le_mul_of_nonneg_left hs2 (le_of_lt hd)
  -- so its floor is q, and its fractional part sits in the band
  have hfloor : ⌊d * s⌋ = q := by
    rw [Int.floor_eq_iff]
    constructor
    · linarith
    · push_cast; linarith [hfr, hhigh]
  have hfr2 : Int.fract (d * s) = d * s - q := by
    rw [← Int.self_sub_floor, hfloor]
  unfold circDist
  rw [hfr2]
  apply le_min
  · linarith
  · linarith [hfr, hhigh]

/-- The opening of the stretch containing `t` is no later than `t`. -/
theorem opening_le {n : ℕ} (hn : 0 < n) {d t : ℝ} (hd : 0 < d)
    (ht : (n : ℝ)⁻¹ ≤ circDist (d * t)) : opening n d t ≤ t := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlow : (n : ℝ)⁻¹ ≤ Int.fract (d * t) := (le_min_iff.mp ht).1
  have hfr : Int.fract (d * t) = d * t - (⌊d * t⌋ : ℝ) := (Int.self_sub_floor (d * t)).symm
  unfold opening
  rw [div_le_iff₀ hd]
  linarith [hfr, hlow]

/-- **L3, completeness.**  If a runner is isolated at `t`, it is isolated at some *opening* no
later than `t` — namely the largest of the openings of the stretches its differences put `t` in.
So the reading, which enumerates only openings, cannot miss the first isolation instant. -/
theorem reading_complete {n : ℕ} (hn : 0 < n) (ds : Finset ℝ) (hne : ds.Nonempty)
    (hpos : ∀ d ∈ ds, 0 < d) {t : ℝ} (ht : ∀ d ∈ ds, (n : ℝ)⁻¹ ≤ circDist (d * t)) :
    ∃ e ∈ ds, opening n e t ≤ t ∧ ∀ d ∈ ds, (n : ℝ)⁻¹ ≤ circDist (d * (opening n e t)) := by
  classical
  obtain ⟨e, he, hmax⟩ := ds.exists_max_image (fun d => opening n d t) hne
  refine ⟨e, he, opening_le hn (hpos e he) (ht e he), ?_⟩
  intro d hd
  exact clear_on_left hn (hpos d hd) (ht d hd) (hmax d hd)
    (opening_le hn (hpos e he) (ht e he))

/-! ## The spine arithmetic

One lemma carries §4's `φ(n)` instants, §7's bijection and §7a's endpoints: an integer numerator
over `n` clears the threshold exactly when `n` does not divide it.  Everything the reference does
is this fact plus the fact that `k ↦ kr` permutes the residues when `gcd(r,n) = 1`.
-/

/-- **The spine test.**  For an integer `c`, the point `c/n` clears the threshold `1/n` iff `n`
does not divide `c`.  This is the whole of "a runner is on a lap line at a reference instant". -/
theorem circDist_int_div {n : ℕ} (hn : 0 < n) {c : ℤ} (h : ¬ ((n : ℤ) ∣ c)) :
    (n : ℝ)⁻¹ ≤ circDist ((c : ℝ) / n) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hnz : (n : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hn.ne'
  set r : ℤ := c % n with hr
  have hr0 : 0 ≤ r := Int.emod_nonneg c hnz
  have hrn : r < n := Int.emod_lt_of_pos c (by exact_mod_cast hn)
  have hrne : r ≠ 0 := fun hz => h (Int.dvd_of_emod_eq_zero hz)
  have hr1 : 1 ≤ r := by omega
  have hrn1 : r ≤ (n : ℤ) - 1 := by omega
  have hid : (n : ℤ) * (c / (n : ℤ)) + r = c := Int.mul_ediv_add_emod c n
  have hidR : (n : ℝ) * ((c / (n : ℤ) : ℤ) : ℝ) + (r : ℝ) = (c : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hid
  have hsplit : (c : ℝ) / n = ((c / (n : ℤ) : ℤ) : ℝ) + (r : ℝ) / n := by
    field_simp
    linarith [hidR]
  have hrr0 : (0 : ℝ) ≤ (r : ℝ) / n := by positivity
  have hrr1 : (r : ℝ) / n < 1 := by
    rw [div_lt_one hn']; exact_mod_cast hrn
  have hfr : Int.fract ((c : ℝ) / n) = (r : ℝ) / n := by
    rw [hsplit, Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨hrr0, hrr1⟩]
  have hR1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hR2 : (r : ℝ) ≤ (n : ℝ) - 1 := by exact_mod_cast hrn1
  unfold circDist
  rw [hfr]
  apply le_min
  · rw [inv_eq_one_div]
    gcongr
  · have hsum : (n : ℝ)⁻¹ + (r : ℝ) / n = (1 + (r : ℝ)) / n := by field_simp
    rw [le_sub_iff_add_le, hsum, div_le_one hn']
    linarith

end Construction8
