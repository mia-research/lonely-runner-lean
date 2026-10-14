import LonelyRunner.LRC.Spec.OrderEightCasesN
import LonelyRunner.LRC.Spec.DescentMultiN

set_option linter.style.longLine false

/-!
# The descent by a general modulus `q` at threshold `1/8`

2026-10-06.  The isolation is taken at the `q` instants `σ + k/q` (`k = 0, …, q − 1`), displaced
by `σ`.  At those instants every reading divisible by `q` returns to the same place: `d = q·m`
reads `m·q·σ + m·k`, unchanged mod 1.  A reading `e` not divisible by `q` reads `e·σ + e·k/q`, and
visits a coset of `(g/q)ℤ`, `g = gcd(e, q)`.  The displacement `σ = ρ/q` is chosen so that the
readings divisible by `q` are clear; the `q` instants then leave one at which no other reading is
in the subject's slot.

**The blocked-shift bound** (`card_blocked_mod_le`).  A reading `e` is in the subject's slot at
no more than `g·⌈q/(4g)⌉` of the `q` shifts.  Write `e = g·c`, `q = g·p`, `c` coprime to `p`.  The
shift `k` puts `e` where `x + (c·k mod p)/p` stands (`circDist_shift_eq_mod`), so the map
`k ↦ (k / p, c·k mod p)` is injective on the blocked shifts and lands in `range g × A`, `A` the
points `r < p` of the grid `x + r/p` inside the open arc `(−1/8, 1/8)` around the integers.  Those
points are `p`-spaced integers `N_r = r − p·K_r` in an open interval of length `p/4`, so
`#A ≤ ⌈p/4⌉ = (p + 3)/4` (`card_grid_near_le`), and `⌈p/4⌉ ≤ ⌈q/(4g)⌉` (`ceil_quarter_le`).
[PROVISIONAL: counting tool; supports: the blocked-shift bound]

**The descent by `q`** (`lonely_eight_of_descent_mod`).  The quotients `m = d/q` of the readings
divisible by `q` are at most six, positive and distinct; `lonely_eight_of_card_le_six` gives
`ρ > 0` with every `‖m·ρ‖ ≥ 1/8` (and covers the empty case).  At `t_k = (ρ + k)/q = σ + k/q` the
multiples are clear, and if the blocked-shift bounds of the non-multiples sum to less than `q`,
some shift `k < q` is free of every non-multiple.
[PROVISIONAL: counting tool; supports: the free shift]

**Lower-order input.**  `lonely_eight_of_card_le_six` rests on order seven,
`LRC.OrderSevenN.lonely_seven_nat`: every set of at most six positive whole-number disparities is
lonely at `1/7 ≥ 1/8`.  The owner's ruling on such lower-order inputs (compilation ground rule 4)
is owed; it is used here as the input that clears the quotients.

Everything here is proved; no `sorry`, no `native_decide`.
-/

namespace LRC.Descent

open ConstructionN

/-! ## The grid `x + r/p` against the open arc of length `1/4` -/

/-- **Two grid points near the lap line differ by less than a quarter lap.**  If `x + a/p` and
`x + b/p` are each within `1/8` of `0`, then `4·(a − b) < p`. -/
theorem four_mul_sub_lt_of_near {p : ℕ} (hp : 0 < p) (x : ℝ) {a b : ℤ}
    (ha : |x + (a : ℝ) / p| < (8 : ℝ)⁻¹) (hb : |x + (b : ℝ) / p| < (8 : ℝ)⁻¹) :
    4 * (a - b) < (p : ℤ) := by
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp
  have hpn : (p : ℝ) ≠ 0 := hppos.ne'
  have e : ((4 * (a - b) : ℤ) : ℝ) = 4 * p * ((x + (a : ℝ) / p) - (x + (b : ℝ) / p)) := by
    push_cast; field_simp; ring
  have hreal : ((4 * (a - b) : ℤ) : ℝ) < ((p : ℤ) : ℝ) := by
    rw [e]
    rw [abs_lt] at ha hb
    push_cast
    nlinarith
  exact_mod_cast hreal

/-- **At most `⌈p/4⌉` points of the grid `x + r/p` lie within `1/8` of the integers.** -/
theorem card_grid_near_le (p : ℕ) (hp : 0 < p) (x : ℝ) :
    ((Finset.range p).filter (fun r : ℕ => circDist (x + (r : ℝ) / p) < (8 : ℝ)⁻¹)).card
      ≤ (p + 3) / 4 := by
  classical
  set B := (Finset.range p).filter
    (fun r : ℕ => circDist (x + (r : ℝ) / p) < (8 : ℝ)⁻¹) with hB
  have hK : ∀ r : ℕ, ∃ K : ℤ, circDist (x + (r : ℝ) / p) = |x + (r : ℝ) / p - K| :=
    fun r => circDist_eq_abs_sub_some_int _
  choose K hK using hK
  set N : ℕ → ℤ := fun r => (r : ℤ) - p * K r with hN
  have hppos : (0 : ℝ) < p := by exact_mod_cast hp
  have hpn : (p : ℝ) ≠ 0 := hppos.ne'
  have hlt : ∀ r ∈ B, r < p := fun r hr => Finset.mem_range.mp (Finset.mem_filter.mp hr).1
  have hnear : ∀ r ∈ B, |x + (N r : ℝ) / p| < (8 : ℝ)⁻¹ := by
    intro r hr
    have h := (Finset.mem_filter.mp hr).2
    rw [hK r] at h
    have heq : x + (N r : ℝ) / p = x + (r : ℝ) / p - K r := by
      simp only [hN]; push_cast; field_simp; ring
    rw [heq]; exact h
  have hinj : Set.InjOn N (B : Set ℕ) := by
    intro a ha b hb hab
    have ha' : (a : ℤ) < p := by exact_mod_cast hlt a ha
    have hb' : (b : ℤ) < p := by exact_mod_cast hlt b hb
    simp only [hN] at hab
    have hd : (a : ℤ) - b = p * (K a - K b) := by linarith
    have hc0 : K a - K b = 0 := by
      rcases lt_trichotomy (K a - K b) 0 with h | h | h
      · nlinarith
      · exact h
      · nlinarith
    rw [hc0, mul_zero] at hd
    omega
  rcases B.eq_empty_or_nonempty with hBe | hne
  · rw [hBe, Finset.card_empty]; exact Nat.zero_le _
  obtain ⟨r₀, hr₀, hmin⟩ := Finset.exists_min_image B N hne
  have hmaps : Set.MapsTo N (B : Set ℕ)
      (Finset.Ico (N r₀) (N r₀ + (((p - 1) / 4 + 1 : ℕ) : ℤ)) : Set ℤ) := by
    intro r hr
    have h1 := hmin r hr
    have h2 := four_mul_sub_lt_of_near hp x (hnear r hr) (hnear r₀ hr₀)
    simp only [Finset.coe_Ico, Set.mem_Ico]
    omega
  have hc := Finset.card_le_card_of_injOn N hmaps hinj
  rw [Int.card_Ico] at hc
  omega

/-! ## A reading `e` at the `q` shifts -/

/-- **The shift `k` puts `e` where the grid point `(c·k mod p)/p` stands**, `e = g·c`, `q = g·p`. -/
theorem circDist_shift_eq_mod {q g p c : ℕ} (hg : 0 < g) (hp : 0 < p) (hq : q = g * p) (x : ℝ)
    (k : ℕ) :
    circDist (x + ((g * c : ℕ) : ℝ) * (k : ℝ) / q) = circDist (x + ((c * k % p : ℕ) : ℝ) / p) := by
  have hgr : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
  have hpr : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have h1 : ((g * c : ℕ) : ℝ) * (k : ℝ) / q = ((c * k : ℕ) : ℝ) / p := by
    rw [hq]; push_cast; field_simp
  have h2 : ((c * k : ℕ) : ℝ) = (p : ℝ) * ((c * k / p : ℕ) : ℝ) + ((c * k % p : ℕ) : ℝ) := by
    exact_mod_cast (Nat.div_add_mod (c * k) p).symm
  have h3 : x + ((c * k : ℕ) : ℝ) / p
      = x + ((c * k % p : ℕ) : ℝ) / p + (((c * k / p : ℕ) : ℤ) : ℝ) := by
    rw [h2, Int.cast_natCast]
    generalize ((c * k / p : ℕ) : ℝ) = u
    generalize ((c * k % p : ℕ) : ℝ) = v
    field_simp; ring
  rw [h1, h3, circDist_add_int]

/-- `⌈p/4⌉ ≤ ⌈q/(4g)⌉` when `q = g·p`.  Only `≤` is proved; it is what the bound needs. -/
theorem ceil_quarter_le {q g p : ℕ} (hg : 0 < g) (hq : q = g * p) :
    (p + 3) / 4 ≤ (q + 4 * g - 1) / (4 * g) := by
  rw [Nat.le_div_iff_mul_le (by omega)]
  have h4 : 4 * ((p + 3) / 4) ≤ p + 3 := Nat.mul_div_le (p + 3) 4
  have h5 : (p + 3) / 4 * (4 * g) ≤ (p + 3) * g := by
    calc (p + 3) / 4 * (4 * g) = (4 * ((p + 3) / 4)) * g := by ring
      _ ≤ (p + 3) * g := Nat.mul_le_mul_right g h4
  have h6 : (p + 3) * g = q + 3 * g := by rw [hq]; ring
  omega

/-- **A reading `e` blocks at most `g·⌈q/(4g)⌉` of the `q` shifts, `g = gcd e q`, at threshold
`1/8`.**  [PROVISIONAL: counting tool; supports: the blocked-shift bound] -/
theorem card_blocked_mod_le (q : ℕ) (hq : 0 < q) (x : ℝ) (e : ℕ) :
    ((Finset.range q).filter (fun k : ℕ => circDist (x + (e : ℝ) * (k : ℝ) / q) < (8 : ℝ)⁻¹)).card
      ≤ Nat.gcd e q * ((q + 4 * Nat.gcd e q - 1) / (4 * Nat.gcd e q)) := by
  classical
  set B := (Finset.range q).filter
    (fun k : ℕ => circDist (x + (e : ℝ) * (k : ℝ) / q) < (8 : ℝ)⁻¹) with hB
  set g := Nat.gcd e q with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right e hq
  set p := q / g with hp
  set c := e / g with hc
  have hqp : q = g * p := (Nat.mul_div_cancel' (Nat.gcd_dvd_right e q)).symm
  have hec : e = g * c := (Nat.mul_div_cancel' (Nat.gcd_dvd_left e q)).symm
  have hcop : Nat.Coprime c p := Nat.coprime_div_gcd_div_gcd hg0
  clear_value c p
  have hp0 : 0 < p := by
    rcases Nat.eq_zero_or_pos p with h | h
    · rw [h, mul_zero] at hqp; omega
    · exact h
  set A := (Finset.range p).filter
    (fun r : ℕ => circDist (x + (r : ℝ) / p) < (8 : ℝ)⁻¹) with hA
  have hread : ∀ k : ℕ, circDist (x + (e : ℝ) * (k : ℝ) / q)
      = circDist (x + ((c * k % p : ℕ) : ℝ) / p) := by
    intro k
    have h := circDist_shift_eq_mod (c := c) hg0 hp0 hqp x k
    rw [← hec] at h
    exact h
  have hmaps : Set.MapsTo (fun k => (k / p, c * k % p)) (B : Set ℕ)
      (Finset.range g ×ˢ A : Finset (ℕ × ℕ)) := by
    intro k hk
    simp only [hB, Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hk
    obtain ⟨hkq, hblk⟩ := hk
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range, hA,
      Finset.mem_filter]
    refine ⟨Nat.div_lt_of_lt_mul (by rw [mul_comm, ← hqp]; exact hkq),
      Nat.mod_lt _ hp0, ?_⟩
    rw [← hread k]; exact hblk
  have hinj : Set.InjOn (fun k => (k / p, c * k % p)) (B : Set ℕ) := by
    intro a _ b _ hab
    simp only [Prod.mk.injEq] at hab
    obtain ⟨h1, h2⟩ := hab
    have hmod : a ≡ b [MOD p] := Nat.ModEq.cancel_left_of_coprime (Nat.coprime_comm.mp hcop) h2
    rw [← Nat.div_add_mod a p, ← Nat.div_add_mod b p, h1, hmod]
  have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
  rw [Finset.card_product, Finset.card_range] at hcard
  calc B.card ≤ g * A.card := hcard
    _ ≤ g * ((p + 3) / 4) := Nat.mul_le_mul_left g (card_grid_near_le p hp0 x)
    _ ≤ g * ((q + 4 * g - 1) / (4 * g)) := Nat.mul_le_mul_left g (ceil_quarter_le hg0 hqp)

end LRC.Descent

namespace LRC.OrderEightN

open ConstructionN LRC.Descent

/-- **The quotients of the readings divisible by `q`** are positive. -/
theorem quotient_pos {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d) {q : ℕ} (hq : 0 < q) :
    ∀ m ∈ (S.filter (fun d => q ∣ d)).image (fun d => d / q), 0 < m := by
  intro m hm
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hm
  obtain ⟨hdS, hdq⟩ := Finset.mem_filter.mp hd
  exact Nat.div_pos (Nat.le_of_dvd (hpos d hdS) hdq) hq

/-- **The descent by `q` at threshold `1/8`.**  If at most six readings are divisible by `q` and
the blocked-shift bounds `g·⌈q/(4g)⌉` of the others sum to less than `q`, the set is lonely at
`1/8`, at an instant `σ + k/q` with `σ = ρ/q`, `ρ` clearing the quotients.  The quotients are
cleared by order seven (`lonely_eight_of_card_le_six`, resting on `LRC.OrderSevenN.lonely_seven_nat`).
[PROVISIONAL: counting tool; supports: the free shift] -/
theorem lonely_eight_of_descent_mod {S : Finset ℕ} (hpos : ∀ d ∈ S, 0 < d) (q : ℕ) (hq : 0 < q)
    (hM : (S.filter (fun d => q ∣ d)).card ≤ 6)
    (hbudget : ∑ e ∈ S.filter (fun d => ¬ q ∣ d),
        Nat.gcd e q * ((q + 4 * Nat.gcd e q - 1) / (4 * Nat.gcd e q)) < q) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  classical
  set M := (S.filter (fun d => q ∣ d)).image (fun d => d / q) with hMdef
  have hMc : M.card ≤ 6 := le_trans Finset.card_image_le hM
  obtain ⟨ρ, hρ, hρM⟩ := lonely_eight_of_card_le_six (quotient_pos hpos hq) hMc
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hqn : (q : ℝ) ≠ 0 := hqpos.ne'
  set E := S.filter (fun d => ¬ q ∣ d) with hEdef
  set Bad : ℕ → Finset ℕ := fun e => (Finset.range q).filter
    (fun k : ℕ => circDist ((e : ℝ) * ρ / q + (e : ℝ) * (k : ℝ) / q) < (8 : ℝ)⁻¹) with hBad
  have hcard : (E.biUnion Bad).card < (Finset.range q).card := by
    rw [Finset.card_range]
    calc (E.biUnion Bad).card ≤ ∑ e ∈ E, (Bad e).card := Finset.card_biUnion_le
      _ ≤ ∑ e ∈ E, Nat.gcd e q * ((q + 4 * Nat.gcd e q - 1) / (4 * Nat.gcd e q)) :=
          Finset.sum_le_sum fun e _ => card_blocked_mod_le q hq ((e : ℝ) * ρ / q) e
      _ < q := hbudget
  obtain ⟨k, hk, hkn⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  refine ⟨(ρ + k) / q, by positivity, fun d hd => ?_⟩
  by_cases hdq : q ∣ d
  · obtain ⟨m, rfl⟩ := hdq
    have hm : m ∈ M := Finset.mem_image.mpr
      ⟨q * m, Finset.mem_filter.mpr ⟨hd, dvd_mul_right q m⟩, Nat.mul_div_cancel_left m hq⟩
    have heq : ((q * m : ℕ) : ℝ) * ((ρ + k) / q) = (m : ℝ) * ρ + (((m * k : ℕ) : ℤ) : ℝ) := by
      push_cast; field_simp
    rw [heq, circDist_add_int]
    exact hρM m hm
  · have hdE : d ∈ E := Finset.mem_filter.mpr ⟨hd, hdq⟩
    have hnot : k ∉ Bad d := fun h => hkn (Finset.mem_biUnion.mpr ⟨d, hdE, h⟩)
    have hclear : ¬ circDist ((d : ℝ) * ρ / q + (d : ℝ) * (k : ℝ) / q) < (8 : ℝ)⁻¹ :=
      fun h => hnot (Finset.mem_filter.mpr ⟨hk, h⟩)
    have heq : (d : ℝ) * ((ρ + k) / q) = (d : ℝ) * ρ / q + (d : ℝ) * (k : ℝ) / q := by ring
    rw [heq]
    exact not_lt.mp hclear

end LRC.OrderEightN
