import LonelyRunner.LRC.Spec.FlankFiniteN

/-!
# Lonely instants that are not indexed by the arrangement

2026-09-21.  Every criterion in `FlankFiniteN`, `ResonanceN`, `WindowN`, `SelfSimilarN` and
`OtherFlankN` searches **flank openings** `(j + 1/n)/e` — instants whose denominator is `n·e`, a
disparity of the very set being tested.  That choice was never examined.  It looked forced, because
`Flanks.lonely_iff_exists_flank` is an `iff`: a flank opening always works, so why look elsewhere.

**Because "the flank family is complete" is not "the flank family is where a proof lives."**  For
*existence* the flank family is without loss of generality.  For *certification* it is the worst
place to look, since the index `j` has no formula in the disparities — which is exactly why six
criteria built on it converged to a residue of fixed density instead of to zero.

A lonely instant at a **small-denominator rational** `a/q` is certified by a divisibility condition
on the disparities and no search at all:

    t = 1/2   every disparity odd
    t = 1/3   no disparity divisible by 3
    t = 1/4   no disparity divisible by 4
    t = 1/5   no disparity divisible by 5        (at order five)

Evidence that this is the right frame: of the twelve sets in `[1,40]` that survived **all six**
flank criteria, **eleven** fall to a rational of denominator at most 9
(`experiments/nN/small_denominator_v1.out`).  `(1,10,21,22)` — which survived P1′ through P7 — is
lonely at `t = 1/4`, because none of `1, 10, 21, 22` is divisible by 4.

**What is not claimed.**  That the denominator is bounded.  A range sweep gives a maximum of 19,
stable from `[1,30]` to `[1,50]` while the population grows 47-fold — but the condition at `q`
depends only on `d mod q`, so range stability is weak evidence, and an adversarial search over
tuples built divisible by many different small moduli reaches **35**
(`experiments/nN/small_denominator_adversarial_v1.out`).  The hard tuples are a CRT spread: each
disparity divisible by a *different* set of small primes.  No bound is proved or conjectured here.

Firewall note: `t = a/q ≤ 1` is a property of the witness exhibited, not a requirement placed on
anything, so §6A row two is not engaged — the same footing as `R < n − 1`.  Contrast `DoorFirstLap`,
which *asserted* a cap and is `[REFUTED]`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace LRC.RationalN

open Flanks MomentIterationN LRC.SpecN LRC.FlankFinite

variable {n : ℕ} [Fact (2 ≤ n)]

/-! ## 1. the criterion -/

/-- `t = a/q` clears the whole-number difference set at threshold `1/n` when every reading
`d·a mod q` lies in the band `[q/n, (n−1)q/n]`. -/
def ratWorks (n : ℕ) (ds : List ℕ) (a q : ℕ) : Bool :=
  ds.all fun d =>
    let r := (d * a) % q
    decide (q ≤ n * r) && decide (n * r ≤ (n - 1) * q)

/-- **The position at a rational instant is its residue.** -/
theorem circDist_rat (d a q : ℕ) (hq : 0 < q) :
    circDist ((d : ℝ) * ((a : ℝ) / (q : ℝ))) = circDist ((((d * a) % q : ℕ) : ℝ) / (q : ℝ)) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hsplit : (d : ℝ) * ((a : ℝ) / (q : ℝ))
      = ((((d * a) % q : ℕ) : ℝ) / (q : ℝ)) + (((d * a / q : ℕ) : ℤ) : ℝ) := by
    have hnat : ((q * (d * a / q) + (d * a) % q : ℕ) : ℝ) = ((d * a : ℕ) : ℝ) := by
      rw [Nat.div_add_mod]
    have hcast : (((d * a / q : ℕ) : ℤ) : ℝ) = ((d * a / q : ℕ) : ℝ) := by norm_cast
    rw [hcast]
    push_cast at hnat
    field_simp
    linarith
  rw [hsplit, ConstructionN.circDist_add_int]

/-- **The bridge.**  A band reading at `a/q` is a genuine clearance over the reals. -/
theorem lonely_of_ratWorks (L : List ℕ) (a q : ℕ) (hq : 0 < q)
    (h : ratWorks n L a q = true) :
    ∀ d ∈ L, (n : ℝ)⁻¹ ≤ circDist ((d : ℝ) * ((a : ℝ) / (q : ℝ))) := by
  have hn2 : 2 ≤ n := Fact.out
  have hn0 : (0 : ℝ) < (n : ℝ) := n_pos
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  intro d hd
  unfold ratWorks at h
  rw [List.all_eq_true] at h
  have hdj := h d hd
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hdj
  obtain ⟨h1, h2⟩ := hdj
  set r : ℕ := (d * a) % q with hr
  have hrq : r < q := Nat.mod_lt _ hq
  have hr1 : (q : ℝ) ≤ (n : ℝ) * (r : ℝ) := by exact_mod_cast h1
  have hr2 : (n : ℝ) * (r : ℝ) ≤ ((n : ℝ) - 1) * (q : ℝ) := by
    have : ((n * r : ℕ) : ℝ) ≤ (((n - 1) * q : ℕ) : ℝ) := by exact_mod_cast h2
    have hc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      have : 1 ≤ n := by omega
      push_cast [Nat.cast_sub this]; ring
    rw [Nat.cast_mul, Nat.cast_mul, hc] at this; exact this
  rw [circDist_rat d a q hq, ← hr]
  have hfr : Int.fract ((r : ℝ) / (q : ℝ)) = (r : ℝ) / (q : ℝ) := by
    refine Int.fract_eq_self.mpr ⟨by positivity, ?_⟩
    rw [div_lt_one hq0]; exact_mod_cast hrq
  rw [circDist, hfr, le_min_iff]
  constructor
  · rw [inv_eq_one_div, div_le_div_iff₀ hn0 hq0, one_mul]; linarith
  · rw [le_sub_iff_add_le, inv_eq_one_div, div_add_div _ _ (ne_of_gt hn0) (ne_of_gt hq0),
      div_le_one (by positivity)]
    nlinarith

/-- **And it gives a lonely instant**, for a real difference set covered by the whole numbers. -/
theorem exists_lonely_of_ratWorks {ds : Finset ℝ} (L : List ℕ) (a q : ℕ) (hq : 0 < q) (ha : 0 < a)
    (hcov : ∀ d ∈ ds, ∃ m ∈ L, d = (m : ℝ)) (h : ratWorks n L a q = true) :
    ∃ s : ℝ, 0 < s ∧ Lonely n ds s := by
  refine ⟨(a : ℝ) / (q : ℝ), by positivity, fun d hd => ?_⟩
  obtain ⟨m, hm, rfl⟩ := hcov d hd
  exact lonely_of_ratWorks L a q hq h m hm

/-! ## 2. the four divisibility criteria at order five

Each is `ratWorks 5 L 1 q` for `q = 2, 3, 4, 5`, and each reduces to a single divisibility
condition because the band `[q/5, 4q/5]` contains every nonzero residue for `q ≤ 5`. -/

/-- **The divisibility rule, at every order.**  For `q ≤ n` the band `[q/n, (n−1)q/n]` excludes
only the zero residue, so `t = 1/q` is lonely exactly when no disparity is divisible by `q`.

Both edges need `q ≤ n`: the near edge is `n·r ≥ q` with `r ≥ 1`, and the far edge is
`n(q−1) ≤ (n−1)q`, which is `q ≤ n` again.  So the rule gives `n − 1` conditions at order `n` —
`q = 2, …, n` — and it is a **rule with a condition**, not a bound on `q`. -/
theorem ratWorks_le_order (L : List ℕ) (q : ℕ) (hq0 : 0 < q) (hqn : q ≤ n)
    (h : ∀ d ∈ L, ¬ (q ∣ d)) : ratWorks n L 1 q = true := by
  have hn2 : 2 ≤ n := Fact.out
  unfold ratWorks
  rw [List.all_eq_true]
  intro d hd
  have hmod : d % q ≠ 0 := fun hc => h d hd (Nat.dvd_of_mod_eq_zero hc)
  have hlt : d % q < q := Nat.mod_lt _ hq0
  simp only [mul_one, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨?_, ?_⟩
  · calc q ≤ n := hqn
      _ = n * 1 := (Nat.mul_one n).symm
      _ ≤ n * (d % q) := Nat.mul_le_mul_left n (by omega)
  · have h1 : n * (d % q) ≤ n * (q - 1) := Nat.mul_le_mul_left n (by omega)
    have h2 : n * (q - 1) ≤ (n - 1) * q := by
      have e1 : n * (q - 1) = n * q - n := by
        rw [Nat.mul_sub, Nat.mul_one]
      have e2 : (n - 1) * q = n * q - q := by
        rw [Nat.sub_mul, Nat.one_mul]
      have : q ≤ n * q := Nat.le_mul_of_pos_left q (by omega)
      omega
    omega

/-- `q ≤ 5` at order five: the special case of `ratWorks_le_order`. -/
theorem ratWorks_small (L : List ℕ) (q : ℕ) (hq0 : 0 < q) (hq5 : q ≤ 5)
    (h : ∀ d ∈ L, ¬ (q ∣ d)) : ratWorks 5 L 1 q = true := by
  unfold ratWorks
  rw [List.all_eq_true]
  intro d hd
  have hmod : d % q ≠ 0 := fun hc => h d hd (Nat.dvd_of_mod_eq_zero hc)
  have hlt : d % q < q := Nat.mod_lt _ hq0
  simp only [mul_one, Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- **Order five, `t = 1/2`: every disparity odd.** -/
theorem lonely_half_of_all_odd {ds : Finset ℝ} (L : List ℕ)
    (hcov : ∀ d ∈ ds, ∃ m ∈ L, d = (m : ℝ)) (h : ∀ d ∈ L, ¬ (2 ∣ d)) :
    ∃ s : ℝ, 0 < s ∧ Lonely 5 ds s :=
  exists_lonely_of_ratWorks (n := 5) L 1 2 (by norm_num) (by norm_num) hcov
    (ratWorks_small L 2 (by norm_num) (by norm_num) h)

/-- **Order five, `t = 1/3`: no disparity divisible by three.** -/
theorem lonely_third_of_not_three {ds : Finset ℝ} (L : List ℕ)
    (hcov : ∀ d ∈ ds, ∃ m ∈ L, d = (m : ℝ)) (h : ∀ d ∈ L, ¬ (3 ∣ d)) :
    ∃ s : ℝ, 0 < s ∧ Lonely 5 ds s :=
  exists_lonely_of_ratWorks (n := 5) L 1 3 (by norm_num) (by norm_num) hcov
    (ratWorks_small L 3 (by norm_num) (by norm_num) h)

/-- **Order five, `t = 1/4`: no disparity divisible by four.**  This is the one that settles
`(1,10,21,22)`, which survived every flank criterion in this development. -/
theorem lonely_quarter_of_not_four {ds : Finset ℝ} (L : List ℕ)
    (hcov : ∀ d ∈ ds, ∃ m ∈ L, d = (m : ℝ)) (h : ∀ d ∈ L, ¬ (4 ∣ d)) :
    ∃ s : ℝ, 0 < s ∧ Lonely 5 ds s :=
  exists_lonely_of_ratWorks (n := 5) L 1 4 (by norm_num) (by norm_num) hcov
    (ratWorks_small L 4 (by norm_num) (by norm_num) h)

/-- **Order five, `t = 1/5`: no disparity divisible by five.**  P1′ without the flank. -/
theorem lonely_fifth_of_not_five {ds : Finset ℝ} (L : List ℕ)
    (hcov : ∀ d ∈ ds, ∃ m ∈ L, d = (m : ℝ)) (h : ∀ d ∈ L, ¬ (5 ∣ d)) :
    ∃ s : ℝ, 0 < s ∧ Lonely 5 ds s :=
  exists_lonely_of_ratWorks (n := 5) L 1 5 (by norm_num) (by norm_num) hcov
    (ratWorks_small L 5 (by norm_num) (by norm_num) h)

/-! ## 2a. the rule family's failure condition, exactly

A rule that only ever *fires* is a measurement.  A rule whose failure is **characterised** is a
case in a case analysis, and cases compose where percentages do not.  For the divisibility family
the characterisation is exact and needs no hypothesis beyond `2 ≤ q ≤ n`.

This is the object to generalise, not the order.  It turns "the rules reach `X` of the
enumeration" into "the rules fail exactly on the sets satisfying this arithmetic condition", which
is a statement about difference sets and carries no measure, no cap and no bound. -/

/-- **The divisibility rule is an `iff`.**  For `2 ≤ q ≤ n`, the instant `t = 1/q` is lonely for
the whole-number set exactly when no member is divisible by `q`. -/
theorem ratWorks_one_iff (L : List ℕ) (q : ℕ) (hq2 : 2 ≤ q) (hqn : q ≤ n) :
    ratWorks n L 1 q = true ↔ ∀ d ∈ L, ¬ (q ∣ d) := by
  constructor
  · intro h d hd hdvd
    unfold ratWorks at h
    rw [List.all_eq_true] at h
    have := h d hd
    simp only [mul_one, Bool.and_eq_true, decide_eq_true_eq] at this
    rw [Nat.mod_eq_zero_of_dvd hdvd] at this
    omega
  · exact ratWorks_le_order L q (by omega) hqn

/-- **So the whole family fails exactly on a set-cover condition.**  Every rule `q = 2 … n` fails
together precisely when the difference set covers every modulus in `[2, n]` by divisibility.

Two things follow with no further work.  Every prime `p ≤ n` must divide some disparity, so a set
missing one prime is settled outright.  And the condition is decidable, order-general, and stated
in the difference set alone — it is the case boundary the family provides. -/
theorem ratWorks_family_fails_iff (L : List ℕ) :
    (∀ q, 2 ≤ q → q ≤ n → ratWorks n L 1 q = false) ↔ (∀ q, 2 ≤ q → q ≤ n → ∃ d ∈ L, q ∣ d) := by
  constructor
  · intro h q hq2 hqn
    by_contra hc
    push_neg at hc
    have : ratWorks n L 1 q = true := (ratWorks_one_iff L q hq2 hqn).mpr (fun d hd => hc d hd)
    rw [h q hq2 hqn] at this; exact Bool.noConfusion this
  · intro h q hq2 hqn
    obtain ⟨d, hd, hdvd⟩ := h q hq2 hqn
    by_contra hc
    rw [Bool.not_eq_false] at hc
    exact (ratWorks_one_iff L q hq2 hqn).mp hc d hd hdvd

/-- **A set missing a prime is settled.**  The contrapositive a reader wants: if some prime
`p ≤ n` divides no disparity, `t = 1/p` is lonely. -/
theorem lonely_of_prime_missed {ds : Finset ℝ} (L : List ℕ) (p : ℕ) (hp : p.Prime) (hpn : p ≤ n)
    (hcov : ∀ d ∈ ds, ∃ m ∈ L, d = (m : ℝ)) (h : ∀ d ∈ L, ¬ (p ∣ d)) :
    ∃ s : ℝ, 0 < s ∧ Lonely n ds s :=
  exists_lonely_of_ratWorks L 1 p hp.pos (by norm_num) hcov
    (ratWorks_le_order L p hp.pos hpn h)

/-- **The `q = n` rule subsumes the coprime-flank rule.**  `Resonance.flankWorks_of_coprime` needs
exactly "no disparity is divisible by `n`" (`Resonance.coprime_rule_applies_iff`), and that is the
`q = n` instance of the divisibility family — which additionally needs no coprime flank to exist.

So the coprime-flank rule adds nothing to the case analysis, and one case can be deleted from it.
Worth knowing before item 3: families that look distinct can be nested. -/
theorem divisibility_subsumes_coprime_flank (L : List ℕ) (h : ∀ d ∈ L, ¬ (n ∣ d)) :
    ratWorks n L 1 n = true := by
  have hn2 : 2 ≤ n := Fact.out
  exact ratWorks_le_order L n (by omega) (le_refl n) h

/-! ## 3. the worked instance: the set that survived everything else -/

/-- `(1, 10, 21, 22)` survived P1′, P2, P3, P4, P5, P6 and P7.  It is lonely at `t = 1/4`, for the
single reason that none of its disparities is divisible by four. -/
theorem residue_instance_1_10_21_22 :
    ratWorks 5 [1, 10, 21, 22] 1 4 = true := by decide

/-! ## 4. the flank index is a Beatty problem

The flank condition is usually written on the residue `(d·a) mod n·e`.  Written on the **floor**
instead it says what kind of object the index is:

    floor(d·a / e) mod n  ∈  {1, …, n−2},  or  = n−1 with `e ∣ d·a`.

So `floor(d·a/e)` is the Beatty sequence of slope `d/e`, and the flank index `a` is a point at
which `card ds − 1` Beatty sequences simultaneously avoid two residues mod `n`.  The flank itself
is free, since `d = e` gives `floor(a) = a ≡ 1 (mod n)`.

That is a deterministic, arithmetic statement — the same solution set every time, no density in
it — and it names the tool the development has never used: continued fractions of the ratios
`d/e`, and the three-distance theorem.  Every criterion so far (P1′, P5, P6, P7) is a closed-form
choice of `a`; what none of them is, is a choice made from the continued fraction.

The clause `= n−1 with e ∣ d·a` is the **closed endpoint** of the band and is not optional:
dropping it makes eight primitive 4-sets in `[1,30]` appear to have no working opening at the
largest flank, contradicting the exhaustive fact that one always does
(`experiments/nN/beatty_form_v1.out`). -/

/-- **The residue band, read on the floor.**  `(d·a) mod n·e ∈ [e, (n−1)·e]` exactly when the
Beatty value `floor(d·a/e)` is `1 … n−2` mod `n`, or `n−1` with `d·a` a multiple of `e`. -/
theorem band_iff_beatty (n e x : ℕ) (he : 0 < e) (hn : 2 ≤ n) :
    (e ≤ x % (n * e) ∧ x % (n * e) ≤ (n - 1) * e) ↔
      ((1 ≤ (x / e) % n ∧ (x / e) % n ≤ n - 2) ∨ ((x / e) % n = n - 1 ∧ x % e = 0)) := by
  have hn0 : 0 < n := by omega
  have hdiv : x % (n * e) / e = x / e % n := by
    rw [Nat.mul_comm]; exact Nat.mod_mul_right_div_self x e n
  have hmod : x % (n * e) % e = x % e := Nat.mod_mod_of_dvd x ⟨n, by ring⟩
  have hsplit : x % (n * e) = e * (x / e % n) + x % e := by
    conv_lhs => rw [← Nat.div_add_mod (x % (n * e)) e]
    rw [hdiv, hmod]
  have hlt : x % e < e := Nat.mod_lt _ he
  have hqlt : x / e % n < n := Nat.mod_lt _ hn0
  set s := x / e % n with hsdef
  set r := x % e with hrdef
  rw [hsplit]
  constructor
  · rintro ⟨h1, h2⟩
    have hs1 : 1 ≤ s := by
      by_contra hc
      have hz : s = 0 := by omega
      rw [hz, Nat.mul_zero, Nat.zero_add] at h1
      omega
    by_cases hsn : s = n - 1
    · refine Or.inr ⟨hsn, ?_⟩
      rw [hsn] at h2
      have heq : e * (n - 1) = (n - 1) * e := Nat.mul_comm _ _
      omega
    · exact Or.inl ⟨hs1, by omega⟩
  · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
    · refine ⟨?_, ?_⟩
      · calc e = e * 1 := (Nat.mul_one e).symm
          _ ≤ e * s := Nat.mul_le_mul_left e ha
          _ ≤ e * s + r := Nat.le_add_right _ _
      · have h1 : e * s ≤ e * (n - 2) := Nat.mul_le_mul_left e hb
        have h2 : e * (n - 2) + e = (n - 1) * e := by
          have hr : n - 1 = (n - 2) + 1 := by omega
          rw [hr]; ring
        omega
    · rw [ha, hb, Nat.add_zero]
      have heq : e * (n - 1) = (n - 1) * e := Nat.mul_comm _ _
      refine ⟨?_, le_of_eq heq⟩
      rw [heq]
      calc e = 1 * e := (Nat.one_mul e).symm
        _ ≤ (n - 1) * e := Nat.mul_le_mul_right e (by omega)

end LRC.RationalN
