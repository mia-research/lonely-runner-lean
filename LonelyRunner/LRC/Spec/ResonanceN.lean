import LonelyRunner.LRC.Spec.FlankFiniteN

/-!
# Arithmetic resonance, and why prime orders have no gap

2026-09-21.  A disparity is **resonant with `n`** when it shares a factor with `n`.  This is the
quantity in the manuscript's Theorem 4.13 (the cage): a resonant offset is confined to
`[gcd(d,n)/n, 1 − gcd(d,n)/n]` and cannot come near the subject at a grid instant.  It is also
the quantity behind over-blocking: a disparity on a coarse lattice blocks more openings than the
generic `2e/n` (measured: `d = 8` at `e = 16`, `n = 8` blocks 8, not 4).

Measured (`docs/nN/RESONANCE_AND_PARITY_v1.md`): across every order and blocker count tested, a
difference set fails at its **largest flank** only if it contains a resonant disparity, with no
counterexample.  What this file proves is the part that follows from the framework:

* **non-resonance is already enough for the obligation, at every order** — it implies no
  disparity is divisible by `n`, and `LRC.SpecN.lonelyAt_inv_of_not_dvd` then names the instant
  `1/n` (`lonelyForSubject_of_no_resonance`);
* **at a prime order, resonance and divisibility by `n` are the same condition**
  (`resonant_iff_dvd_of_prime`).  That is the mechanism: at prime `n` the framework's criterion
  covers exactly the non-resonant sets with nothing left over, while at composite `n` the two
  conditions differ and the difference is indexed by the proper divisors of `n`.  Measured, 147
  failures pass the divisibility test and still fail, all of them at composite orders.

The extra content of the empirical law — that the witness can be taken at the **largest flank** —
is `CoprimeLargestFlank` below.  It is **not proved**, and appears only as a hypothesis.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace LRC.Resonance

open Flanks MomentIterationN LRC.SpecN LRC.FlankFinite

variable {n : ℕ} [Fact (2 ≤ n)]

/-! ## 1. resonance -/

/-- A whole-number disparity is **resonant with `n`** when it shares a factor with `n`. -/
def Resonant (n m : ℕ) : Prop := 1 < Nat.gcd m n

instance (n m : ℕ) : Decidable (Resonant n m) := by unfold Resonant; infer_instance

theorem gcd_ne_zero (m : ℕ) : Nat.gcd m n ≠ 0 := by
  have hn2 : 2 ≤ n := Fact.out
  intro h
  rw [Nat.gcd_eq_zero_iff] at h
  omega

/-- Non-resonance is coprimality. -/
theorem not_resonant_iff {m : ℕ} : ¬ Resonant n m ↔ Nat.gcd m n = 1 := by
  unfold Resonant
  have := gcd_ne_zero (n := n) m
  omega

/-- **Non-resonance rules out divisibility** — the bridge to the framework's proved criterion. -/
theorem not_dvd_of_not_resonant {m : ℕ} (h : ¬ Resonant n m) : ¬ (n ∣ m) := by
  have hg : Nat.gcd m n = 1 := not_resonant_iff.mp h
  have hn2 : 2 ≤ n := Fact.out
  intro hd
  have hdd : n ∣ Nat.gcd m n := Nat.dvd_gcd hd dvd_rfl
  rw [hg] at hdd
  have := Nat.le_of_dvd one_pos hdd
  omega

/-- **At a prime order, resonance and divisibility by `n` are the same condition.**

This is why prime orders have no gap.  `LRC.SpecN.lonelyAt_inv_of_not_dvd` settles every subject
none of whose disparities is divisible by `n`; at prime `n` that is exactly the non-resonant
subjects, so nothing is left over.  At composite `n` the conditions part company, and the sets
between them are the ones the criterion misses. -/
theorem resonant_iff_dvd_of_prime (hp : n.Prime) {m : ℕ} :
    Resonant n m ↔ n ∣ m := by
  unfold Resonant
  constructor
  · intro h
    have h1 : Nat.gcd m n ∣ n := Nat.gcd_dvd_right m n
    have he := (Nat.Prime.eq_one_or_self_of_dvd hp _ h1).resolve_left (by omega)
    have h2 : Nat.gcd m n ∣ m := Nat.gcd_dvd_left m n
    rwa [he] at h2
  · intro hd
    have hn2 : 2 ≤ n := Fact.out
    have hdd : n ∣ Nat.gcd m n := Nat.dvd_gcd hd dvd_rfl
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero (gcd_ne_zero (n := n) m)) hdd
    omega

/-! ## 2. the non-resonant case is settled, at every order -/

/-- **No resonant disparity ⟹ the subject is lonely at the named instant `1/n`.**
Holds at every order; at a prime order it is exactly the non-resonant subjects, by
`resonant_iff_dvd_of_prime`. -/
theorem lonelyAt_inv_of_no_resonance {v : Fin n → ℝ} {k : Fin n}
    (h : ∀ i : Fin n, i ≠ k → ∃ a : ℤ, v i - v k = (a : ℝ) ∧ ¬ Resonant n a.natAbs) :
    LonelyAt v k ((n : ℝ)⁻¹) := by
  refine lonelyAt_inv_of_not_dvd (fun i hi => ?_)
  obtain ⟨a, ha, hres⟩ := h i hi
  refine ⟨a, ha, ?_⟩
  rw [Int.ofNat_dvd_left]
  exact not_dvd_of_not_resonant hres

/-- **And the subject's obligation is discharged there.** -/
theorem lonelyForSubject_of_no_resonance {v : Fin n → ℝ} {k : Fin n}
    (h : ∀ i : Fin n, i ≠ k → ∃ a : ℤ, v i - v k = (a : ℝ) ∧ ¬ Resonant n a.natAbs) :
    LonelyForSubject v k :=
  ⟨(n : ℝ)⁻¹, inv_pos.mpr (n_pos (n := n)), lonelyAt_inv_of_no_resonance h⟩

/-- **All four doors follow**, since `doors_agree` is an equivalence. -/
theorem doors_of_no_resonance {v : Fin n → ℝ} (hv : Function.Injective v) (k : Fin n)
    (h : ∀ i : Fin n, i ≠ k → ∃ a : ℤ, v i - v k = (a : ℝ) ∧ ¬ Resonant n a.natAbs) :
    DoorFlank v k ∧ DoorArrives v k ∧ DoorCapped v k ∧ DoorFAM v k := by
  obtain ⟨h1, h2, h3, h4⟩ := doors_agree hv k
  have hL := lonelyForSubject_of_no_resonance h
  exact ⟨h1.mpr hL, h2.mpr hL, h3.mpr hL, h4.mpr hL⟩

/-! ## 3. what the measurement adds, stated rather than assumed

The sweeps found more than §2: under non-resonance the witness can be taken at the subject's
**largest** disparity, not merely at `1/n`.  That is strictly stronger and is **not proved**. -/

open Classical in
/-- **The candidate.**  Under non-resonance the *largest* disparity hosts a lonely opening.
`[EMPIRICAL — no counterexample over the ranges of `docs/nN/RESONANCE_AND_PARITY_v1.md` §1]`.
**Not proved.**  A hypothesis wherever it appears. -/
def CoprimeLargestFlank (n : ℕ) : Prop :=
  ∀ ds : Finset ℝ, (∀ d ∈ ds, 0 < d) →
    (∀ d ∈ ds, ∃ m : ℕ, d = (m : ℝ) ∧ ¬ Resonant n m) →
    ∀ e ∈ ds, (∀ d ∈ ds, d ≤ e) → ∃ j : ℕ, Lonely n ds (flankOpening n e j)

/-! ## 4. the mechanism at a prime order — an explicit opening  `[PROVED]`

The measurement said a set fails its largest flank only if it is resonant.  At a **prime** order
that has a proof, and the proof exhibits the opening.  It also shows why the statement is about
primality and not about size: the step `n ∤ d` and `n ∤ s` therefore `n ∤ d·s` is Euclid's lemma,
and it is exactly what fails at a composite order — at `n = 8` the pairs `(2,4), (4,2), (4,4)`
have `8 ∣ d·s` with `8 ∤ d` and `8 ∤ s`, and at every prime order there are none. -/

/-! ### the hypothesis was never primality — it is the flank's resonance

2026-09-22.  `flankWorks_of_prime` below carries `n.Prime`, and it is used in exactly two places:
to get `Nat.Coprime e n` out of `¬ n ∣ e`, and to split `n ∣ d·s` by Euclid.  Neither needs a
prime.  Take coprimality as the hypothesis and the second split follows because `s` is a unit.

So the discriminator is **`gcd(e, n) = 1`** — the flank being **non-resonant**, `¬ Resonant n e`
— and not the primality of `n`, and not its parity.  At prime `n` the two coincide, because
`n ∤ e` and `gcd(e,n) = 1` say the same thing there; that coincidence is the whole reason
primality looked load-bearing.  At composite `n` they come apart, and it is the gcd that matters.

The fraction of usable flanks at order `n` is therefore `φ(n)/n = ∏_{p ∣ n} (1 − 1/p)`:

    n      5     6     7     8     9    10    11    12
    φ(n)/n 4/5   1/3   6/7   1/2   2/3   2/5  10/11  1/3

Primes are best because `φ(p)/p = 1 − 1/p`.  Even orders are never better than `1/2` because `2`
always divides them — which is the odds-and-evens effect, but it is a **consequence** of the
totient, not the mechanism.  Order 9, an odd prime power, sits at `2/3`, between the primes and
order 8; parity alone would put it with the primes and primality alone would put it with 6.
This is §5's `φ(n)` count (`isolation_iff_coprime`, `card_coprime_eq_totient`), arrived at from
the flank side. -/

/-- **The criterion at every order.**  A flank coprime to `n`, with no other disparity divisible
by `n`, hosts a lonely opening.  No primality: the witness is `a = e·(e⁻¹ mod n)`, whose readings
are `e·(d·s mod n)`, and `gcd(s,n) = 1` turns `n ∣ d·s` into `n ∣ d` with no appeal to Euclid. -/
theorem flankWorks_of_coprime (hcop : Nat.Coprime e n) (L : List ℕ) (he : 0 < e)
    (hL : ∀ d ∈ L, ¬ (n ∣ d)) :
    flankWorks n L e = true := by
  have hn2 : 2 ≤ n := Fact.out
  haveI : NeZero n := ⟨by omega⟩
  set s : ℕ := ((e : ZMod n)⁻¹).val with hs
  have hmod : (e * s) % n = 1 % n := by
    have h1 : ((e * s : ℕ) : ZMod n) = 1 := by
      rw [hs]; push_cast [ZMod.natCast_val, ZMod.cast_id]
      exact ZMod.mul_inv_of_unit _ ((ZMod.isUnit_iff_coprime e n).mpr hcop)
    exact (ZMod.natCast_eq_natCast_iff' (e * s) 1 n).mp (by rw [h1]; simp)
  have hslt : s < n := by rw [hs]; exact ZMod.val_lt _
  have hone : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
  rw [hone] at hmod
  have hscop : Nat.Coprime s n := by
    have : Nat.gcd s n ∣ 1 := by
      have h1 : Nat.gcd s n ∣ e * s := Dvd.dvd.mul_left (Nat.gcd_dvd_left s n) e
      have h2 : Nat.gcd s n ∣ n := Nat.gcd_dvd_right s n
      have h3 : Nat.gcd s n ∣ (e * s) % n := (Nat.dvd_mod_iff h2).mpr h1
      rwa [hmod] at h3
    exact Nat.eq_one_of_dvd_one this
  have hge : 1 ≤ e * s := by
    rcases Nat.eq_zero_or_pos (e * s) with h | h
    · rw [h] at hmod; simp at hmod
    · exact h
  set j : ℕ := (e * s) / n with hj
  have hkey : n * j + 1 = e * s := by
    have h := Nat.div_add_mod (e * s) n
    rw [hmod] at h
    rw [hj]; omega
  have hjlt : j < e := by
    have h1 : e * s ≤ e * (n - 1) := Nat.mul_le_mul_left e (by omega)
    have h2 : e * (n - 1) < e * n := (Nat.mul_lt_mul_left he).mpr (by omega)
    have h3 : n * j < n * e := by
      have : n * j + 1 ≤ e * n := by rw [hkey]; omega
      have hcomm : e * n = n * e := Nat.mul_comm e n
      omega
    exact Nat.lt_of_mul_lt_mul_left h3
  unfold flankWorks
  rw [List.any_eq_true]
  refine ⟨j, List.mem_range.mpr hjlt, ?_⟩
  rw [List.all_eq_true]
  intro d hd
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  have hdn : ¬ (n ∣ d) := hL d hd
  set r : ℕ := (d * s) % n with hr
  have hrlt : r < n := Nat.mod_lt _ (by omega)
  have hrne : r ≠ 0 := by
    intro h0
    have hdvd : n ∣ d * s := Nat.dvd_of_mod_eq_zero (by rw [← hr]; exact h0)
    exact hdn ((Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.symm hscop)) hdvd)
  have hval : (d * (n * j + 1)) % (n * e) = e * r := by
    rw [hkey]
    have hsplit : d * (e * s) = n * e * ((d * s) / n) + e * r := by
      have := Nat.div_add_mod (d * s) n
      calc d * (e * s) = e * (d * s) := by ring
        _ = e * (n * ((d * s) / n) + r) := by rw [hr]; rw [Nat.div_add_mod]
        _ = n * e * ((d * s) / n) + e * r := by ring
    rw [hsplit, show n * e * ((d * s) / n) + e * r = e * r + n * e * ((d * s) / n) by ring,
      Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by nlinarith [hrlt, he])
  rw [hval]
  constructor
  · nlinarith [hrne, he, Nat.one_le_iff_ne_zero.mpr hrne]
  · have hle : r ≤ n - 1 := by omega
    nlinarith [hle, he]

/-- **`Resonant` is the right name for it.**  The criterion asks that the flank be non-resonant. -/
theorem flankWorks_of_not_resonant (hres : ¬ Resonant n e) (L : List ℕ) (he : 0 < e)
    (hL : ∀ d ∈ L, ¬ (n ∣ d)) :
    flankWorks n L e = true := by
  have hn2 : 2 ≤ n := Fact.out
  refine flankWorks_of_coprime ?_ L he hL
  unfold Resonant at hres
  have hpos : 0 < Nat.gcd e n := Nat.gcd_pos_of_pos_right e (by omega)
  unfold Nat.Coprime
  omega

/-! ### item 2 of the working list: the coprime rule's applicability, characterised

The divisibility family has an exact failure condition (`RationalN.ratWorks_family_fails_iff`).
This is the same for the coprime-flank rule, and it collapses further than expected.

Note what is being characterised: **when the rule's hypotheses can be met at some flank**, not
when `flankWorks` happens to be true.  `flankWorks` can hold for reasons this rule does not see,
and conflating the two would be the `DoorLargestFlank` error again. -/

/-- **The coprime-flank rule applies exactly when no disparity is divisible by `n` and some
disparity is coprime to it.**  The collapse: a flank coprime to `n` is itself not divisible by
`n`, so "all the *others* avoid `n`" already forces "all of them avoid `n`".

So the rule's blind spot is precisely the sets carrying a multiple of `n` — nothing finer. -/
theorem coprime_rule_applies_iff (L : List ℕ) :
    (∃ e ∈ L, Nat.Coprime e n ∧ ∀ d ∈ L, d ≠ e → ¬ (n ∣ d)) ↔
      ((∀ d ∈ L, ¬ (n ∣ d)) ∧ ∃ e ∈ L, Nat.Coprime e n) := by
  have hn2 : 2 ≤ n := Fact.out
  constructor
  · rintro ⟨e, heL, hcop, hrest⟩
    refine ⟨fun d hd => ?_, ⟨e, heL, hcop⟩⟩
    by_cases hde : d = e
    · subst hde
      intro hdvd
      have : Nat.gcd d n = n := Nat.gcd_eq_right hdvd
      rw [Nat.Coprime, this] at hcop
      omega
    · exact hrest d hd hde
  · rintro ⟨hall, e, heL, hcop⟩
    exact ⟨e, heL, hcop, fun d hd _ => hall d hd⟩

/-- **And the rule does fire on that condition.** -/
theorem exists_flankWorks_of_no_multiple (L : List ℕ) (hpos : ∀ d ∈ L, 0 < d)
    (hall : ∀ d ∈ L, ¬ (n ∣ d)) {e : ℕ} (heL : e ∈ L) (hcop : Nat.Coprime e n) :
    flankWorks n L e = true :=
  flankWorks_of_coprime hcop L (hpos e heL) hall

/-! ### item 1 of the working list: the case boundary, stated exactly

Write `M = { d ∈ ds : n ∣ d }`.  By `coprime_rule_applies_iff` the coprime rule reaches exactly
`M = ∅` (given some disparity coprime to `n`).  The complement splits in three, and only one part
is closed:

* `M = ∅` — `exists_flankWorks_of_no_multiple`.  **Closed.**
* `M = {m}` with `m` the largest — take `m` as the flank: `flankWorks_of_prime_dvd`.  **Closed**
  at prime `n`.
* `M = {m}` with `m` **not** the largest — **open**, and it is exactly what the `ρ`-construction
  (`LRC.Witness.flankWorks_of_witness`) was built for, as a per-set check rather than a theorem.
* `|M| ≥ 2` — **open**.

Why the third resists the second's proof: `flankWorks_of_prime_dvd` reaches the flank through
`exists_goodK`, a pigeonhole on `k` in which each disparity forbids **one** value, because
`(d·k) mod n ≠ 0` is automatic when `gcd(d,n) = 1` and `k ≠ 0`.  With the flank not largest, the
disparities above it carry an offset `d / e ≠ 0` (`flankWorks_of_shifted`'s `hgood`), and then
`(d·k + d/e) mod n ≠ 0` is no longer automatic: each such disparity forbids **two** values of `k`.
The count `L.length + 1 < n` that carries the zero-offset case is `n − 2 < n − 1`, which has no
room to absorb a second forbidden value.  That is the exact arithmetic of the obstruction, and it
is what a proof of the third case has to beat. -/

/-! ### the shifted family's budget, exactly

`flankWorks_of_shifted` reaches a flank divisible by `n` through a good `k`.  Each non-flank
disparity `d` forbids values of `k`:

* the residue `n−1` is forbidden unless `e ∣ d` — **one** value, always;
* the residue `0` is forbidden too, but only when the offset `d / e` is nonzero: with zero offset
  the condition reads `(d·k) mod n ≠ 0`, which is automatic for `gcd(d,n) = 1` and `k ≠ 0`.

So the forbidden count is `|L| + #{d ∈ L : e ≤ d}`, against `n − 1` available values of `k`.
A subject at order `n` has `n − 2` non-flank disparities, so the budget is

    (n − 2) + #{d : e ≤ d}  <  n − 1      ⟺      #{d : e ≤ d} = 0,

which is exactly the `∀ d ∈ L, d < e` hypothesis `flankWorks_of_prime_dvd` already carries.

**The budget has zero slack.**  One disparity above the flank exhausts it.  That is why item 1's
third case — one multiple of `n`, not the largest — cannot be reached by sharpening this
pigeonhole, and needs the `ρ`-construction (`LRC.Witness.flankWorks_of_witness`) instead.  Stated
as arithmetic rather than left as a remark. -/

/-- **Every opening index is a unit mod `n`, by construction.**  A flank opening has
`a = n·j + 1`, so `gcd(a, n) = gcd(1, n) = 1` with nothing assumed.  The framework never
exhibits a witness that is not a unit — the residue class `1 mod n` sits inside `(ℤ/n)ˣ`. -/
theorem witness_is_unit (j : ℕ) : Nat.Coprime (n * j + 1) n := by
  unfold Nat.Coprime
  rw [Nat.add_comm, Nat.gcd_comm, Nat.gcd_rec]
  simp [Nat.add_mul_mod_self_left]

/-- **The pigeonhole's budget is `φ(n)`, not `n − 1`.**  `exists_goodK` ranges `k` over `[1, n)`
and uses primality to rule out `(d·k) mod n = 0`.  At composite `n` that step fails, and the `k`
actually available are the **units** — `φ(n)` of them.  So the budget at general `n` is
`|L| < φ(n)`, of which `|L| + 1 < n` is the prime specialisation, since `φ(p) = p − 1`.

**And that rewrites the shifted family's primality as a totient fact.**  A subject at order `n`
has `n − 2` non-flank disparities, so the family needs `n − 2 < φ(n)` — and by
`Nat.totient_eq_iff_prime` that holds **exactly at prime `n`**, because `φ(n) ≤ n − 1` always,
with equality only there.

So the primality in `flankWorks_of_prime_dvd` is not Euclid's lemma doing the work.  It is
`φ(n) = n − 1`.  That is the second time in this development a `φ(n)` effect was recorded as a
statement about primes — the first was `flankWorks_of_prime`, corrected above. -/
theorem shifted_budget_is_totient : (n - 2 < Nat.totient n) ↔ n.Prime := by
  have hn2 : 2 ≤ n := Fact.out
  have h1 : Nat.totient n < n := Nat.totient_lt n (by omega)
  constructor
  · intro h
    have heq : Nat.totient n = n - 1 := by omega
    exact (Nat.totient_eq_iff_prime (by omega)).mp heq
  · intro hp
    rw [(Nat.totient_eq_iff_prime (by omega)).mpr hp]
    omega

/-- **Where else `φ` is doing the work, for the record.**  Three more sites, none of them new
mathematics, all of them places this development named something else:

* the **usable flanks** are the non-resonant residues, `φ(n)` of them
  (`card_nonresonant_eq_totient`);
* the **rational family** `ratWorks n L a q` has `φ(q)` choices of `a` at each `q`, and the
  divisibility corollaries use only `a = 1` — the family is `φ(q)`-fold and only one member of
  each is drawn on;
* the **`ρ`-construction** needs `gcd(m', e) = 1` to aim, which is a `φ(e)` condition at the
  flank's own modulus rather than at `n`.

Stated so the next session does not rediscover any of them as a fact about primes. -/
theorem totient_le_sub_one : Nat.totient n ≤ n - 1 := by
  have hn2 : 2 ≤ n := Fact.out
  have := Nat.totient_lt n (by omega)
  omega

/-- **The pigeonhole budget at a full disparity set, exhausted.**  With `n − 2` non-flank
disparities the forbidden count reaches `n − 1` as soon as one disparity sits at or above the
flank, so no `k` is guaranteed.  The hypothesis `flankWorks_of_prime_dvd` carries is tight for
this method. -/
theorem shifted_budget_exhausted {L : ℕ} {above : ℕ} (hL : L = n - 2) (habove : 1 ≤ above) :
    ¬ (L + above < n - 1) := by
  -- NOTE (corrected below by `shifted_budget_is_totient`): `n - 1` here is the PRIME-case count.
  -- The general budget is `φ(n)`, which is smaller at composite `n`, so this bound is the
  -- loosest case and the conclusion holds a fortiori.
  have hn2 : 2 ≤ n := Fact.out
  omega

/-- **And with no disparity above the flank the budget holds**, which is the existing case. -/
theorem shifted_budget_holds {L : ℕ} (hL : L = n - 2) (hn3 : 3 ≤ n) :
    L + 0 < n - 1 := by
  have hn2 : 2 ≤ n := Fact.out
  omega

/-- **The usable flanks are counted by Euler's totient.**  `flankWorks_of_not_resonant` applies
at a flank exactly when `e` is non-resonant, and there are `φ(n)` such residues mod `n`.

This is §5's `φ(n)` count (`ConstructionN.card_coprime_eq_totient`) reached from the flank side:
there it counts the arithmetic-progression instants, here the flanks the criterion can use.  It
is the same quantity, and it is what distinguishes the orders — not primality, not parity. -/
theorem card_nonresonant_eq_totient :
    ((Finset.range n).filter (fun e => ¬ Resonant n e)).card = Nat.totient n := by
  have hn2 : 2 ≤ n := Fact.out
  rw [Nat.totient]
  congr 1
  apply Finset.filter_congr
  intro e _
  simp only [Resonant, Nat.Coprime, eq_iff_iff]
  have hpos : 0 < Nat.gcd e n := Nat.gcd_pos_of_pos_right e (by omega)
  rw [Nat.gcd_comm n e]
  omega

/-- **Read as a fraction**: the criterion's usable flanks are a `φ(n)/n` share of the residues.
`φ(p)/p = 1 − 1/p` puts the primes at the top; `2 ∣ n` forces `φ(n)/n ≤ 1/2`, which is the
odds-and-evens effect as a consequence rather than a cause. -/
theorem nonresonant_lt_card :
    ((Finset.range n).filter (fun e => ¬ Resonant n e)).card ≤ n := by
  rw [card_nonresonant_eq_totient]
  exact le_trans (Nat.totient_le n) (le_refl n)

/-- **The prime form, kept.**  At prime `n`, `¬ n ∣ e` and `Nat.Coprime e n` say the same thing,
so this is `flankWorks_of_coprime` with the hypothesis in the shape the prime case wants. -/
theorem flankWorks_of_prime (hp : n.Prime) (L : List ℕ) (e : ℕ) (he : 0 < e)
    (hen : ¬ (n ∣ e)) (hL : ∀ d ∈ L, ¬ (n ∣ d)) :
    flankWorks n L e = true := by
  have hn2 : 2 ≤ n := Fact.out
  haveI : NeZero n := ⟨by omega⟩
  -- the modular inverse of e
  have hcop : Nat.Coprime e n := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hen))
  set s : ℕ := ((e : ZMod n)⁻¹).val with hs
  have hmod : (e * s) % n = 1 % n := by
    have h1 : ((e * s : ℕ) : ZMod n) = 1 := by
      rw [hs]; push_cast [ZMod.natCast_val, ZMod.cast_id]
      exact ZMod.mul_inv_of_unit _ ((ZMod.isUnit_iff_coprime e n).mpr hcop)
    exact (ZMod.natCast_eq_natCast_iff' (e * s) 1 n).mp (by rw [h1]; simp)
  have hslt : s < n := by rw [hs]; exact ZMod.val_lt _
  have hone : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
  rw [hone] at hmod
  have hsne : ¬ (n ∣ s) := by
    intro hd
    have hz : s = 0 := Nat.eq_zero_of_dvd_of_lt hd hslt
    rw [hz, Nat.mul_zero] at hmod
    simp at hmod
  -- a = e*s = n*j + 1
  have hge : 1 ≤ e * s := by
    rcases Nat.eq_zero_or_pos (e * s) with h | h
    · rw [h] at hmod; simp at hmod
    · exact h
  set j : ℕ := (e * s) / n with hj
  have hkey : n * j + 1 = e * s := by
    have h := Nat.div_add_mod (e * s) n
    rw [hmod] at h
    rw [hj]; omega
  have hjlt : j < e := by
    have h1 : e * s ≤ e * (n - 1) := Nat.mul_le_mul_left e (by omega)
    have h2 : e * (n - 1) < e * n := (Nat.mul_lt_mul_left he).mpr (by omega)
    have h3 : n * j < n * e := by
      have : n * j + 1 ≤ e * n := by rw [hkey]; omega
      have hcomm : e * n = n * e := Nat.mul_comm e n
      omega
    exact Nat.lt_of_mul_lt_mul_left h3
  -- exhibit j
  unfold flankWorks
  rw [List.any_eq_true]
  refine ⟨j, List.mem_range.mpr hjlt, ?_⟩
  rw [List.all_eq_true]
  intro d hd
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  have hdn : ¬ (n ∣ d) := hL d hd
  set r : ℕ := (d * s) % n with hr
  have hrlt : r < n := Nat.mod_lt _ (by omega)
  have hrne : r ≠ 0 := by
    intro h0
    have : n ∣ d * s := Nat.dvd_of_mod_eq_zero (by rw [← hr]; exact h0)
    rcases (Nat.Prime.dvd_mul hp).mp this with h | h
    · exact hdn h
    · exact hsne h
  have hval : (d * (n * j + 1)) % (n * e) = e * r := by
    rw [hkey]
    have hsplit : d * (e * s) = n * e * ((d * s) / n) + e * r := by
      have := Nat.div_add_mod (d * s) n
      calc d * (e * s) = e * (d * s) := by ring
        _ = e * (n * ((d * s) / n) + r) := by rw [hr]; rw [Nat.div_add_mod]
        _ = n * e * ((d * s) / n) + e * r := by ring
    rw [hsplit, show n * e * ((d * s) / n) + e * r = e * r + n * e * ((d * s) / n) by ring,
      Nat.add_mul_mod_self_left]
    exact Nat.mod_eq_of_lt (by nlinarith [hrlt, he])
  rw [hval]
  constructor
  · nlinarith [hrne, he, Nat.one_le_iff_ne_zero.mpr hrne]
  · have : r ≤ n - 1 := by omega
    nlinarith [this, he]

/-- **The real-valued form.**  Every flank, not merely the largest. -/
theorem lonely_flank_of_prime (hp : n.Prime) (L : List ℕ) (e : ℕ) (he : 0 < e)
    (hen : ¬ (n ∣ e)) (hL : ∀ d ∈ L, ¬ (n ∣ d)) :
    ∃ j : ℕ, ∀ d ∈ L, (n : ℝ)⁻¹ ≤ circDist ((d : ℝ) * flankOpening n (e : ℝ) j) :=
  LRC.FlankFinite.lonely_of_flankWorks L e he (flankWorks_of_prime hp L e he hen hL)

open Classical in
/-- **On a difference set.**  At a prime order, a subject none of whose disparities is divisible
by `n` has a lonely opening at **every** one of its flanks — in particular the largest. -/
theorem lonely_flank_of_prime_image (hp : n.Prime) {S : Finset ℕ} {e : ℕ} (he : 0 < e)
    (hen : ¬ (n ∣ e)) (hS : ∀ d ∈ S, ¬ (n ∣ d)) :
    ∃ j : ℕ, Lonely n (Finset.image (fun d : ℕ => (d : ℝ)) S) (flankOpening n (e : ℝ) j) := by
  obtain ⟨j, hj⟩ := lonely_flank_of_prime hp S.toList e he hen
    (fun d hd => hS d (Finset.mem_toList.mp hd))
  refine ⟨j, fun x hx => ?_⟩
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hx
  exact hj d (Finset.mem_toList.mpr hd)

/-! ## 5. the other half: when `n` divides the flank  `[PROVED]`

§4 needs `n ∤ e`.  When `n ∣ e` a different opening works: `a = k·e + 1`.  Then
`d·a mod n·e = e·(d·k mod n) + d`, inside the band exactly when `d·k mod n ∈ {1,…,n−2}`.
For fixed `d` coprime to `n` the map `k ↦ d·k mod n` is injective, so each disparity rules out
exactly **one** `k` out of the `n − 1` candidates — and a subject at order `n` has at most
`n − 2` non-flank disparities.  Pigeonhole supplies the `k`.

Together with §4 this settles **every** subject none of whose non-flank disparities is divisible
by a prime `n`, whether or not `n` divides the flank. -/

def GoodK (n : ℕ) (L : List ℕ) (k : ℕ) : Prop := ∀ d ∈ L, (d * k) % n ≠ 0 ∧ (d * k) % n ≠ n - 1

/-- For `d` coprime to `n`, `k ↦ d·k mod n` is injective below `n`. -/
theorem mul_mod_inj (hp : n.Prime) {d : ℕ} (hd : ¬ (n ∣ d)) {k₁ k₂ : ℕ}
    (h1 : k₁ < n) (h2 : k₂ < n) (h : (d * k₁) % n = (d * k₂) % n) : k₁ = k₂ := by
  have hcop : Nat.Coprime n d := (Nat.Prime.coprime_iff_not_dvd hp).mpr hd
  have : k₁ % n = k₂ % n := Nat.ModEq.cancel_left_of_coprime (by simpa [Nat.Coprime] using hcop) h
  rwa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this

open Classical in
theorem exists_goodK (hp : n.Prime) (L : List ℕ) (hL : ∀ d ∈ L, ¬ (n ∣ d))
    (hlen : L.length + 1 < n) : ∃ k, 0 < k ∧ k < n ∧ GoodK n L k := by
  have hn2 : 2 ≤ n := Fact.out
  by_contra hcon
  push Not at hcon
  -- every k in [1,n) fails, so each has a witness d in L with d*k = n-1 mod n
  have hwit : ∀ k, ∃ d, (0 < k → k < n → (d ∈ L ∧ (d * k) % n = n - 1)) := by
    intro k
    rcases Classical.em (0 < k ∧ k < n) with ⟨hk1, hk2⟩ | hno
    swap
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hno⟩
    have := hcon k hk1 hk2
    unfold GoodK at this
    push Not at this
    obtain ⟨d, hd, hcase⟩ := this
    refine ⟨d, fun _ _ => ⟨hd, ?_⟩⟩
    rcases Classical.em ((d * k) % n = 0) with h0 | h0
    · exfalso
      have : n ∣ d * k := Nat.dvd_of_mod_eq_zero h0
      rcases (Nat.Prime.dvd_mul hp).mp this with h | h
      · exact hL d hd h
      · have := Nat.le_of_dvd hk1 h; omega
    · tauto
  -- pick the witness map and show it is injective on [1,n)
  choose f hf using hwit
  have hinj : Set.InjOn f (Finset.Ico 1 n : Finset ℕ) := by
    intro a ha b hb hab
    simp only [Finset.coe_Ico, Set.mem_Ico] at ha hb
    obtain ⟨hm1, h1⟩ := hf a ha.1 ha.2
    obtain ⟨hm2, h2⟩ := hf b hb.1 hb.2
    rw [hab] at h1
    exact mul_mod_inj hp (hL _ hm2) ha.2 hb.2 (h1.trans h2.symm)
  have hmaps : ∀ k ∈ Finset.Ico 1 n, f k ∈ L.toFinset := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := Finset.mem_Ico.mp hk
    exact List.mem_toFinset.mpr (hf k hk1 hk2).1
  have := Finset.card_le_card_of_injOn f hmaps hinj
  rw [Nat.card_Ico] at this
  have := le_trans this (List.toFinset_card_le L)
  omega



/-- **At a prime order with `n ∣ e`, a good `k` gives a lonely opening at `a = k·e + 1`.**
The flank itself is clear because `n ∣ e` makes `k·e ≡ 0 (mod n)`; every other disparity `d`
reads `e·(d·k mod n) + d`, which sits inside `[e, (n−1)e]` exactly when `d·k mod n ∈ {1,…,n−2}`.
With at most `n − 2` non-flank disparities, `exists_goodK` supplies such a `k`. -/
theorem flankWorks_of_prime_dvd (hp : n.Prime) (L : List ℕ) (e : ℕ) (he : 0 < e)
    (hen : n ∣ e) (hdvd : ∀ d ∈ L, ¬ (n ∣ d)) (hlt : ∀ d ∈ L, d < e)
    (hlen : L.length + 1 < n) :
    flankWorks n (e :: L) e = true := by
  have hn2 : 2 ≤ n := Fact.out
  obtain ⟨k, hk0, hkn, hgood⟩ := exists_goodK hp L hdvd hlen
  obtain ⟨E, hE⟩ := hen
  set j : ℕ := k * E with hj
  have hkey : n * j + 1 = k * e + 1 := by rw [hj, hE]; ring
  have hjlt : j < e := by
    have hE0 : 0 < E := by
      rcases Nat.eq_zero_or_pos E with h | h
      · exfalso; rw [h, Nat.mul_zero] at hE; omega
      · exact h
    have : k * E < n * E := (Nat.mul_lt_mul_right hE0).mpr hkn
    rw [hj, hE]; omega
  unfold flankWorks
  rw [List.any_eq_true]
  refine ⟨j, List.mem_range.mpr hjlt, ?_⟩
  rw [List.all_eq_true]
  intro d hd
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [hkey]
  rcases List.mem_cons.mp hd with rfl | hdL
  · -- the flank itself
    have hflank : d * (k * d + 1) = d + (n * d) * (k * E) := by
      have hd : n * E = d := hE.symm
      calc d * (k * d + 1) = d + d * (k * d) := by ring
        _ = d + (n * E) * (k * d) := by rw [hd]
        _ = d + (n * d) * (k * E) := by rw [← hd]; ring
    have hlt1 : d < n * d := by
      have := (Nat.mul_lt_mul_right he).mpr (show 1 < n by omega)
      simpa using this
    rw [hflank, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt1]
    exact ⟨le_refl d, Nat.le_mul_of_pos_left d (by omega)⟩
  · -- a non-flank disparity
    set q : ℕ := (d * k) % n with hq
    have hq1 : q ≠ 0 := (hgood d hdL).1
    have hq2 : q ≠ n - 1 := (hgood d hdL).2
    have hqlt : q < n := Nat.mod_lt _ (by omega)
    have hde : d < e := hlt d hdL
    have hsplit : d * (k * e + 1) = (q * e + d) + (n * e) * ((d * k) / n) := by
      have h := Nat.div_add_mod (d * k) n
      calc d * (k * e + 1) = (d * k) * e + d := by ring
        _ = (n * ((d*k)/n) + q) * e + d := by rw [hq, h]
        _ = (q * e + d) + (n * e) * ((d * k) / n) := by ring
    rw [hsplit, Nat.add_mul_mod_self_left]
    have hub : q * e + d < n * e := by nlinarith [hqlt, hde, he]
    rw [Nat.mod_eq_of_lt hub]
    constructor
    · nlinarith [Nat.one_le_iff_ne_zero.mpr hq1, he]
    · have hqle : q ≤ n - 2 := by omega
      have h1 : q * e ≤ (n - 2) * e := Nat.mul_le_mul_right e hqle
      have hne : (n - 2) * e + e = (n - 1) * e := by
        have hstep : n - 1 = (n - 2) + 1 := by omega
        rw [hstep, Nat.succ_mul]
      omega

end LRC.Resonance
