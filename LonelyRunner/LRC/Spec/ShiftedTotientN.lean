import LonelyRunner.LRC.Spec.ResonanceN

/-!
# The shifted flank at every order: the budget is `φ(n)`

2026-09-24.  `flankWorks_of_prime_dvd` settles a flank `e` divisible by `n` through the opening
`a = k·e + 1`, where every non-flank disparity `d` reads `e·(d·k mod n) + d`.  It carried
`n.Prime`, used in one place only: to rule out `(d·k) mod n = 0` by Euclid's lemma.

Take `k` from the **units** of `ℤ/n` instead, and no prime is needed anywhere:

* a unit `k` never sends a non-multiple of `n` to `0` (`mul_unit_mod_ne_zero`);
* a disparity that shares a factor with `n` can never read `n − 1`
  (`coprime_of_mul_mod_eq_pred`), so it rules out **no** unit;
* a disparity coprime to `n` rules out **exactly one** unit, since `k ↦ d·k mod n` is injective.

So the pigeonhole runs over the `φ(n)` units against the coprime non-flank disparities only, and
the condition is: **fewer than `φ(n)` of the non-flank disparities are coprime to `n`**
(`flankWorks_of_dvd_totient`).  The prime form is the special case in which every non-multiple is
coprime and `φ(n) = n − 1` (`budget_of_prime`).

Everything here is proved; no `sorry`, no `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace LRC.Resonance

open Flanks MomentIterationN LRC.SpecN LRC.FlankFinite

variable {n : ℕ} [Fact (2 ≤ n)]

/-- **A unit never sends a non-multiple of `n` to `0`.** -/
theorem mul_unit_mod_ne_zero {d k : ℕ} (hk : Nat.Coprime n k) (hd : ¬ n ∣ d) :
    (d * k) % n ≠ 0 := by
  intro h
  exact hd (Nat.Coprime.dvd_of_dvd_mul_right hk (Nat.dvd_of_mod_eq_zero h))

/-- **Only a disparity coprime to `n` can read `n − 1`.**  If `d·k ≡ −1 (mod n)` then
`n ∣ d·k + 1`, so any common factor of `d` and `n` divides `1`. -/
theorem coprime_of_mul_mod_eq_pred {d k : ℕ} (h : (d * k) % n = n - 1) : Nat.Coprime d n := by
  have hn2 : 2 ≤ n := Fact.out
  have hdvd : n ∣ d * k + 1 := by
    apply Nat.dvd_of_mod_eq_zero
    rw [Nat.add_mod, h, Nat.mod_eq_of_lt (show 1 < n by omega), Nat.sub_add_cancel (by omega),
      Nat.mod_self]
  have hg1 : Nat.gcd d n ∣ d * k := Dvd.dvd.mul_right (Nat.gcd_dvd_left d n) k
  have hg2 : Nat.gcd d n ∣ d * k + 1 := (Nat.gcd_dvd_right d n).trans hdvd
  have hg : Nat.gcd d n ∣ 1 := (Nat.dvd_add_right hg1).mp hg2
  exact Nat.eq_one_of_dvd_one hg

open Classical in
/-- **The pigeonhole over the units.**  If no non-flank disparity is divisible by `n` and fewer
than `φ(n)` of them are coprime to `n`, some unit `k` makes every reading avoid `0` and `n − 1`. -/
theorem exists_goodK_totient (L : List ℕ) (hL : ∀ d ∈ L, ¬ (n ∣ d))
    (hbudget : (L.filter (fun d => Nat.Coprime d n)).length < Nat.totient n) :
    ∃ k, 0 < k ∧ k < n ∧ GoodK n L k := by
  have hn2 : 2 ≤ n := Fact.out
  set S : Finset ℕ := (Finset.range n).filter (Nat.Coprime n) with hS
  have hcardS : S.card = Nat.totient n := (Nat.totient_eq_card_coprime n).symm
  by_contra hcon
  -- every unit `k` is ruled out by a coprime disparity reading `n − 1`
  have hwit : ∀ k ∈ S, ∃ d, d ∈ L ∧ Nat.Coprime d n ∧ (d * k) % n = n - 1 := by
    intro k hk
    obtain ⟨hkr, hkc⟩ := Finset.mem_filter.mp hk
    have hkn : k < n := Finset.mem_range.mp hkr
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h
        have : n = 1 := by simpa using hkc
        omega
      · exact h
    have hnot : ¬ GoodK n L k := fun hg => hcon ⟨k, hk0, hkn, hg⟩
    unfold GoodK at hnot
    push Not at hnot
    obtain ⟨d, hd, hcase⟩ := hnot
    have h0 : (d * k) % n ≠ 0 := mul_unit_mod_ne_zero hkc (hL d hd)
    have h1 : (d * k) % n = n - 1 := by tauto
    exact ⟨d, hd, coprime_of_mul_mod_eq_pred h1, h1⟩
  choose! f hfL hfc hfeq using hwit
  -- the witness map is injective on the units
  have hinj : Set.InjOn f (S : Set ℕ) := by
    intro a ha b hb hab
    have ha' := hfeq a ha
    have hb' := hfeq b hb
    rw [hab] at ha'
    have hc : Nat.Coprime n (f b) := (hfc b hb).symm
    have hmod : f b * a ≡ f b * b [MOD n] := ha'.trans hb'.symm
    have hab' := Nat.ModEq.cancel_left_of_coprime (by simpa [Nat.Coprime] using hc) hmod
    have ha2 : a < n := Finset.mem_range.mp (Finset.mem_filter.mp ha).1
    have hb2 : b < n := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
    unfold Nat.ModEq at hab'
    rwa [Nat.mod_eq_of_lt ha2, Nat.mod_eq_of_lt hb2] at hab'
  have hmaps : ∀ k ∈ S, f k ∈ (L.filter (fun d => Nat.Coprime d n)).toFinset := by
    intro k hk
    rw [List.mem_toFinset, List.mem_filter]
    exact ⟨hfL k hk, by simpa using hfc k hk⟩
  have h1 := Finset.card_le_card_of_injOn f hmaps hinj
  have h2 := List.toFinset_card_le (L.filter (fun d => Nat.Coprime d n))
  omega

/-- **The shifted flank at every order.**  If `n ∣ e`, `e` exceeds every other disparity, none of
the others is divisible by `n`, and fewer than `φ(n)` of them are coprime to `n`, then the flank
`e` hosts a lonely opening, at `a = k·e + 1` for a unit `k`.  No primality. -/
theorem flankWorks_of_dvd_totient (L : List ℕ) (e : ℕ) (he : 0 < e)
    (hen : n ∣ e) (hdvd : ∀ d ∈ L, ¬ (n ∣ d)) (hlt : ∀ d ∈ L, d < e)
    (hbudget : (L.filter (fun d => Nat.Coprime d n)).length < Nat.totient n) :
    flankWorks n (e :: L) e = true := by
  have hn2 : 2 ≤ n := Fact.out
  obtain ⟨k, hk0, hkn, hgood⟩ := exists_goodK_totient L hdvd hbudget
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

/-- **The prime form is a special case.**  At a prime order every non-multiple of `n` is coprime
to it and `φ(n) = n − 1`, so the length hypothesis of `flankWorks_of_prime_dvd` gives the budget. -/
theorem budget_of_prime (hp : n.Prime) (L : List ℕ)
    (hlen : L.length + 1 < n) :
    (L.filter (fun d => Nat.Coprime d n)).length < Nat.totient n := by
  rw [Nat.totient_prime hp]
  have := List.length_filter_le (fun d => decide (Nat.Coprime d n)) L
  omega

end LRC.Resonance
