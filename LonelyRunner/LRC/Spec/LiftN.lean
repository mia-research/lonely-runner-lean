import LonelyRunner.LRC.Spec.ResonanceN

/-!
# The resonant flank at every order, and the lift

2026-09-24.  Two results, both at general `n`.

**1. The resonant flank without primality.**  `Resonance.flankWorks_of_prime_dvd` carried
`n.Prime`, used in one step: excluding `(d·k) mod n = 0` by Euclid.  Take the multiplier `k` from
the units of `ℤ/n` instead.  Then `(d·k) mod n = 0` is impossible because `n ∤ d`; and
`(d·k) mod n = n − 1` forces `gcd(d, n) = 1`, since `n − 1` is a unit, and for such `d` it fixes
`k`.  So each non-flank disparity coprime to `n` rules out exactly one unit and no other disparity
rules out any: fewer coprime non-flank disparities than `φ(n)` leaves a unit.
`flankWorks_of_resonant_flank`.  The prime version is recovered as a corollary.

**2. The lift.**  Write a whole-number difference set as `n·M ∪ X`.  A lonely opening of `M` at
flank `f`, index `j₀`, lifts to the flank `n·f` at the indices `j₀ + f·i`, `0 ≤ i < n`: every
multiple `n·m` reads `n·(m·(n j₀ + 1) mod n f)`, exactly as `m` did one scale down, and a disparity
`x` of `X` reads `n f·((q + x·i) mod n) + ρ`, with `q, ρ` fixed by `j₀`.  So `x` is clear once
`(q + x·i) mod n ∉ {0, n − 1}` (`flankWorks_lift`).  With one free disparity, `n ∤ x` and `n ≥ 3`,
some `i ∈ {0, 1, 2}` does it (`exists_lift_index_one`).

Hence the `M ≥ c − 1` end of the trichotomy is a reduction to one fewer disparity **at the same
order**: `n·M ∪ {x}` has a certificate exactly when `M` has one (`certificate_iff_of_one_free`),
and `n·M` exactly when `M` does (`certificate_iff_of_multiples`).  The reverse directions pass
through the reals: an instant `t` lonely for `n·M ∪ X` makes `n·t` lonely for `M`, and
Localisation (`Flanks.lonely_iff_exists_flank`) returns a flank of `M`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace LRC.Lift

open Flanks MomentIterationN LRC.SpecN LRC.FlankFinite LRC.Resonance

variable {n : ℕ} [Fact (2 ≤ n)]

/-! ## 1. the resonant flank, with the units as multipliers -/

/-- A unit multiplier never sends a disparity not divisible by `n` to `0`. -/
theorem mul_unit_mod_ne_zero {d k : ℕ} (hk : Nat.Coprime n k) (hd : ¬ n ∣ d) :
    (d * k) % n ≠ 0 := by
  intro h
  exact hd (hk.dvd_of_dvd_mul_right (Nat.dvd_of_mod_eq_zero h))

/-- **Reading `n − 1` forces coprimality**: `n − 1` is a unit, so any common factor of `d` and `n`
divides both `n − 1` and `n`. -/
theorem coprime_of_mul_mod_eq_pred {d k : ℕ} (h : (d * k) % n = n - 1) : Nat.Coprime d n := by
  have hn2 : 2 ≤ n := Fact.out
  have hg1 : Nat.gcd d n ∣ d * k := Dvd.dvd.mul_right (Nat.gcd_dvd_left d n) k
  have hg2 : Nat.gcd d n ∣ n := Nat.gcd_dvd_right d n
  have hsplit : d * k = n * (d * k / n) + (n - 1) := by
    rw [← h]; exact (Nat.div_add_mod _ _).symm
  have hg3 : Nat.gcd d n ∣ n - 1 := by
    rw [hsplit] at hg1
    exact (Nat.dvd_add_right (Dvd.dvd.mul_right hg2 _)).mp hg1
  have hg4 : Nat.gcd d n ∣ n - (n - 1) := Nat.dvd_sub hg2 hg3
  have h1 : n - (n - 1) = 1 := by omega
  rw [h1] at hg4
  exact Nat.dvd_one.mp hg4

/-- For `d` coprime to `n`, at most one `k < n` has `d·k ≡ n − 1`. -/
theorem mul_mod_inj_of_coprime {d k₁ k₂ : ℕ} (hd : Nat.Coprime n d) (h1 : k₁ < n) (h2 : k₂ < n)
    (h : (d * k₁) % n = (d * k₂) % n) : k₁ = k₂ := by
  have : k₁ % n = k₂ % n :=
    Nat.ModEq.cancel_left_of_coprime (by simpa [Nat.Coprime] using hd) h
  rwa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at this

/-- **The pigeonhole over the units.**  If fewer non-flank disparities are coprime to `n` than
there are units, some unit `k` keeps every `(d·k) mod n` off `0` and off `n − 1`.  No primality. -/
theorem exists_unit_goodK (L : List ℕ) (hL : ∀ d ∈ L, ¬ (n ∣ d))
    (hcount : (L.filter (fun d => Nat.Coprime d n)).length < Nat.totient n) :
    ∃ k, 0 < k ∧ k < n ∧ Nat.Coprime n k ∧ GoodK n L k := by
  classical
  have hn2 : 2 ≤ n := Fact.out
  by_contra hcon
  push Not at hcon
  set U : Finset ℕ := {a ∈ Finset.range n | n.Coprime a} with hU
  have hunit : ∀ k ∈ U, 0 < k ∧ k < n ∧ Nat.Coprime n k := by
    intro k hk
    obtain ⟨hkn, hcop⟩ := Finset.mem_filter.mp hk
    refine ⟨?_, Finset.mem_range.mp hkn, hcop⟩
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0; simp [Nat.Coprime] at hcop; omega
    · exact h0
  have hwit : ∀ k, ∃ d, k ∈ U → (d ∈ L.filter (fun d => Nat.Coprime d n) ∧ (d * k) % n = n - 1) := by
    intro k
    by_cases hk : k ∈ U
    · obtain ⟨hk0, hkn, hcop⟩ := hunit k hk
      have hbad := hcon k hk0 hkn hcop
      unfold GoodK at hbad
      push Not at hbad
      obtain ⟨d, hd, hcase⟩ := hbad
      have hpred : (d * k) % n = n - 1 := hcase (mul_unit_mod_ne_zero hcop (hL d hd))
      exact ⟨d, fun _ => ⟨List.mem_filter.mpr ⟨hd, by simpa using coprime_of_mul_mod_eq_pred hpred⟩, hpred⟩⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose f hf using hwit
  have hinj : Set.InjOn f U := by
    intro a ha b hb hab
    obtain ⟨hma, h1⟩ := hf a ha
    obtain ⟨hmb, h2⟩ := hf b hb
    rw [hab] at h1
    have hcop : Nat.Coprime (f b) n := by
      have := (List.mem_filter.mp hmb).2
      simpa using this
    exact mul_mod_inj_of_coprime hcop.symm (hunit a ha).2.1 (hunit b hb).2.1 (h1.trans h2.symm)
  have hmaps : ∀ k ∈ U, f k ∈ (L.filter (fun d => Nat.Coprime d n)).toFinset := by
    intro k hk
    exact List.mem_toFinset.mpr (hf k hk).1
  have hcard := Finset.card_le_card_of_injOn f hmaps hinj
  have hU' : U.card = Nat.totient n := (Nat.totient_eq_card_coprime n).symm
  have := le_trans hcard (List.toFinset_card_le _)
  omega

/-- **A good multiplier gives a lonely opening at a flank divisible by `n`**, at `a = k·e + 1`.
This is the body of `Resonance.flankWorks_of_prime_dvd`, which never used primality once `k`
was in hand. -/
theorem flankWorks_of_goodK (L : List ℕ) (e k : ℕ) (he : 0 < e) (hen : n ∣ e) (hkn : k < n)
    (hgood : GoodK n L k) (hlt : ∀ d ∈ L, d < e) :
    flankWorks n (e :: L) e = true := by
  have hn2 : 2 ≤ n := Fact.out
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
  · have hflank : d * (k * d + 1) = d + (n * d) * (k * E) := by
      have hd : n * E = d := hE.symm
      calc d * (k * d + 1) = d + d * (k * d) := by ring
        _ = d + (n * E) * (k * d) := by rw [hd]
        _ = d + (n * d) * (k * E) := by rw [← hd]; ring
    have hlt1 : d < n * d := by
      have := (Nat.mul_lt_mul_right he).mpr (show 1 < n by omega)
      simpa using this
    rw [hflank, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt1]
    exact ⟨le_refl d, Nat.le_mul_of_pos_left d (by omega)⟩
  · set q : ℕ := (d * k) % n with hq
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

/-- **The resonant flank, at every order.**  `n ∣ e`, `e` the largest disparity, no other
disparity divisible by `n`, and fewer of them coprime to `n` than `φ(n)`: the flank `e` hosts a
lonely opening.  No primality. -/
theorem flankWorks_of_resonant_flank (L : List ℕ) (e : ℕ) (he : 0 < e) (hen : n ∣ e)
    (hdvd : ∀ d ∈ L, ¬ (n ∣ d)) (hlt : ∀ d ∈ L, d < e)
    (hcount : (L.filter (fun d => Nat.Coprime d n)).length < Nat.totient n) :
    flankWorks n (e :: L) e = true := by
  obtain ⟨k, -, hkn, -, hgood⟩ := exists_unit_goodK L hdvd hcount
  exact flankWorks_of_goodK L e k he hen hkn hgood hlt

/-- **The prime version is the special case.**  At prime `n`, `φ(n) = n − 1`, and the hypothesis
`|L| + 1 < n` of `Resonance.flankWorks_of_prime_dvd` bounds the coprime count below it. -/
theorem flankWorks_of_prime_dvd' (hp : n.Prime) (L : List ℕ) (e : ℕ) (he : 0 < e)
    (hen : n ∣ e) (hdvd : ∀ d ∈ L, ¬ (n ∣ d)) (hlt : ∀ d ∈ L, d < e)
    (hlen : L.length + 1 < n) :
    flankWorks n (e :: L) e = true := by
  refine flankWorks_of_resonant_flank L e he hen hdvd hlt ?_
  rw [Nat.totient_prime hp]
  have := List.length_filter_le (fun d => Nat.Coprime d n) L
  omega

/-! ## 2. the lift -/

/-- **Multiples read as their quotients did, one scale down**, at every index of `j₀`'s class
mod `f`. -/
theorem lift_reading_multiple (m f j₀ i : ℕ) :
    (n * m * (n * (j₀ + f * i) + 1)) % (n * (n * f)) = n * ((m * (n * j₀ + 1)) % (n * f)) := by
  have h : n * m * (n * (j₀ + f * i) + 1) = n * (m * (n * j₀ + 1)) + n * (n * f) * (m * i) := by
    ring
  rw [h, Nat.add_mul_mod_self_left, Nat.mul_mod_mul_left]

/-- **A free disparity's reading along the class.**  With `r₀ = x·(n j₀ + 1) mod n²f`,
`q = r₀ div n f` and `ρ = r₀ mod n f`, the reading at the index `j₀ + f·i` is
`n f·((q + x·i) mod n) + ρ`. -/
theorem lift_reading_free (x f j₀ i : ℕ) (hf : 0 < f) :
    (x * (n * (j₀ + f * i) + 1)) % (n * (n * f))
      = n * f * (((x * (n * j₀ + 1)) % (n * (n * f)) / (n * f) + x * i) % n)
        + (x * (n * j₀ + 1)) % (n * (n * f)) % (n * f) := by
  have hn2 : 2 ≤ n := Fact.out
  have hn : 0 < n := by omega
  have hP : 0 < n * f := Nat.mul_pos hn hf
  generalize hA : x * (n * j₀ + 1) = A
  have hxa : x * (n * (j₀ + f * i) + 1) = A + n * f * (x * i) := by rw [← hA]; ring
  rw [hxa]
  generalize hr : A % (n * (n * f)) = r
  generalize hq : r / (n * f) = q
  generalize hρ : r % (n * f) = ρ
  generalize hQ : (q + x * i) % n = Q
  have h1 : A = n * (n * f) * (A / (n * (n * f))) + r := by rw [← hr]; exact (Nat.div_add_mod _ _).symm
  have h2 : r = n * f * q + ρ := by rw [← hq, ← hρ]; exact (Nat.div_add_mod _ _).symm
  have h3 : q + x * i = n * ((q + x * i) / n) + Q := by rw [← hQ]; exact (Nat.div_add_mod _ _).symm
  have hQlt : Q < n := by rw [← hQ]; exact Nat.mod_lt _ hn
  have hρlt : ρ < n * f := by rw [← hρ]; exact Nat.mod_lt _ hP
  have hsum : A + n * f * (x * i)
      = (n * f * Q + ρ) + n * (n * f) * (A / (n * (n * f)) + (q + x * i) / n) := by
    have e3 : n * f * (q + x * i) = n * f * (n * ((q + x * i) / n)) + n * f * Q := by
      rw [← mul_add, ← h3]
    calc A + n * f * (x * i) = n * (n * f) * (A / (n * (n * f))) + (n * f * q + ρ) + n * f * (x * i) := by
          rw [← h2, ← h1]
      _ = n * (n * f) * (A / (n * (n * f))) + ρ + n * f * (q + x * i) := by ring
      _ = n * (n * f) * (A / (n * (n * f))) + ρ + (n * f * (n * ((q + x * i) / n)) + n * f * Q) := by
          rw [e3]
      _ = (n * f * Q + ρ) + n * (n * f) * (A / (n * (n * f)) + (q + x * i) / n) := by ring
  rw [hsum, Nat.add_mul_mod_self_left]
  apply Nat.mod_eq_of_lt
  have : n * f * Q + n * f ≤ n * (n * f) := by
    have := Nat.mul_le_mul_left (n * f) (show Q + 1 ≤ n by omega)
    nlinarith
  omega

/-- The band at modulus `n·(n f)` from the residue position `Q ∉ {0, n − 1}`. -/
theorem lift_band_free {f Q ρ : ℕ} (hQlt : Q < n) (hρ : ρ < n * f) (h0 : Q ≠ 0) (h1 : Q ≠ n - 1) :
    n * f ≤ n * f * Q + ρ ∧ n * f * Q + ρ ≤ (n - 1) * (n * f) := by
  have hn2 : 2 ≤ n := Fact.out
  constructor
  · have : n * f * 1 ≤ n * f * Q := Nat.mul_le_mul_left _ (by omega)
    omega
  · have hQ2 : Q + 1 ≤ n - 1 := by omega
    have : n * f * (Q + 1) ≤ n * f * (n - 1) := Nat.mul_le_mul_left _ hQ2
    have hc : (n - 1) * (n * f) = n * f * (n - 1) := by ring
    rw [hc]
    nlinarith

/-- **The lift.**  A lonely opening `j₀` of `M` at the flank `f` lifts to the flank `n·f` of
`n·M ∪ X` at the index `j₀ + f·i`, as soon as the shift `i < n` keeps every free disparity's
residue position off `0` and off `n − 1`.  No hypothesis on `X` beyond that. -/
theorem flankWorks_lift (M X : List ℕ) (f j₀ : ℕ) (hf : 0 < f) (hj₀ : j₀ < f)
    (hM : ∀ m ∈ M, f ≤ (m * (n * j₀ + 1)) % (n * f) ∧ (m * (n * j₀ + 1)) % (n * f) ≤ (n - 1) * f)
    (i : ℕ) (hi : i < n)
    (hX : ∀ x ∈ X, ((x * (n * j₀ + 1)) % (n * (n * f)) / (n * f) + x * i) % n ≠ 0 ∧
                   ((x * (n * j₀ + 1)) % (n * (n * f)) / (n * f) + x * i) % n ≠ n - 1) :
    flankWorks n (M.map (fun m => n * m) ++ X) (n * f) = true := by
  have hn2 : 2 ≤ n := Fact.out
  have hn : 0 < n := by omega
  have hP : 0 < n * f := Nat.mul_pos hn hf
  have hjlt : j₀ + f * i < n * f := by
    have : f * (i + 1) ≤ f * n := Nat.mul_le_mul_left f (by omega)
    nlinarith
  unfold flankWorks
  rw [List.any_eq_true]
  refine ⟨j₀ + f * i, List.mem_range.mpr hjlt, ?_⟩
  rw [List.all_eq_true]
  intro d hd
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rcases List.mem_append.mp hd with hdM | hdX
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hdM
    rw [lift_reading_multiple]
    obtain ⟨hlo, hhi⟩ := hM m hm
    constructor
    · exact Nat.mul_le_mul_left n hlo
    · calc n * ((m * (n * j₀ + 1)) % (n * f)) ≤ n * ((n - 1) * f) := Nat.mul_le_mul_left n hhi
        _ = (n - 1) * (n * f) := by ring
  · rw [lift_reading_free d f j₀ i hf]
    exact lift_band_free (Nat.mod_lt _ hn) (Nat.mod_lt _ hP) (hX d hdX).1 (hX d hdX).2

/-- Residues below `3n`, reduced by hand. -/
theorem mod_of_lt_three_mul {a : ℕ} (h : a < 3 * n) :
    (a < n ∧ a % n = a) ∨ (n ≤ a ∧ a < 2 * n ∧ a % n = a - n) ∨ (2 * n ≤ a ∧ a % n = a - 2 * n) := by
  have hn2 : 2 ≤ n := Fact.out
  rcases lt_or_ge a n with h1 | h1
  · exact Or.inl ⟨h1, Nat.mod_eq_of_lt h1⟩
  rcases lt_or_ge a (2 * n) with h2 | h2
  · refine Or.inr (Or.inl ⟨h1, h2, ?_⟩)
    rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]
  · refine Or.inr (Or.inr ⟨h2, ?_⟩)
    rw [Nat.mod_eq_sub_mod (by omega : n ≤ a), Nat.mod_eq_sub_mod (by omega : n ≤ a - n),
      Nat.mod_eq_of_lt (by omega)]
    omega

/-- **One free disparity always has a shift**, at `n ≥ 3`: among `i = 0, 1, 2` the positions
`q, q + x, q + 2x` (mod `n`) are not all in `{0, n − 1}`, because `n ∤ x` makes consecutive
positions distinct, which forces `x ≡ ±1`, and then the third position is `1` or `n − 2`. -/
theorem exists_lift_index_one (hn3 : 3 ≤ n) (q x : ℕ) (hx : ¬ n ∣ x) :
    ∃ i, i < n ∧ (q + x * i) % n ≠ 0 ∧ (q + x * i) % n ≠ n - 1 := by
  have hn2 : 2 ≤ n := Fact.out
  have hn : 0 < n := by omega
  set r := q % n with hr
  set u := x % n with hu
  have hrlt : r < n := Nat.mod_lt _ hn
  have hult : u < n := Nat.mod_lt _ hn
  have hu0 : u ≠ 0 := fun h => hx (Nat.dvd_of_mod_eq_zero h)
  have hred : ∀ i, (q + x * i) % n = (r + u * i) % n := by
    intro i
    have hq := Nat.div_add_mod q n
    have hxd := Nat.div_add_mod x n
    have : q + x * i = (r + u * i) + n * (q / n + (x / n) * i) := by
      calc q + x * i = (n * (q / n) + r) + (n * (x / n) + u) * i := by rw [hq, hxd]
        _ = (r + u * i) + n * (q / n + (x / n) * i) := by ring
    rw [this, Nat.add_mul_mod_self_left]
  have c0 := mod_of_lt_three_mul (n := n) (a := r + u * 0) (by omega)
  have c1 := mod_of_lt_three_mul (n := n) (a := r + u * 1) (by omega)
  have c2 := mod_of_lt_three_mul (n := n) (a := r + u * 2) (by omega)
  by_cases h0 : (r + u * 0) % n ≠ 0 ∧ (r + u * 0) % n ≠ n - 1
  · exact ⟨0, hn, by rw [hred]; exact h0⟩
  by_cases h1 : (r + u * 1) % n ≠ 0 ∧ (r + u * 1) % n ≠ n - 1
  · exact ⟨1, by omega, by rw [hred]; exact h1⟩
  refine ⟨2, by omega, ?_⟩
  rw [hred]
  simp only [mul_zero, add_zero, mul_one] at h0 h1 c0 c1 c2 ⊢
  omega

/-- **The `M = c − 1` step.**  One disparity `x` not divisible by `n`, the rest `n·M`: a flank of
`M` lifts to a flank of the whole set, at `n ≥ 3`. -/
theorem flankWorks_lift_one (hn3 : 3 ≤ n) (M : List ℕ) (x f : ℕ) (hf : 0 < f) (hx : ¬ n ∣ x)
    (hM : flankWorks n M f = true) :
    flankWorks n (M.map (fun m => n * m) ++ [x]) (n * f) = true := by
  unfold flankWorks at hM
  rw [List.any_eq_true] at hM
  obtain ⟨j₀, hj₀mem, hj₀⟩ := hM
  rw [List.all_eq_true] at hj₀
  obtain ⟨i, hi, hgood⟩ :=
    exists_lift_index_one hn3 ((x * (n * j₀ + 1)) % (n * (n * f)) / (n * f)) x hx
  refine flankWorks_lift M [x] f j₀ hf (List.mem_range.mp hj₀mem) ?_ i hi ?_
  · intro m hm
    have := hj₀ m hm
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this
  · intro y hy
    rw [List.mem_singleton] at hy
    subst hy
    exact hgood

/-- **Descent through the reals.**  A certificate of `n·M ∪ X` gives one of `M`: if `t` is
lonely for the whole set then `n·t` is lonely for `M`, and Localisation hands back a flank. -/
theorem certificate_of_lift (M X : List ℕ) (hMpos : ∀ m ∈ M, 0 < m) (hMne : M ≠ [])
    (e : ℕ) (he : 0 < e) (h : flankWorks n (M.map (fun m => n * m) ++ X) e = true) :
    ∃ f ∈ M, flankWorks n M f = true := by
  classical
  have hn2 : 2 ≤ n := Fact.out
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨j, hj⟩ := lonely_of_flankWorks _ e he h
  set t := flankOpening n (e : ℝ) j with ht
  have htpos : 0 < t := flankOpening_pos (by exact_mod_cast he) j
  set ds : Finset ℝ := M.toFinset.image (fun m : ℕ => (m : ℝ)) with hds
  have hpos : ∀ d ∈ ds, 0 < d := by
    intro d hd
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hd
    exact_mod_cast hMpos m (List.mem_toFinset.mp hm)
  have hne : ds.Nonempty := by
    obtain ⟨m, hm⟩ := List.exists_mem_of_ne_nil M hMne
    exact ⟨(m : ℝ), Finset.mem_image.mpr ⟨m, List.mem_toFinset.mpr hm, rfl⟩⟩
  have hlon : Lonely n ds ((n : ℝ) * t) := by
    intro d hd
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hd
    have hmem : n * m ∈ M.map (fun m => n * m) ++ X :=
      List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨m, List.mem_toFinset.mp hm, rfl⟩))
    have := hj (n * m) hmem
    have hre : ((n * m : ℕ) : ℝ) * t = (m : ℝ) * ((n : ℝ) * t) := by push_cast; ring
    rw [hre] at this
    exact this
  obtain ⟨e', he', k, hk⟩ :=
    (lonely_iff_exists_flank hpos hne).mp ⟨(n : ℝ) * t, mul_pos hn0 htpos, hlon⟩
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he'
  have hfM : f ∈ M := List.mem_toFinset.mp hf
  refine ⟨f, hfM, flankWorks_of_lonely M f (hMpos f hfM) k ?_⟩
  intro d hd
  exact hk (d : ℝ) (Finset.mem_image.mpr ⟨d, List.mem_toFinset.mpr hd, rfl⟩)

/-- **The `M = c − 1` end, as a reduction.**  At `n ≥ 3`, with one disparity `x` not divisible by
`n` and the rest `n·M`: the whole set has a certificate exactly when `M` does.  The threshold stays
`1/n`, so this is the same obligation with one fewer disparity. -/
theorem certificate_iff_of_one_free (hn3 : 3 ≤ n) (M : List ℕ) (hMpos : ∀ m ∈ M, 0 < m)
    (hMne : M ≠ []) (x : ℕ) (hx0 : 0 < x) (hx : ¬ n ∣ x) :
    (∃ e ∈ M.map (fun m => n * m) ++ [x], flankWorks n (M.map (fun m => n * m) ++ [x]) e = true) ↔
      ∃ f ∈ M, flankWorks n M f = true := by
  have hn2 : 2 ≤ n := Fact.out
  constructor
  · rintro ⟨e, he, h⟩
    have he0 : 0 < e := by
      rcases List.mem_append.mp he with hm | hm
      · obtain ⟨m, hm', rfl⟩ := List.mem_map.mp hm
        exact Nat.mul_pos (by omega) (hMpos m hm')
      · rw [List.mem_singleton] at hm; omega
    exact certificate_of_lift M [x] hMpos hMne e he0 h
  · rintro ⟨f, hf, h⟩
    exact ⟨n * f, List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨f, hf, rfl⟩)),
      flankWorks_lift_one hn3 M x f (hMpos f hf) hx h⟩

/-- **The `M = c` end.**  Every disparity a multiple of `n`: the set has a certificate exactly when
its quotient does.  (The lift with `X` empty, `i = 0`.) -/
theorem certificate_iff_of_multiples (M : List ℕ) (hMpos : ∀ m ∈ M, 0 < m) (hMne : M ≠ []) :
    (∃ e ∈ M.map (fun m => n * m), flankWorks n (M.map (fun m => n * m)) e = true) ↔
      ∃ f ∈ M, flankWorks n M f = true := by
  have hn2 : 2 ≤ n := Fact.out
  constructor
  · rintro ⟨e, he, h⟩
    have he0 : 0 < e := by
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp he
      exact Nat.mul_pos (by omega) (hMpos m hm)
    exact certificate_of_lift M [] hMpos hMne e he0 (by simpa using h)
  · rintro ⟨f, hf, h⟩
    refine ⟨n * f, List.mem_map.mpr ⟨f, hf, rfl⟩, ?_⟩
    unfold flankWorks at h
    rw [List.any_eq_true] at h
    obtain ⟨j₀, hj₀mem, hj₀⟩ := h
    rw [List.all_eq_true] at hj₀
    have := flankWorks_lift (n := n) M [] f j₀ (hMpos f hf) (List.mem_range.mp hj₀mem)
      (fun m hm => by
        have := hj₀ m hm
        simp only [Bool.and_eq_true, decide_eq_true_eq] at this
        exact this) 0 (by omega) (by simp)
    simpa using this

end LRC.Lift
