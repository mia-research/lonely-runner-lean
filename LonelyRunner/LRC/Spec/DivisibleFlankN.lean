import LonelyRunner.LRC.Spec.ShiftedTotientN

/-!
# The divisible flank without the largest hypothesis

2026-09-24.  `flankWorks_of_dvd_totient` settles a flank `e` divisible by `n` when `e` is the
largest disparity.  This file drops that hypothesis.

At the opening `a = k·e + 1` (`k < n`, so `a ≡ 1 mod n` and `a < n·e`), write a disparity as
`d = q·e + r` with `q = ⌊d/e⌋`, `r = d mod e`.

* If `n ∣ d`, the reading is `d mod n·e`, whatever `k` is: the shift does not move it.
* If `n ∤ d`, then `r ≥ 1` and the reading is `e·((d·k + q) mod n) + r`, which is in the band
  `[e, (n−1)e]` exactly when `(d·k + q) mod n ∉ {0, n − 1}`.

Each congruence `d·k + q ≡ c (mod n)` has at most `gcd(d, n)` solutions below `n`
(`card_congr_le`), and when `gcd(d, n) ≥ 2` the two residues `0` and `n − 1` cannot both be hit.
So `d` forbids at most `max 2 (gcd d n)` of the `n` shifts (`card_forbidden_le`) — the same cost as
the descent.  If the costs of the non-multiples add up to less than `n`, and every other multiple
of `n` already reads in the band, some shift is free and the flank `e` hosts a lonely opening
(`flankWorks_of_dvd_budget`).  A pigeonhole used as a tool.

Everything here is proved; no `sorry`, no `native_decide`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace LRC.Resonance

open Flanks MomentIterationN LRC.SpecN LRC.FlankFinite

variable {n : ℕ} [Fact (2 ≤ n)]

/-- **One congruence has at most `gcd d n` solutions below `n`.**  Two solutions `a, b` give
`n ∣ d·(b − a)`, so `n / gcd(d, n)` divides `b − a`, and the solutions below `n` sit in one
residue class mod `n / gcd(d, n)`. -/
theorem card_congr_le (d q c : ℕ) :
    ((Finset.range n).filter (fun k => (d * k + q) % n = c)).card ≤ Nat.gcd d n := by
  classical
  have hn2 : 2 ≤ n := Fact.out
  have hn : 0 < n := by omega
  set S := (Finset.range n).filter (fun k => (d * k + q) % n = c) with hS
  set g := Nat.gcd d n with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right d hn
  set m := n / g with hm
  have hmg : n = m * g := (Nat.div_mul_cancel (Nat.gcd_dvd_right d n)).symm
  have hdg : d = (d / g) * g := (Nat.div_mul_cancel (Nat.gcd_dvd_left d n)).symm
  have hcop : Nat.Coprime (d / g) m := Nat.coprime_div_gcd_div_gcd hg0
  have hlt : ∀ k ∈ S, k < n := fun k hk => Finset.mem_range.mp (Finset.mem_filter.mp hk).1
  have hmod : ∀ a ∈ S, ∀ b ∈ S, a % m = b % m := by
    intro a ha b hb
    have h1 := (Finset.mem_filter.mp ha).2
    have h2 := (Finset.mem_filter.mp hb).2
    have hab : d * a + q ≡ d * b + q [MOD n] := h1.trans h2.symm
    have hab' : d * a ≡ d * b [MOD n] := Nat.ModEq.add_right_cancel' q hab
    have hdvd : (n : ℤ) ∣ (d : ℤ) * ((b : ℤ) - a) := by
      have := (Nat.modEq_iff_dvd.mp hab')
      push_cast at this
      rw [mul_sub]; exact this
    have hdvd' : ((g : ℤ) * m) ∣ (g : ℤ) * ((d / g : ℕ) * ((b : ℤ) - a)) := by
      have e1 : (n : ℤ) = (g : ℤ) * m := by rw [hmg]; push_cast; ring
      have e2 : (d : ℤ) * ((b : ℤ) - a) = (g : ℤ) * ((d / g : ℕ) * ((b : ℤ) - a)) := by
        conv_lhs => rw [hdg]
        push_cast; ring
      rw [← e1, ← e2]; exact hdvd
    have hg0' : (g : ℤ) ≠ 0 := by exact_mod_cast hg0.ne'
    have hm1 : (m : ℤ) ∣ (d / g : ℕ) * ((b : ℤ) - a) := Int.dvd_of_mul_dvd_mul_left hg0' hdvd'
    have hic : IsCoprime (m : ℤ) ((d / g : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop.symm
    have hm2 : (m : ℤ) ∣ ((b : ℤ) - a) := hic.dvd_of_dvd_mul_left hm1
    have hzm : (a : ℤ) % m = (b : ℤ) % m := Int.modEq_iff_dvd.mpr hm2
    exact_mod_cast hzm
  have hinj : Set.InjOn (fun k => k / m) (S : Set ℕ) := by
    intro a ha b hb hab
    have hr := hmod a ha b hb
    simp only at hab
    rw [← Nat.div_add_mod a m, ← Nat.div_add_mod b m, hab, hr]
  have hmaps : ∀ k ∈ S, k / m ∈ Finset.range g := by
    intro k hk
    rw [Finset.mem_range]
    have hk := hlt k hk
    rw [hmg] at hk
    exact Nat.div_lt_of_lt_mul hk
  have hc := Finset.card_le_card_of_injOn (fun k => k / m) hmaps hinj
  rwa [Finset.card_range] at hc

/-- **A non-multiple forbids at most `max 2 (gcd d n)` of the `n` shifts.** -/
theorem card_forbidden_le (d q : ℕ) :
    ((Finset.range n).filter
        (fun k => (d * k + q) % n = 0 ∨ (d * k + q) % n = n - 1)).card ≤ max 2 (Nat.gcd d n) := by
  classical
  have hn2 : 2 ≤ n := Fact.out
  set A := (Finset.range n).filter (fun k => (d * k + q) % n = 0) with hA
  set B := (Finset.range n).filter (fun k => (d * k + q) % n = n - 1) with hB
  have hsplit : (Finset.range n).filter
      (fun k => (d * k + q) % n = 0 ∨ (d * k + q) % n = n - 1) = A ∪ B := by
    rw [hA, hB, Finset.filter_or]
  rw [hsplit]
  have hcA : A.card ≤ Nat.gcd d n := card_congr_le d q 0
  have hcB : B.card ≤ Nat.gcd d n := card_congr_le d q (n - 1)
  have hu := Finset.card_union_le A B
  rcases Nat.lt_or_ge (Nat.gcd d n) 2 with hg1 | hg2
  · omega
  · -- with `gcd(d, n) ≥ 2`, the residues `0` and `n − 1` cannot both be hit
    have hdisj : A = ∅ ∨ B = ∅ := by
      by_contra hne
      push Not at hne
      obtain ⟨a, ha⟩ := hne.1
      obtain ⟨b, hb⟩ := hne.2
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      have hna : n ∣ d * a + q := Nat.dvd_of_mod_eq_zero ha'
      have hnb : n ∣ d * b + q + 1 := by
        apply Nat.dvd_of_mod_eq_zero
        rw [Nat.add_mod, hb', Nat.mod_eq_of_lt (show 1 < n by omega),
          Nat.sub_add_cancel (by omega), Nat.mod_self]
      have hgn : Nat.gcd d n ∣ n := Nat.gcd_dvd_right d n
      have hgd : Nat.gcd d n ∣ d := Nat.gcd_dvd_left d n
      have hq : Nat.gcd d n ∣ q :=
        (Nat.dvd_add_right (Dvd.dvd.mul_right hgd a)).mp (hgn.trans hna)
      have hq1 : Nat.gcd d n ∣ q + 1 := by
        have h := hgn.trans hnb
        rw [add_assoc] at h
        exact (Nat.dvd_add_right (Dvd.dvd.mul_right hgd b)).mp h
      have h1 : Nat.gcd d n ∣ 1 := (Nat.dvd_add_right hq).mp hq1
      have := Nat.eq_one_of_dvd_one h1
      omega
    rcases hdisj with h | h
    · rw [h, Finset.empty_union]; exact le_trans hcB (le_max_right _ _)
    · rw [h, Finset.union_empty]; exact le_trans hcA (le_max_right _ _)

/-- **The divisible flank, with no hypothesis on its size.**  Let `n ∣ e`.  Suppose every other
multiple of `n` already reads in the band at the flank's opening `j = 0`, and the disparities not
divisible by `n` have total cost `∑ max 2 (gcd d n)` below `n`.  Then the flank `e` hosts a lonely
opening, at `a = k·e + 1` for some `k < n`. -/
theorem flankWorks_of_dvd_budget (L : List ℕ) (e : ℕ) (he : 0 < e) (hen : n ∣ e)
    (hmult : ∀ d ∈ L, n ∣ d → e ≤ d % (n * e) ∧ d % (n * e) ≤ (n - 1) * e)
    (hcost : ∑ d ∈ L.toFinset.filter (fun d => ¬ n ∣ d), max 2 (Nat.gcd d n) < n) :
    flankWorks n (e :: L) e = true := by
  classical
  have hn2 : 2 ≤ n := Fact.out
  set N := L.toFinset.filter (fun d => ¬ n ∣ d) with hN
  set F : ℕ → Finset ℕ := fun d => (Finset.range n).filter
    (fun k => (d * k + d / e) % n = 0 ∨ (d * k + d / e) % n = n - 1) with hF
  have hcard : (N.biUnion F).card < (Finset.range n).card := by
    rw [Finset.card_range]
    calc (N.biUnion F).card ≤ ∑ d ∈ N, (F d).card := Finset.card_biUnion_le
      _ ≤ ∑ d ∈ N, max 2 (Nat.gcd d n) :=
        Finset.sum_le_sum fun d _ => card_forbidden_le d (d / e)
      _ < n := hcost
  obtain ⟨k, hk, hkU⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hkn : k < n := Finset.mem_range.mp hk
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
  · -- the flank itself reads `e`
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
  · by_cases hnd : n ∣ d
    · -- a multiple of `n`: the shift does not move it
      obtain ⟨m, hm⟩ := hnd
      have hsplit : d * (k * e + 1) = d + (n * e) * (m * k) := by rw [hm]; ring
      rw [hsplit, Nat.add_mul_mod_self_left]
      exact hmult d hdL ⟨m, hm⟩
    · -- a non-multiple: the reading is `e·((d·k + q) mod n) + r`
      set q : ℕ := d / e with hq
      set r : ℕ := d % e with hr
      have hdqr : e * q + r = d := Nat.div_add_mod d e
      have hr0 : r ≠ 0 := by
        intro h0
        apply hnd
        have : e ∣ d := Nat.dvd_of_mod_eq_zero h0
        exact (show n ∣ e from ⟨E, hE⟩).trans this
      have hrlt : r < e := Nat.mod_lt d he
      set c : ℕ := (d * k + q) % n with hc
      have hkF : k ∉ F d := by
        intro h
        exact hkU (Finset.mem_biUnion.mpr ⟨d, Finset.mem_filter.mpr
          ⟨List.mem_toFinset.mpr hdL, hnd⟩, h⟩)
      have hc0 : c ≠ 0 := fun h => hkF (Finset.mem_filter.mpr ⟨hk, Or.inl h⟩)
      have hc1 : c ≠ n - 1 := fun h => hkF (Finset.mem_filter.mpr ⟨hk, Or.inr h⟩)
      have hclt : c < n := Nat.mod_lt _ (by omega)
      have hsplit : d * (k * e + 1) = (e * c + r) + (n * e) * ((d * k + q) / n) := by
        have h := Nat.div_add_mod (d * k + q) n
        calc d * (k * e + 1) = e * (d * k) + d := by ring
          _ = e * (d * k) + (e * q + r) := by rw [hdqr]
          _ = e * (d * k + q) + r := by ring
          _ = e * (n * ((d * k + q) / n) + c) + r := by rw [hc, h]
          _ = (e * c + r) + (n * e) * ((d * k + q) / n) := by ring
      rw [hsplit, Nat.add_mul_mod_self_left]
      have hub : e * c + r < n * e := by nlinarith
      rw [Nat.mod_eq_of_lt hub]
      constructor
      · nlinarith [Nat.one_le_iff_ne_zero.mpr hc0]
      · have hcle : c ≤ n - 2 := by omega
        have h1 : e * c ≤ e * (n - 2) := Nat.mul_le_mul_left e hcle
        have hne : e * (n - 2) + e = (n - 1) * e := by
          have hstep : n - 1 = (n - 2) + 1 := by omega
          rw [hstep, Nat.succ_mul, mul_comm]
        omega

end LRC.Resonance
