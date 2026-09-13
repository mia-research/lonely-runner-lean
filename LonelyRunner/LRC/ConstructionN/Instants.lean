import LonelyRunner.LRC.ConstructionN.Integrality

/-!
# The instants of global isolation, at general `n`

**RING-FENCE.** This module is part of the general-`n` line (`LRC/ConstructionN/`).
It is NOT part of the `n = 8` paper's artefact (`LRC/Construction8/`), which is frozen.

## What this module is for

The manuscript's part 2(b) — that a configuration in global isolation is in it at exactly
the `φ(n)` instants `p/n` with `gcd(p, n) = 1` — is the framework's **sole external
dependency**, cited rather than re-derived.  This module derives it at general `n` from the
framework's own objects: the separation criterion, the integrality of the displacements, and
the spine test that are already proved here.

The chain is:

* `dvd_of_forall_dvd_mul` — the denominator step.  Primitivity of the speed set is exactly
  what makes it work, and this is where it is used.
* `spine_iff` — at `t = p/n`, pairwise separation is non-divisibility.  Both directions come
  from the spine test already in `LemmaPass`.
* `spine_iff_residues` — with `p` coprime to `n`, that is distinctness of the residues.
* `break_of_not_coprime` — the converse half.  When `gcd(p, n) > 1` the residue map is no
  longer a permutation, and some pair collides, so isolation fails.
* `isolation_iff_coprime` — the dichotomy: isolation at `p/n` **iff** `gcd(n, p) = 1`.
* `card_coprime_eq_totient` — and there are `φ(n)` such `p`.

That much is the dichotomy **on the grid**.  The forward half — that no other instant
can work at all — is the rest:

* `int_of_forall_int_mul` — Bézout.  If `e i * y` is an integer for every `i`, so is
  `gcd(e) * y`.  No rationality of `y` is needed anywhere, which is what makes the step
  short.
* `instants_on_grid` — isolation at **any real** `t` forces `n * t` to be an integer.
  Primitivity is what closes it: without `gcd(e) = 1` the conclusion is false.
* `coprime_of_isolation` — and that integer is coprime to `n`.
* `isolation_forces_coprime_grid` — the two together: global isolation at a real `t`
  happens only at `t = p/n` with `gcd(n, p) = 1`.

`isolation_forces_coprime_grid` with `isolation_iff_coprime` and `card_coprime_eq_totient`
is part 2(b).  **Part 7 is not stated here and is not approached by
any of this.**

## What is NOT claimed

Nothing here bears on whether LRC holds at any order.  This says where global isolation can
occur once it occurs, not that it occurs.
-/

open Finset

namespace ConstructionN

/-- **The denominator step.**  If `q` divides `n * e j` for every `j` and the `e j` have gcd
`1`, then `q ∣ n`.  Primitivity of the speed set is load-bearing here: drop it and the
conclusion fails. -/
theorem dvd_of_forall_dvd_mul {ι : Type*} [Fintype ι] [Nonempty ι] (q n : ℕ) (e : ι → ℕ)
    (hg : (univ : Finset ι).gcd e = 1) (h : ∀ j, q ∣ n * e j) : q ∣ n := by
  have hd : q ∣ (univ : Finset ι).gcd (fun j => n * e j) := Finset.dvd_gcd (fun j _ => h j)
  rw [Finset.gcd_mul_left, hg, mul_one] at hd
  simpa using hd

/-- At `t = p/n`, pairwise separation is exactly non-divisibility. -/
theorem spine_iff {n : ℕ} (hn : 0 < n) (e : Fin n → ℤ) (p : ℤ) :
    (∀ a b : Fin n, a ≠ b → (n : ℝ)⁻¹ ≤ circDist (((e a - e b) * p : ℤ) / (n : ℝ)))
      ↔ (∀ a b : Fin n, a ≠ b → ¬ ((n : ℤ) ∣ (e a - e b) * p)) := by
  constructor
  · intro h a b hab
    exact not_dvd_of_sep hn (h a b hab)
  · intro h a b hab
    exact circDist_int_div hn (h a b hab)

/-- With `p` coprime to `n`, non-divisibility is distinctness of the residues. -/
theorem spine_iff_residues {n : ℕ} (e : Fin n → ℤ) (p : ℤ)
    (hcop : IsCoprime (n : ℤ) p) :
    (∀ a b : Fin n, a ≠ b → ¬ ((n : ℤ) ∣ (e a - e b) * p))
      ↔ (∀ a b : Fin n, a ≠ b → ¬ ((n : ℤ) ∣ (e a - e b))) := by
  constructor
  · intro h a b hab hdvd
    exact h a b hab (hdvd.mul_right p)
  · intro h a b hab hdvd
    exact h a b hab (hcop.dvd_of_dvd_mul_right hdvd)

/-- **The converse half.**  Distinct residues make the residue map a permutation of `ZMod n`.
When `gcd(n, p) > 1` multiplication by `p` is no longer injective there, so some pair
collides and isolation fails. -/
theorem break_of_not_coprime {n : ℕ} (hn : 0 < n) (e : Fin n → ℤ)
    (hdist : ∀ a b : Fin n, a ≠ b → ¬ ((n : ℤ) ∣ (e a - e b)))
    (p : ℤ) (hg : Nat.gcd n p.natAbs ≠ 1) :
    ∃ a b : Fin n, a ≠ b ∧ (n : ℤ) ∣ (e a - e b) * p := by
  set g := Nat.gcd n p.natAbs with hgdef
  have hg0 : g ≠ 0 := by
    simp only [hgdef, Ne, Nat.gcd_eq_zero_iff, not_and]
    intro h; omega
  have hg1 : 1 < g := by omega
  have hgn : g ∣ n := Nat.gcd_dvd_left _ _
  obtain ⟨d, hd⟩ := hgn
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h; simp at hd; omega
    · exact h
  have hdn : d < n := by
    have h : d < g * d := by nlinarith
    omega
  have hinj : Function.Injective (fun j : Fin n => ((e j : ZMod n))) := by
    intro a b hab
    by_contra hne
    refine hdist a b hne ?_
    have hm : e a ≡ e b [ZMOD (n : ℤ)] := (ZMod.intCast_eq_intCast_iff _ _ _).mp hab
    simpa using (Int.ModEq.dvd hm.symm)
  haveI : NeZero n := ⟨hn.ne'⟩
  have hcard : Fintype.card (Fin n) = Fintype.card (ZMod n) := by simp
  have hsurj : Function.Surjective (fun j : Fin n => ((e j : ZMod n))) :=
    (Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj, hcard⟩ |>.2
  set b : Fin n := ⟨0, hn⟩
  obtain ⟨a, ha⟩ := hsurj ((e b : ZMod n) + (d : ZMod n))
  have hdne : ((d : ZMod n)) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have := Nat.le_of_dvd hd0 hdvd
    omega
  have hab : a ≠ b := by
    intro h; rw [h] at ha; simp at ha; exact hdne ha
  refine ⟨a, b, hab, ?_⟩
  have h1 : (n : ℤ) ∣ (e a - e b - (d : ℤ)) := by
    have : ((e a - e b - (d : ℤ) : ℤ) : ZMod n) = 0 := by
      push_cast
      simp only [ha]
      ring
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
  have h2 : (n : ℤ) ∣ (d : ℤ) * p := by
    have hgp : (g : ℤ) ∣ p := Int.dvd_natAbs.mp (Int.ofNat_dvd.mpr (Nat.gcd_dvd_right n p.natAbs))
    obtain ⟨k, hk⟩ := hgp
    refine ⟨k, ?_⟩
    rw [hk, hd]
    push_cast
    ring
  have hsplit : (e a - e b) * p = (e a - e b - (d : ℤ)) * p + (d : ℤ) * p := by ring
  rw [hsplit]
  exact dvd_add (h1.mul_right p) h2

/-- **The dichotomy, general `n`.**  For a configuration whose residues are distinct, global
isolation holds at `t = p/n` **exactly when** `gcd(n, p) = 1`.  This is part 2(b)'s content,
derived here from the framework's own objects rather than cited. -/
theorem isolation_iff_coprime {n : ℕ} (hn : 0 < n) (e : Fin n → ℤ)
    (hdist : ∀ a b : Fin n, a ≠ b → ¬ ((n : ℤ) ∣ (e a - e b))) (p : ℕ) :
    (∀ a b : Fin n, a ≠ b →
        (n : ℝ)⁻¹ ≤ circDist (((e a - e b) * (p : ℤ) : ℤ) / (n : ℝ)))
      ↔ Nat.Coprime n p := by
  rw [spine_iff hn]
  constructor
  · intro h
    by_contra hcop
    have hg : Nat.gcd n ((p : ℤ)).natAbs ≠ 1 := by simpa [Nat.Coprime] using hcop
    obtain ⟨a, b, hab, hdvd⟩ := break_of_not_coprime hn e hdist (p : ℤ) hg
    exact h a b hab hdvd
  · intro hcop
    have hz : IsCoprime (n : ℤ) (p : ℤ) := by
      rw [Int.isCoprime_iff_gcd_eq_one]
      simpa [Int.gcd] using hcop
    exact (spine_iff_residues e (p : ℤ) hz).mpr hdist

/-- **And there are `φ(n)` of them.**  Euler's totient counts the instants. -/
theorem card_coprime_eq_totient (n : ℕ) :
    ((range n).filter (fun p => Nat.Coprime n p)).card = Nat.totient n := rfl

/-! ## The forward half: no instant off the grid -/

/-- **Bézout.**  If `e i * y` is an integer for every `i` in `s`, then so is `(s.gcd e) * y`.
`y` is an arbitrary real — nothing here needs it to be rational, which is what keeps the
step to one induction. -/
theorem int_of_forall_int_mul {ι : Type*} [DecidableEq ι] (s : Finset ι) (e : ι → ℤ) (y : ℝ)
    (h : ∀ i ∈ s, ∃ z : ℤ, (e i : ℝ) * y = z) :
    ∃ z : ℤ, ((s.gcd e : ℤ) : ℝ) * y = z := by
  classical
  induction s using Finset.induction with
  | empty => exact ⟨0, by simp⟩
  | insert a s ha ih =>
      obtain ⟨za, hza⟩ := h a (mem_insert_self a s)
      obtain ⟨zs, hzs⟩ := ih (fun i hi => h i (mem_insert_of_mem hi))
      refine ⟨Int.gcdA (e a) (s.gcd e) * za + Int.gcdB (e a) (s.gcd e) * zs, ?_⟩
      rw [Finset.gcd_insert]
      have hb : (GCDMonoid.gcd (e a) (s.gcd e)) =
          e a * Int.gcdA (e a) (s.gcd e) + (s.gcd e) * Int.gcdB (e a) (s.gcd e) := by
        have := Int.gcd_eq_gcd_ab (e a) (s.gcd e)
        simpa [Int.gcd_eq_natAbs, Int.coe_gcd] using this
      rw [hb]
      push_cast
      rw [add_mul]
      rw [show ((e a : ℝ) * Int.gcdA (e a) (s.gcd e)) * y
            = (Int.gcdA (e a) (s.gcd e) : ℝ) * ((e a : ℝ) * y) by ring,
          show (((s.gcd e : ℤ) : ℝ) * Int.gcdB (e a) (s.gcd e)) * y
            = (Int.gcdB (e a) (s.gcd e) : ℝ) * (((s.gcd e : ℤ) : ℝ) * y) by ring,
          hza, hzs]

/-- **Isolation at any real `t` puts `n * t` on the integers.**  The subject sits at
relative speed `0` in its own frame; `hprim` is primitivity of the speed set, and it is
load-bearing — drop it and the conclusion is false. -/
theorem instants_on_grid {n : ℕ} (hn : 1 < n) (e : Fin n → ℤ)
    (hprim : (univ : Finset (Fin n)).gcd e = 1)
    (j₀ : Fin n) (he : e j₀ = 0) (t : ℝ)
    (hiso : ∀ a b : Fin n, a ≠ b → (n : ℝ)⁻¹ ≤ circDist ((e a - e b : ℤ) * t)) :
    ∃ z : ℤ, (n : ℝ) * t = z := by
  classical
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  set x : Fin n → ℝ := fun j => (n : ℝ) * (e j : ℝ) * t with hx
  have hx0 : x j₀ = 0 := by simp [hx, he]
  have hsep : ∀ a b : Fin n, a ≠ b → (n : ℝ)⁻¹ ≤ circDist ((x a - x b) / n) := by
    intro a b hab
    have : (x a - x b) / (n : ℝ) = ((e a - e b : ℤ) : ℝ) * t := by
      simp only [hx]; push_cast; field_simp
    rw [this]; exact hiso a b hab
  have hall : ∀ j : Fin n, ∃ z : ℤ, (e j : ℝ) * ((n : ℝ) * t) = z := by
    intro j
    obtain ⟨z, hz⟩ := int_of_pairwise_sep hn x j₀ hx0 hsep j
    exact ⟨z, by rw [← hz]; simp [hx]; ring⟩
  obtain ⟨z, hz⟩ := int_of_forall_int_mul (univ : Finset (Fin n)) e ((n : ℝ) * t)
    (fun i _ => hall i)
  rw [hprim] at hz
  exact ⟨z, by simpa using hz⟩

/-- Once `n * t = p`, isolation forces `p` coprime to `n`.  Distinctness of the residues is
not a hypothesis here: isolation already supplies it. -/
theorem coprime_of_isolation {n : ℕ} (hn : 1 < n) (e : Fin n → ℤ) (t : ℝ) (p : ℤ)
    (hp : (n : ℝ) * t = p)
    (hiso : ∀ a b : Fin n, a ≠ b → (n : ℝ)⁻¹ ≤ circDist ((e a - e b : ℤ) * t)) :
    Nat.gcd n p.natAbs = 1 := by
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hnpos : 0 < n := by omega
  have hpos : (0 : ℝ) < (n : ℝ)⁻¹ := by positivity
  have ht : t = (p : ℝ) / n := by field_simp; linarith [hp]
  have key : ∀ a b : Fin n, a ≠ b → ¬ ((n : ℤ) ∣ (e a - e b) * p) := by
    intro a b hab hdvd
    have hrw : ((e a - e b : ℤ) : ℝ) * t = (((e a - e b) * p : ℤ) : ℝ) / n := by
      rw [ht]; push_cast; ring
    have h0 := circDist_int_div_of_dvd hnpos hdvd
    have hab' := hiso a b hab
    rw [hrw, h0] at hab'
    exact absurd hab' (not_le.mpr hpos)
  have hdist : ∀ a b : Fin n, a ≠ b → ¬ ((n : ℤ) ∣ (e a - e b)) := by
    intro a b hab hdvd
    exact key a b hab (hdvd.mul_right p)
  by_contra hg
  obtain ⟨a, b, hab, hdvd⟩ := break_of_not_coprime hnpos e hdist p hg
  exact key a b hab hdvd

/-- **Part 2(b) at general `n`, both halves.**  Global isolation of a primitive
configuration happens only at `t = p/n` with `gcd(n, p) = 1` — and by
`isolation_iff_coprime` it happens at every such `t`, of which `card_coprime_eq_totient`
counts `φ(n)` per period.

This is the framework's sole external dependency, derived here from its own objects.
**It says where global isolation can occur once it occurs, not that it occurs**, and it
does not approach part 7. -/
theorem isolation_forces_coprime_grid {n : ℕ} (hn : 1 < n) (e : Fin n → ℤ)
    (hprim : (univ : Finset (Fin n)).gcd e = 1)
    (j₀ : Fin n) (he : e j₀ = 0) (t : ℝ)
    (hiso : ∀ a b : Fin n, a ≠ b → (n : ℝ)⁻¹ ≤ circDist ((e a - e b : ℤ) * t)) :
    ∃ p : ℤ, (n : ℝ) * t = p ∧ Nat.gcd n p.natAbs = 1 := by
  obtain ⟨p, hp⟩ := instants_on_grid hn e hprim j₀ he t hiso
  exact ⟨p, hp, coprime_of_isolation hn e t p hp hiso⟩

/-- **Non-vacuity.**  A theorem whose hypotheses cannot all hold proves nothing, so here is
a configuration satisfying every hypothesis of `isolation_forces_coprime_grid`: two runners
at relative speeds `0` and `1`, isolated at `t = 1/2`.  It returns `p = 1`, coprime to `2`. -/
theorem instants_hypotheses_satisfiable :
    ∃ (e : Fin 2 → ℤ) (j₀ : Fin 2) (t : ℝ),
      (univ : Finset (Fin 2)).gcd e = 1 ∧ e j₀ = 0 ∧
      (∀ a b : Fin 2, a ≠ b → ((2 : ℕ) : ℝ)⁻¹ ≤ circDist ((e a - e b : ℤ) * t)) := by
  refine ⟨![0, 1], 0, 1/2, by decide, by decide, ?_⟩
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp_all <;>
    · norm_num [circDist, Int.fract]

end ConstructionN
