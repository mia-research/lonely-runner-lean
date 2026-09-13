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

The last two together are part 2(b).  **Part 7 is not stated here and is not approached by
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

end ConstructionN
