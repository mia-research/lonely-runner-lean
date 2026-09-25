import LonelyRunner.LRC.Spec.MergeN

/-!
# The mirror merge: two runners read as one on the lattice of their sum

2026-09-24.  At an instant `t = K/(a + b)`, `(a + b)·t` is a whole number, so `b·t ≡ −a·t` and the
two runners stand at mirror positions: `circDist (b t) = circDist (a t)` (`circDist_mirror`).  On
that lattice a set with `a` and `b` is lonely exactly when the set without `b` is
(`lonely_mirror_iff`).  With whole-number disparities the instant is checked by residues:
`d·K mod (a + b)` in the band `[(a+b)/n, (n−1)(a+b)/n]` for every `d` (`lonely_of_mirror_band`).

This is the merge rule made exact, as in `RankTwoN.lean`, but on the whole-number line: the
lattice of the sum is where the two runners coincide.

Everything here is proved; no `sorry`, no `native_decide`.
-/

set_option linter.style.longLine false

namespace LRC.SpecN

open MomentIterationN ConstructionN

/-- **Mirror positions.**  If `(a + b)·t` is a whole number, `a` and `b` are equally far from the
subject. -/
theorem circDist_mirror {a b t : ℝ} {k : ℤ} (h : (a + b) * t = k) :
    circDist (b * t) = circDist (a * t) := by
  have : b * t = -(a * t) + k := by linarith [show (a + b) * t = a * t + b * t by ring]
  rw [this, circDist_add_int, circDist.symm_neg]

/-- **The mirror merge.**  On the lattice of `a + b`, a set holding `a` and `b` is lonely exactly
when it is lonely without `b`. -/
theorem lonely_mirror_iff {n : ℕ} {S : Finset ℝ} {a b t : ℝ} {k : ℤ} (ha : a ∈ S) (hab : a ≠ b)
    (h : (a + b) * t = k) :
    (∀ d ∈ insert b S, (n : ℝ)⁻¹ ≤ circDist (d * t)) ↔ ∀ d ∈ S, (n : ℝ)⁻¹ ≤ circDist (d * t) := by
  constructor
  · exact fun H d hd => H d (Finset.mem_insert_of_mem hd)
  · intro H d hd
    rcases Finset.mem_insert.mp hd with rfl | hdS
    · rw [circDist_mirror h]; exact H a ha
    · exact H d hdS

/-- **The mirror instant, by residues.**  For whole numbers, `K/q` is lonely at `1/n` when every
reading `d·K mod q` lies in `[q/n, (n−1)q/n]`.  With `q = a + b` the readings of `a` and `b` are
mirror images, so one check covers both. -/
theorem lonely_of_mirror_band {n q K : ℕ} (hq : 0 < q) (hn : 0 < n) {S : Finset ℕ}
    (hband : ∀ d ∈ S, q ≤ n * ((d * K) % q) ∧ n * ((d * K) % q) ≤ (n - 1) * q) :
    ∀ d ∈ S, (n : ℝ)⁻¹ ≤ circDist ((d : ℝ) * ((K : ℝ) / q)) := by
  intro d hd
  obtain ⟨h1, h2⟩ := hband d hd
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set r := (d * K) % q with hr
  set Q := (d * K) / q with hQ
  have hdiv : d * K = q * Q + r := (Nat.div_add_mod _ _).symm
  have hreal : (d : ℝ) * K = q * Q + r := by exact_mod_cast hdiv
  have heq : (d : ℝ) * ((K : ℝ) / q) = (r : ℝ) / q + ((Q : ℤ) : ℝ) := by
    rw [Int.cast_natCast]
    field_simp
    linarith
  rw [heq, circDist_add_int]
  have hrq : r < q := Nat.mod_lt _ hq
  have hn1 : 1 ≤ n := hn
  have hr1 : (q : ℝ) ≤ n * r := by exact_mod_cast h1
  have hr2 : (n : ℝ) * r ≤ (n - 1) * q := by
    have h2' := (Nat.cast_le (α := ℝ)).mpr h2
    have hc : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn1]; simp
    rw [Nat.cast_mul, Nat.cast_mul, hc] at h2'
    exact h2'
  have hfr : Int.fract ((r : ℝ) / q) = (r : ℝ) / q :=
    Int.fract_eq_self.mpr ⟨by positivity, by rw [div_lt_one hq']; exact_mod_cast hrq⟩
  unfold circDist
  rw [hfr, inv_eq_one_div]
  refine le_min ?_ ?_
  · rw [div_le_div_iff₀ hn' hq']; linarith
  · have e1 : (1 : ℝ) - r / q = (q - r) / q := by field_simp
    rw [e1, div_le_div_iff₀ hn' hq']
    nlinarith

end LRC.SpecN
