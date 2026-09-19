import Mathlib

/-!
# The last class, and why the largest-flank counterexample exists

At order `n`, a mover `p/q` blocks the candidate `A` when the residue of `p*A` modulo
`n*q` lies within `q` of a multiple of `n*q`.  For the candidate family `A = n*k+1`
the residue has the closed form `n*u + p` with `u = (p*k) mod q` (`residue_form`).

Three consequences, all general in `n`:

* `only_zero_class` — if `p + q ≤ n` the mover blocks **only** the class `q ∣ p*k`.
  A second blocked class requires `n < p + q`.
* `second_class_blocks` — when `n < p + q` the class `(p*k) % q = q-1` is blocked.
* `last_class_forces` — the class `k ≡ -1 (mod q)` is blocked, among `q ≤ n`,
  **only** by the single mover `1/n`.

The last of these explains the refutation of the largest-flank hypothesis `H`.
Saturating the candidate index needs the class `k ≡ -1`, hence needs `q = n`;
with `q ≤ n-1` it is unreachable.  That is the same boundary at which
`Rescale.small_b_blocks_iff` breaks and at which the `n-1` constant of Theorem 4.8
fails, and it is where the exhaustive tables put the first shadowing multiset.
-/

namespace LastClass

/-- Mover `p/q` blocks candidate `A` at order `n`. -/
def blocksN (n p A q : ℤ) : Prop :=
  min ((p * A) % (n * q)) (n * q - (p * A) % (n * q)) < q

/-- Closed form for the residue on the candidate family `A = n*k+1`. -/
theorem residue_form {n p q k : ℤ} (hq : 0 < q) (hn : 0 < n) (hp : 0 < p) (hpn : p < n) :
    (p * (n * k + 1)) % (n * q) = n * ((p * k) % q) + p := by
  have hu0 : 0 ≤ (p * k) % q := Int.emod_nonneg _ (by omega)
  have hu1 : (p * k) % q < q := Int.emod_lt_of_pos _ hq
  have key : p * (n * k + 1) = (n * ((p * k) % q) + p) + n * q * ((p * k) / q) := by
    have h := Int.mul_ediv_add_emod (p * k) q
    nlinarith [h]
  rw [key, Int.add_mul_emod_self_left]
  exact Int.emod_eq_of_lt (by nlinarith) (by nlinarith)

/-- **No second class below the threshold.**  If `p + q ≤ n`, the mover `p/q` blocks
only the zero class: every `k` with `q ∤ p*k` is clear. -/
theorem only_zero_class {n p q k : ℤ} (hp : 0 < p) (hpq : p < q) (hsum : p + q ≤ n)
    (hne : (p * k) % q ≠ 0) : ¬ blocksN n p (n * k + 1) q := by
  have hq : 0 < q := by omega
  have hn : 0 < n := by omega
  have hpn : p < n := by omega
  have hu0 : 0 ≤ (p * k) % q := Int.emod_nonneg _ (by omega)
  have hu1 : (p * k) % q < q := Int.emod_lt_of_pos _ hq
  have hu : 1 ≤ (p * k) % q := by omega
  unfold blocksN
  rw [residue_form hq hn hp hpn]
  simp only [not_lt, le_min_iff]
  exact ⟨by nlinarith, by nlinarith⟩

/-- **Above the threshold the second class appears.**  When `n < p + q` the class
`(p*k) % q = q-1` is blocked. -/
theorem second_class_blocks {n p q k : ℤ} (hp : 0 < p) (hpq : p < q) (hqn : q ≤ n)
    (hsum : n < p + q) (hk : (p * k) % q = q - 1) : blocksN n p (n * k + 1) q := by
  have hq : 0 < q := by omega
  have hn : 0 < n := by omega
  have hpn : p < n := by omega
  unfold blocksN
  rw [residue_form hq hn hp hpn, hk]
  have h : n * q - (n * (q - 1) + p) = n - p := by ring
  calc min (n * (q - 1) + p) (n * q - (n * (q - 1) + p))
      ≤ n * q - (n * (q - 1) + p) := min_le_right _ _
    _ = n - p := h
    _ < q := by omega

/-- The residue of `p*k` when `k ≡ -1 (mod q)`. -/
theorem neg_one_residue {p q k : ℤ} (hp : 0 < p) (hpq : p < q) (hk : k % q = q - 1) :
    (p * k) % q = q - p := by
  have hq : 0 < q := by omega
  have h1 : (p * k) % q = (p % q * (k % q)) % q := Int.mul_emod p k q
  have h2 : p % q = p := Int.emod_eq_of_lt (by omega) hpq
  rw [h1, h2, hk]
  have h3 : p * (q - 1) = (q - p) + q * (p - 1) := by ring
  rw [h3, Int.add_mul_emod_self_left]
  exact Int.emod_eq_of_lt (by omega) (by omega)

/-- **The last class is reachable only by `1/n`.**  Among movers with `q ≤ n`,
the class `k ≡ -1 (mod q)` is blocked exactly by `p = 1, q = n`.  This is why
a shadowing configuration cannot be built from denominators `q ≤ n-1`. -/
theorem last_class_forces {n p q k : ℤ} (hp : 0 < p) (hpq : p < q) (hqn : q ≤ n)
    (hn2 : 2 ≤ n) (hk : k % q = q - 1) (hb : blocksN n p (n * k + 1) q) :
    p = 1 ∧ q = n := by
  have hq : 0 < q := by omega
  have hn : 0 < n := by omega
  have hpn : p < n := by omega
  have hu : (p * k) % q = q - p := neg_one_residue hp hpq hk
  -- the residue is `n*(q-p) + p`; its distance to `n*q` is `p*(n-1)`
  have hr : (p * (n * k + 1)) % (n * q) = n * (q - p) + p := by
    rw [residue_form hq hn hp hpn, hu]
  have hmin : min (n * (q - p) + p) (n * q - (n * (q - p) + p)) < q := by
    unfold blocksN at hb; rwa [hr] at hb
  have hhi : n * q - (n * (q - p) + p) = p * (n - 1) := by ring
  -- the low branch is too big, so the high branch must be the small one
  have hlow : q ≤ n * (q - p) + p := by nlinarith
  have hp1 : p * (n - 1) < q := by
    rcases min_cases (n * (q - p) + p) (n * q - (n * (q - p) + p)) with ⟨he, _⟩ | ⟨he, _⟩
    · omega
    · rw [he, hhi] at hmin; exact hmin
  have : p = 1 := by nlinarith
  subst this
  constructor
  · rfl
  · nlinarith

/-- **A mover with a small denominator cannot block the last index.**  If `q ≤ n-1`
and `q ∣ k+1`, the mover `p/q` leaves `k` clear. -/
theorem clear_of_small_denom {n p q k : ℤ} (hp : 0 < p) (hpq : p < q) (hqn : q ≤ n - 1)
    (hn2 : 2 ≤ n) (hdvd : q ∣ (k + 1)) : ¬ blocksN n p (n * k + 1) q := by
  intro hb
  have hq : 0 < q := by omega
  have hk : k % q = q - 1 := by
    obtain ⟨c, hc⟩ := hdvd
    have hk' : k = (q - 1) + q * (c - 1) := by linarith [hc]
    rw [hk', Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt (by omega) (by omega)
  have h := last_class_forces hp hpq (by omega) hn2 hk hb
  omega

/-- **No shadowing below the full denominator.**  If every mover's denominator divides
`L` and is at most `n-1`, then the index `k = L-1` is clear for all of them at once.
This turns the exhaustive `q ≤ n-1` tables into a theorem: it holds for any number of
movers and any order `n`. -/
theorem lcm_minus_one_clear {n L : ℤ} (hn2 : 2 ≤ n) (ms : List (ℤ × ℤ))
    (hms : ∀ m ∈ ms, 0 < m.1 ∧ m.1 < m.2 ∧ m.2 ≤ n - 1 ∧ m.2 ∣ L) :
    ∀ m ∈ ms, ¬ blocksN n m.1 (n * (L - 1) + 1) m.2 := by
  intro m hm
  obtain ⟨h1, h2, h3, h4⟩ := hms m hm
  exact clear_of_small_denom h1 h2 h3 hn2 (by rw [sub_add_cancel]; exact h4)

/-- **Contrapositive: shadowing forces a denominator of at least `n`.**  If the index
`L-1` is blocked by some mover whose denominator divides `L`, that mover has `q ≥ n`. -/
theorem shadow_needs_full_denom {n L : ℤ} (hn2 : 2 ≤ n) (ms : List (ℤ × ℤ))
    (hpos : ∀ m ∈ ms, 0 < m.1 ∧ m.1 < m.2 ∧ m.2 ∣ L)
    (hshadow : ∃ m ∈ ms, blocksN n m.1 (n * (L - 1) + 1) m.2) :
    ∃ m ∈ ms, n ≤ m.2 := by
  obtain ⟨m, hm, hb⟩ := hshadow
  obtain ⟨h1, h2, h4⟩ := hpos m hm
  refine ⟨m, hm, ?_⟩
  by_contra h
  exact clear_of_small_denom h1 h2 (by omega) hn2 (by rw [sub_add_cancel]; exact h4) hb

end LastClass

#print axioms LastClass.residue_form
#print axioms LastClass.only_zero_class
#print axioms LastClass.second_class_blocks
#print axioms LastClass.neg_one_residue
#print axioms LastClass.last_class_forces
#print axioms LastClass.clear_of_small_denom
#print axioms LastClass.lcm_minus_one_clear
#print axioms LastClass.shadow_needs_full_denom
