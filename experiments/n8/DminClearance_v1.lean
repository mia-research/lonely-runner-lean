import LonelyRunner.LRC.ConstructionN.LemmaPass

/-! # When does a subject clear at its own `d_min`, with no cascade at all?

Audit finding.  I reported "63.8% / 66.7% clear at scale `d_min` with zero cascade moves" several
times without ever giving a criterion — and separately refuted a parallel session's proposed
theorem for exactly this case (`FILTER_ASSESSMENT_AND_CROSSCHECK_v1` B.3) without supplying the
correct one.  A deterministic arithmetic fact was left as a percentage.  Here it is.

At scale `D = d_min` the reading of disparity `d` is `s = d/d_min`.  In reduced units `d = a·g`
and `d_min = c·g`, so `s = a/c` and the blocking condition `|s − 8M| < 1` becomes `|a − 8Mc| < c`.
Hence, with the threshold counting as clear:

> **clear at `d_min`  ⟺  every disparity satisfies  `c ≤ a mod 8c ≤ 7c`**,  where `c = d_min/g`.

Verified against the cascade on 32,000 subject-instances: **32,000 / 32,000**
(`dmin_criterion_v1.py`).  The parallel session's predicate ("unique residue", which is the
criterion at scale `g`, not at scale `d_min`) agrees only 57.2%.

Sanity: `a = c` (the minimum itself) gives `c mod 8c = c`, on the boundary, clear — as it must be,
since `d_min` is what defines the scale. -/

namespace DminClearance

/-- The blocking condition, reduced to the residue.  With `0 ≤ r < 8c`, some multiple of `8c` lands
within `c` of `r` exactly when `r` is in one of the two end zones. -/
theorem bad_iff {c r : ℤ} (hc : 0 < c) (h0 : 0 ≤ r) (h1 : r < 8 * c) :
    (∃ k : ℤ, |8 * c * k + r| < c) ↔ (r < c ∨ 7 * c < r) := by
  constructor
  · rintro ⟨k, hk⟩
    rw [abs_lt] at hk
    obtain ⟨hlo, hhi⟩ := hk
    rcases lt_trichotomy k 0 with h | h | h
    · right
      have hk1 : k ≤ -1 := by omega
      nlinarith [mul_le_mul_of_nonneg_left hk1 (le_of_lt (by linarith : (0:ℤ) < 8 * c))]
    · subst h; left; simpa using hhi
    · exfalso
      have hk1 : 1 ≤ k := by omega
      nlinarith [mul_le_mul_of_nonneg_left hk1 (le_of_lt (by linarith : (0:ℤ) < 8 * c))]
  · rintro (h | h)
    · exact ⟨0, by rw [abs_lt]; constructor <;> omega⟩
    · exact ⟨-1, by rw [abs_lt]; constructor <;> nlinarith⟩

/-- **The criterion.**  Disparity `a` (in reduced units) leaves the subject clear at scale `c`
exactly when `a`'s residue mod `8c` lies in the central band `[c, 7c]`. -/
theorem clear_iff {a c : ℤ} (hc : 0 < c) :
    (∀ M : ℤ, c ≤ |a - 8 * M * c|) ↔ (c ≤ a % (8 * c) ∧ a % (8 * c) ≤ 7 * c) := by
  have h8c : (0:ℤ) < 8 * c := by linarith
  set r := a % (8 * c) with hr
  have h0 : 0 ≤ r := Int.emod_nonneg _ (by omega)
  have h1 : r < 8 * c := Int.emod_lt_of_pos _ h8c
  have hsplit : 8 * c * (a / (8 * c)) + r = a := Int.mul_ediv_add_emod a (8 * c)
  have hbij : (∃ M : ℤ, |a - 8 * M * c| < c) ↔ (∃ k : ℤ, |8 * c * k + r| < c) := by
    constructor
    · rintro ⟨M, hM⟩
      refine ⟨a / (8 * c) - M, ?_⟩
      have : 8 * c * (a / (8 * c) - M) + r = a - 8 * M * c := by linarith [hsplit]
      rwa [this]
    · rintro ⟨k, hk⟩
      refine ⟨a / (8 * c) - k, ?_⟩
      have : a - 8 * (a / (8 * c) - k) * c = 8 * c * k + r := by linarith [hsplit]
      rwa [this]
  have hbad := (hbij.trans (bad_iff hc h0 h1))
  constructor
  · intro h
    by_contra hcon
    have : r < c ∨ 7 * c < r := by omega
    obtain ⟨M, hM⟩ := hbad.mpr this
    exact absurd (h M) (by omega)
  · rintro ⟨hlo, hhi⟩ M
    by_contra hM
    have : r < c ∨ 7 * c < r := hbad.mp ⟨M, by omega⟩
    omega



/-! ## Corollary: `S ≤ 7` forces clearance, and `d_min` never fails

Decomposing the balance (the subjects that do *not* clear at `d_min`) from the criterion:

* `a mod 8c > 7c` with `a < 8c` needs `7c < a < 8c` — reading in `(7,8)`;
* `a mod 8c < c` with `a ≥ c` needs `a ≥ 8c` — reading `≥ 8`.

Both require the reading `a/c` to exceed `7`. So a subject whose spread satisfies `S ≤ 7` cannot
fail — which is Theorem 4.8's constant, arriving here as a corollary rather than an input.
Measured: **9716 / 9716**, zero violations (`dmin_balance_v1.py`).

And `d_min` itself is always clear: `a = c` gives `c mod 8c = c`, on the boundary. So at most `6`
of a subject's `7` disparities can ever fail; measured maximum is `5`. -/

/-- **`S ≤ 7` forces clearance at `d_min`.**  A disparity whose reading lies in `[1, 7]` is inside
the central band already, so its residue mod `8c` is itself. -/
theorem clear_of_reading_le_seven {a c : ℤ} (hc : 0 < c) (hlo : c ≤ a) (hhi : a ≤ 7 * c) :
    c ≤ a % (8 * c) ∧ a % (8 * c) ≤ 7 * c := by
  have h : a % (8 * c) = a := Int.emod_eq_of_lt (by omega) (by omega)
  omega

/-- **`d_min` itself never fails.**  Taking `a = c`, the residue is `c`, on the lower boundary —
and the threshold counts as clear.  Hence at most `6` of the `7` disparities can fail. -/
theorem dmin_always_clear {c : ℤ} (hc : 0 < c) :
    c ≤ c % (8 * c) ∧ c % (8 * c) ≤ 7 * c :=
  clear_of_reading_le_seven hc le_rfl (by omega)



/-! ## The criterion does not depend on `8`

Nothing in `bad_iff`'s proof uses the value `8`, so the whole thing is a general-`n` statement with
the constant `n − 1`. At `n = 8` that constant is `7` — Theorem 4.8's. So:

> **at any order `n`, a subject clears at its own `d_min` whenever `S ≤ n − 1`**,

and more precisely whenever every disparity has `c ≤ a mod nc ≤ (n−1)c`. The `n = 8` versions above
are the `n := 8` instances. -/

/-- `bad_iff` at arbitrary order. -/
theorem bad_iff_gen {n c r : ℤ} (hc : 0 < c) (hn : 1 < n) (h0 : 0 ≤ r) (h1 : r < n * c) :
    (∃ k : ℤ, |n * c * k + r| < c) ↔ (r < c ∨ (n - 1) * c < r) := by
  constructor
  · rintro ⟨k, hk⟩
    rw [abs_lt] at hk
    obtain ⟨hlo, hhi⟩ := hk
    rcases lt_trichotomy k 0 with h | h | h
    · right
      have hk1 : k ≤ -1 := by omega
      nlinarith [mul_le_mul_of_nonneg_left hk1 (le_of_lt (by nlinarith : (0:ℤ) < n * c))]
    · subst h; left; simpa using hhi
    · exfalso
      have hk1 : 1 ≤ k := by omega
      nlinarith [mul_le_mul_of_nonneg_left hk1 (le_of_lt (by nlinarith : (0:ℤ) < n * c))]
  · rintro (h | h)
    · exact ⟨0, by rw [abs_lt]; constructor <;> omega⟩
    · exact ⟨-1, by rw [abs_lt]; constructor <;> nlinarith⟩

/-- **`S ≤ n − 1` forces clearance at `d_min`, at every order.**  The `n = 8` case is
`clear_of_reading_le_seven`, i.e. Theorem 4.8's constant. -/
theorem clear_of_reading_le_gen {n a c : ℤ} (hc : 0 < c) (hlo : c ≤ a) (hhi : a ≤ (n - 1) * c) :
    c ≤ a % (n * c) ∧ a % (n * c) ≤ (n - 1) * c := by
  have h : a % (n * c) = a := Int.emod_eq_of_lt (by omega) (by nlinarith)
  omega



/-! ## `d_min` was never special: the criterion holds at every cascade scale

A cascade scale is `D = e·g/(8N+1)`, where the reading of disparity `a·g` is `a(8N+1)/e`. Blocking
is `|reading − 8M| < 1`, i.e. `|a(8N+1) − 8Me| < e` — which is `clear_iff`'s statement with `a`
replaced by `a(8N+1)` and `c` by `e`. So the general criterion *is* `clear_iff`:

> **clear at scale `e/(8N+1)` ⟺ for every disparity `a`,  `e ≤ a(8N+1) mod 8e ≤ 7e`**

and `clear_iff` as first stated is the case `e = d_min/g`, `N = 0`.

Verified against the cascade at **every scale it visits**, not only the first: 46,353 / 46,353
(`scale_criterion_v1.py`). The depth stratification that follows: `k=0` covers 53.0% of subjects,
through `k=1` 74.8%, `k=2` 88.0%, `k=3` 95.0%, `k=4` 97.7%.

So the cascade is a sequence of applications of **one** residue-band test, with the host `e` and
multiplier `8N+1` updating at each move. -/

/-- **The criterion at an arbitrary cascade scale.**  Identical to `clear_iff`; only the arguments
move.  Stated separately because the reading — not the disparity — is what carries the multiplier. -/
theorem clear_at_scale_iff {a e N : ℤ} (he : 0 < e) :
    (∀ M : ℤ, e ≤ |a * (8 * N + 1) - 8 * M * e|) ↔
      (e ≤ (a * (8 * N + 1)) % (8 * e) ∧ (a * (8 * N + 1)) % (8 * e) ≤ 7 * e) :=
  clear_iff he

end DminClearance
