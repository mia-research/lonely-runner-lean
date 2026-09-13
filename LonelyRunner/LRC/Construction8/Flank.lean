import LonelyRunner.LRC.Construction8.Sorted

/-!
# Part 1 — the nearest other runner is a cyclic neighbour

`docs/n8/PROOF_CANDIDATE_v3.md` part 1; `docs/n8/PROOF_PLAN_v1.md` §2 target 3.

The content of part 1 is that seven constraints collapse to two: whether runner `i` is
lonely depends only on its two flanking gaps.  The half proved here is the direction that
produces loneliness — both flanking gaps reaching `1/n` puts *every* other runner at
distance at least `1/n`.

The argument needs only monotonicity of the sorted list and the positions lying in
`[0,1)`.  From index `k`, going one way you must cross the gap after `k`; going the other
way, the gap before it.  Whichever way the other runner lies, its circle distance is at
least one of those two, hence at least their minimum.

**Scope, stated rather than left to be read off the hypotheses.**  `circDist_ge_flank`
covers **interior** indices, `1 ≤ k` and `k + 1 < n`.  The two ends need the wrap — which
is exactly `SKETCH` §2's "there are no end runners", and formally it is the cyclic
indexing `cycGap` already carries.  Doing the ends means restating this against `cycGap`
rather than against `p k - p (k-1)` and `p (k+1) - p k` directly, and is not done here.

The converse direction — the minimum over all other runners is *attained* at a flanking
neighbour, so loneliness *implies* both flanking gaps reach `1/n` — is also not done.

Nothing here states or attempts part 7.
-/

namespace Construction8

/-- For `|x| < 1` the circle distance is `min |x| (1 - |x|)`, both signs at once. -/
theorem circDist_of_abs_lt_one {x : ℝ} (h : |x| < 1) : circDist x = min |x| (1 - |x|) := by
  rcases le_total 0 x with hx | hx
  · have hax : |x| = x := abs_of_nonneg hx
    rw [hax] at h ⊢
    unfold circDist
    rw [Int.fract_eq_self.mpr ⟨hx, h⟩]
  · have hax : |x| = -x := abs_of_nonpos hx
    rw [hax] at h ⊢
    rcases eq_or_lt_of_le hx with heq | hlt
    · subst heq; simp [circDist]
    · have hfloor : ⌊x⌋ = -1 := by
        rw [Int.floor_eq_iff]
        constructor <;> push_cast <;> linarith
      have hfr : Int.fract x = 1 + x := by
        unfold Int.fract; rw [hfloor]; push_cast; ring
      unfold circDist
      rw [hfr]
      have h2 : (1 : ℝ) - (1 + x) = -x := by ring
      have h3 : (1 : ℝ) - -x = 1 + x := by ring
      rw [h2, h3]
      exact min_comm _ _

/-- **The nearest other runner is a cyclic neighbour.**  For sorted positions in `[0,1)`
and an interior index `k`, the circle distance from `k` to any other index is at least the
smaller of `k`'s two flanking gaps. -/
theorem circDist_ge_flank (p : ℕ → ℝ) (n k m : ℕ)
    (hk1 : 1 ≤ k) (hkn : k + 1 < n) (hmn : m < n) (hmk : m ≠ k)
    (hmono : ∀ i j, i ≤ j → j < n → p i ≤ p j)
    (h0 : ∀ i, i < n → 0 ≤ p i) (h1 : ∀ i, i < n → p i < 1) :
    min (p k - p (k - 1)) (p (k + 1) - p k) ≤ circDist (p m - p k) := by
  have hk : k < n := by omega
  have hkm1 : k - 1 < n := by omega
  have hpm0 : 0 ≤ p m := h0 m hmn
  have hpm1 : p m < 1 := h1 m hmn
  have hpk0 : 0 ≤ p k := h0 k hk
  have hpk1 : p k < 1 := h1 k hk
  have hpk11 : p (k + 1) < 1 := h1 _ hkn
  have hpkm10 : 0 ≤ p (k - 1) := h0 _ hkm1
  have habs : |p m - p k| < 1 := by rw [abs_lt]; constructor <;> linarith
  rw [circDist_of_abs_lt_one habs]
  rcases lt_or_gt_of_ne hmk with hlt | hgt
  · have hle : p m ≤ p k := hmono m k (by omega) hk
    have hmk1 : p m ≤ p (k - 1) := hmono m (k - 1) (by omega) hkm1
    have hd : |p m - p k| = p k - p m := by rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    rw [hd]
    exact le_min (le_trans (min_le_left _ _) (by linarith))
                 (le_trans (min_le_right _ _) (by linarith))
  · have hge : p k ≤ p m := hmono k m (by omega) hmn
    have hk1m : p (k + 1) ≤ p m := hmono (k + 1) m (by omega) hmn
    have hd : |p m - p k| = p m - p k := abs_of_nonneg (by linarith)
    rw [hd]
    exact le_min (le_trans (min_le_right _ _) (by linarith))
                 (le_trans (min_le_left _ _) (by linarith))

/-- **Part 1, the direction that produces loneliness.**  Both flanking gaps reaching `1/n`
puts every other runner at distance at least `1/n` — seven constraints from two. -/
theorem lonely_of_flanks {n : ℕ} (p : ℕ → ℝ) (k : ℕ)
    (hk1 : 1 ≤ k) (hkn : k + 1 < n)
    (hmono : ∀ i j, i ≤ j → j < n → p i ≤ p j)
    (h0 : ∀ i, i < n → 0 ≤ p i) (h1 : ∀ i, i < n → p i < 1)
    (hflank : (n : ℝ)⁻¹ ≤ min (p k - p (k - 1)) (p (k + 1) - p k))
    (m : ℕ) (hmn : m < n) (hmk : m ≠ k) :
    (n : ℝ)⁻¹ ≤ circDist (p m - p k) :=
  le_trans hflank (circDist_ge_flank p n k m hk1 hkn hmn hmk hmono h0 h1)

/-! ## The ends — "there are no end runners"

`SKETCH` §2 makes adjacency cyclic so the first and last runners are not special: the
first runner's gap *before* it is the wrap, and the last runner's gap *after* it is the
same wrap.  With that reading both ends have two flanking gaps like everyone else, and the
same argument applies.
-/

/-- **The first runner has two flanking gaps too**, its gap before being the wrap. -/
theorem circDist_ge_flank_first (p : ℕ → ℝ) (n m : ℕ) (hn : 1 < n) (hmn : m < n) (hm0 : m ≠ 0)
    (hmono : ∀ i j, i ≤ j → j < n → p i ≤ p j)
    (h0 : ∀ i, i < n → 0 ≤ p i) (h1 : ∀ i, i < n → p i < 1) :
    min (1 - p (n - 1) + p 0) (p 1 - p 0) ≤ circDist (p m - p 0) := by
  have h0n : 0 < n := by omega
  have hn1 : n - 1 < n := by omega
  have hpm0 : 0 ≤ p m := h0 m hmn
  have hpm1 : p m < 1 := h1 m hmn
  have hp00 : 0 ≤ p 0 := h0 0 h0n
  have hp01 : p 0 < 1 := h1 0 h0n
  have habs : |p m - p 0| < 1 := by rw [abs_lt]; constructor <;> linarith
  rw [circDist_of_abs_lt_one habs]
  have hge : p 0 ≤ p m := hmono 0 m (by omega) hmn
  have hd : |p m - p 0| = p m - p 0 := abs_of_nonneg (by linarith)
  rw [hd]
  have h1m : p 1 ≤ p m := hmono 1 m (by omega) hmn
  have hmn1 : p m ≤ p (n - 1) := hmono m (n - 1) (by omega) hn1
  exact le_min (le_trans (min_le_right _ _) (by linarith))
               (le_trans (min_le_left _ _) (by linarith))

/-- **And the last runner**, its gap after being the same wrap. -/
theorem circDist_ge_flank_last (p : ℕ → ℝ) (n m : ℕ) (hn : 1 < n) (hmn : m < n)
    (hml : m ≠ n - 1)
    (hmono : ∀ i j, i ≤ j → j < n → p i ≤ p j)
    (h0 : ∀ i, i < n → 0 ≤ p i) (h1 : ∀ i, i < n → p i < 1) :
    min (p (n - 1) - p (n - 2)) (1 - p (n - 1) + p 0) ≤ circDist (p m - p (n - 1)) := by
  have h0n : 0 < n := by omega
  have hn1 : n - 1 < n := by omega
  have hn2 : n - 2 < n := by omega
  have hpm0 : 0 ≤ p m := h0 m hmn
  have hpm1 : p m < 1 := h1 m hmn
  have hpl0 : 0 ≤ p (n - 1) := h0 _ hn1
  have hpl1 : p (n - 1) < 1 := h1 _ hn1
  have habs : |p m - p (n - 1)| < 1 := by rw [abs_lt]; constructor <;> linarith
  rw [circDist_of_abs_lt_one habs]
  have hle : p m ≤ p (n - 1) := hmono m (n - 1) (by omega) hn1
  have hd : |p m - p (n - 1)| = p (n - 1) - p m := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
  rw [hd]
  have hmn2 : p m ≤ p (n - 2) := hmono m (n - 2) (by omega) hn2
  have h0m : p 0 ≤ p m := hmono 0 m (by omega) hmn
  exact le_min (le_trans (min_le_left _ _) (by linarith))
               (le_trans (min_le_right _ _) (by linarith))

/-- Part 1's producing direction at the first runner. -/
theorem lonely_of_flanks_first {n : ℕ} (p : ℕ → ℝ) (hn : 1 < n)
    (hmono : ∀ i j, i ≤ j → j < n → p i ≤ p j)
    (h0 : ∀ i, i < n → 0 ≤ p i) (h1 : ∀ i, i < n → p i < 1)
    (hflank : (n : ℝ)⁻¹ ≤ min (1 - p (n - 1) + p 0) (p 1 - p 0))
    (m : ℕ) (hmn : m < n) (hm0 : m ≠ 0) :
    (n : ℝ)⁻¹ ≤ circDist (p m - p 0) :=
  le_trans hflank (circDist_ge_flank_first p n m hn hmn hm0 hmono h0 h1)

/-- Part 1's producing direction at the last runner. -/
theorem lonely_of_flanks_last {n : ℕ} (p : ℕ → ℝ) (hn : 1 < n)
    (hmono : ∀ i j, i ≤ j → j < n → p i ≤ p j)
    (h0 : ∀ i, i < n → 0 ≤ p i) (h1 : ∀ i, i < n → p i < 1)
    (hflank : (n : ℝ)⁻¹ ≤ min (p (n - 1) - p (n - 2)) (1 - p (n - 1) + p 0))
    (m : ℕ) (hmn : m < n) (hml : m ≠ n - 1) :
    (n : ℝ)⁻¹ ≤ circDist (p m - p (n - 1)) :=
  le_trans hflank (circDist_ge_flank_last p n m hn hmn hml hmono h0 h1)

/-! ## The converse — a lonely runner has both flanking gaps at `1/n`

Only the two flanking pairs are needed, not the attainment of any minimum.  Instantiating
loneliness at `k-1` and `k+1` gives each gap directly; at the ends, the wrap gap comes
from the complementary arc of the far pair.
-/

/-- The other half of `le_of_le_circDist`: a circle distance of at least `1/n` also bounds
the complementary arc. -/
theorem one_sub_ge_of_circDist {n : ℕ} {x : ℝ} (h : |x| < 1)
    (hc : (n : ℝ)⁻¹ ≤ circDist x) : (n : ℝ)⁻¹ ≤ 1 - |x| := by
  rw [circDist_of_abs_lt_one h] at hc
  exact le_trans hc (min_le_right _ _)

/-- **Part 1's converse, interior.** -/
theorem flanks_of_lonely {n : ℕ} (hn : 0 < n) (p : ℕ → ℝ) (k : ℕ)
    (hk1 : 1 ≤ k) (hkn : k + 1 < n)
    (hmono : ∀ i j, i ≤ j → j < n → p i ≤ p j)
    (hlonely : ∀ m, m < n → m ≠ k → (n : ℝ)⁻¹ ≤ circDist (p m - p k)) :
    (n : ℝ)⁻¹ ≤ min (p k - p (k - 1)) (p (k + 1) - p k) := by
  have hk : k < n := by omega
  refine le_min ?_ ?_
  · have h := hlonely (k - 1) (by omega) (by omega)
    have hneg : p (k - 1) - p k = -(p k - p (k - 1)) := by ring
    rw [hneg, circDist.symm_neg] at h
    exact le_of_le_circDist hn (by have := hmono (k - 1) k (by omega) hk; linarith) h
  · have h := hlonely (k + 1) (by omega) (by omega)
    exact le_of_le_circDist hn (by have := hmono k (k + 1) (by omega) hkn; linarith) h

/-- **Part 1's converse at the first runner.** -/
theorem flanks_of_lonely_first {n : ℕ} (hn : 1 < n) (p : ℕ → ℝ)
    (hmono : ∀ i j, i ≤ j → j < n → p i ≤ p j)
    (h0 : ∀ i, i < n → 0 ≤ p i) (h1 : ∀ i, i < n → p i < 1)
    (hlonely : ∀ m, m < n → m ≠ 0 → (n : ℝ)⁻¹ ≤ circDist (p m - p 0)) :
    (n : ℝ)⁻¹ ≤ min (1 - p (n - 1) + p 0) (p 1 - p 0) := by
  have h0n : 0 < n := by omega
  have hn1 : n - 1 < n := by omega
  refine le_min ?_ ?_
  · have h := hlonely (n - 1) hn1 (by omega)
    have hge : p 0 ≤ p (n - 1) := hmono 0 (n - 1) (by omega) hn1
    have habs : |p (n - 1) - p 0| = p (n - 1) - p 0 := abs_of_nonneg (by linarith)
    have hlt : |p (n - 1) - p 0| < 1 := by
      rw [habs]; have := h0 0 h0n; have := h1 (n - 1) hn1; linarith
    have hres := one_sub_ge_of_circDist hlt h
    rw [habs] at hres; linarith
  · have h := hlonely 1 (by omega) (by omega)
    exact le_of_le_circDist h0n (by have := hmono 0 1 (by omega) (by omega); linarith) h

/-- **Part 1's converse at the last runner.** -/
theorem flanks_of_lonely_last {n : ℕ} (hn : 1 < n) (p : ℕ → ℝ)
    (hmono : ∀ i j, i ≤ j → j < n → p i ≤ p j)
    (h0 : ∀ i, i < n → 0 ≤ p i) (h1 : ∀ i, i < n → p i < 1)
    (hlonely : ∀ m, m < n → m ≠ n - 1 → (n : ℝ)⁻¹ ≤ circDist (p m - p (n - 1))) :
    (n : ℝ)⁻¹ ≤ min (p (n - 1) - p (n - 2)) (1 - p (n - 1) + p 0) := by
  have h0n : 0 < n := by omega
  have hn1 : n - 1 < n := by omega
  have hn2 : n - 2 < n := by omega
  refine le_min ?_ ?_
  · have h := hlonely (n - 2) hn2 (by omega)
    have hneg : p (n - 2) - p (n - 1) = -(p (n - 1) - p (n - 2)) := by ring
    rw [hneg, circDist.symm_neg] at h
    exact le_of_le_circDist h0n
      (by have := hmono (n - 2) (n - 1) (by omega) hn1; linarith) h
  · have h := hlonely 0 h0n (by omega)
    have hneg : p 0 - p (n - 1) = -(p (n - 1) - p 0) := by ring
    rw [hneg, circDist.symm_neg] at h
    have hge : p 0 ≤ p (n - 1) := hmono 0 (n - 1) (by omega) hn1
    have habs : |p (n - 1) - p 0| = p (n - 1) - p 0 := abs_of_nonneg (by linarith)
    have hlt : |p (n - 1) - p 0| < 1 := by
      rw [habs]; have := h0 0 h0n; have := h1 (n - 1) hn1; linarith
    have hres := one_sub_ge_of_circDist hlt h
    rw [habs] at hres; linarith

/-! ## Part 1, as an iff

`PROOF_CANDIDATE_v3` part 1 states it as an iff, and this is it, at every index: the
seven constraints on a runner are equivalent to the two on its flanking gaps.
-/

/-- **Part 1, interior.**  Lonely iff both flanking gaps reach `1/n`. -/
theorem lonely_iff_flanks {n : ℕ} (hn : 0 < n) (p : ℕ → ℝ) (k : ℕ)
    (hk1 : 1 ≤ k) (hkn : k + 1 < n)
    (hmono : ∀ i j, i ≤ j → j < n → p i ≤ p j)
    (h0 : ∀ i, i < n → 0 ≤ p i) (h1 : ∀ i, i < n → p i < 1) :
    (∀ m, m < n → m ≠ k → (n : ℝ)⁻¹ ≤ circDist (p m - p k))
      ↔ (n : ℝ)⁻¹ ≤ min (p k - p (k - 1)) (p (k + 1) - p k) :=
  ⟨fun h => flanks_of_lonely hn p k hk1 hkn hmono h,
   fun h m hm hmk => lonely_of_flanks p k hk1 hkn hmono h0 h1 h m hm hmk⟩

/-- **Part 1, first runner.** -/
theorem lonely_iff_flanks_first {n : ℕ} (hn : 1 < n) (p : ℕ → ℝ)
    (hmono : ∀ i j, i ≤ j → j < n → p i ≤ p j)
    (h0 : ∀ i, i < n → 0 ≤ p i) (h1 : ∀ i, i < n → p i < 1) :
    (∀ m, m < n → m ≠ 0 → (n : ℝ)⁻¹ ≤ circDist (p m - p 0))
      ↔ (n : ℝ)⁻¹ ≤ min (1 - p (n - 1) + p 0) (p 1 - p 0) :=
  ⟨fun h => flanks_of_lonely_first hn p hmono h0 h1 h,
   fun h m hm hm0 => lonely_of_flanks_first p hn hmono h0 h1 h m hm hm0⟩

/-- **Part 1, last runner.** -/
theorem lonely_iff_flanks_last {n : ℕ} (hn : 1 < n) (p : ℕ → ℝ)
    (hmono : ∀ i j, i ≤ j → j < n → p i ≤ p j)
    (h0 : ∀ i, i < n → 0 ≤ p i) (h1 : ∀ i, i < n → p i < 1) :
    (∀ m, m < n → m ≠ n - 1 → (n : ℝ)⁻¹ ≤ circDist (p m - p (n - 1)))
      ↔ (n : ℝ)⁻¹ ≤ min (p (n - 1) - p (n - 2)) (1 - p (n - 1) + p 0) :=
  ⟨fun h => flanks_of_lonely_last hn p hmono h0 h1 h,
   fun h m hm hml => lonely_of_flanks_last p hn hmono h0 h1 h m hm hml⟩

end Construction8
