import LonelyRunner.LRC.Spec.OrderEightCasesN

/-!
# Order eight: the rung budget and the link lemma

2026-09-25.  A **rung** is a flank `e = N·M` and the rational openings `t = i/N + 1/(8e)` at it
(`OrderEightCasesN`, §2c).  An index `i` sharing a factor with `N` is a rung of smaller `N`, so the
instants a rung adds are its units, `φ(N)` of them.  A disparity `d` is blocked at `i` exactly when
its class condition `ClassClear8 N M i d` fails, and that condition sees `i` only through
`i·d mod N`.

* **The rung budget** (`lonely_eight_of_rung_budget`).  If the units at which some disparity is
  blocked, counted disparity by disparity, number fewer than `φ(N)`, then some unit is blocked by
  none, and its rational opening is lonely.  A pigeonhole over `(ℤ/N)ˣ`.  R4 is the case `N = 8` at
  the largest multiple of `8`; the thirds, fifths and sixths rules are further cases.  On the
  7-subsets of `[1, 30]` it holds at some rung for 12,257 of the 12,309 sets of the original
  residual (`experiments/nN/ladder_budget_v1.py`).
* **The link lemma** (`link_reading`).  If `N ∣ d' − c·d`, then at every opening
  `a = 8·(i·M) + 1` of the rung, `d'·a ≡ c·(d·a) + (d' − c·d) (mod 8e)`: the two readings move
  together, and a group of linked disparities is blocked exactly where one progression meets a
  list of arcs.  This is the constructive interference measured in
  `experiments/nN/interference_v1.py`.

Everything here is proved; no `sorry`, no `native_decide`.
-/

set_option linter.style.longLine false

namespace LRC.OrderEightN

instance decClassClear8 (N M i d : ℕ) : Decidable (ClassClear8 N M i d) := by
  unfold ClassClear8; infer_instance

/-- The units of a rung: the indices `i < N` coprime to `N`.  There are `φ(N)` of them. -/
def rungUnits (N : ℕ) : Finset ℕ := (Finset.range N).filter N.Coprime

theorem card_rungUnits (N : ℕ) : (rungUnits N).card = N.totient :=
  (Nat.totient_eq_card_coprime N).symm

/-- The units of the rung `(N, M)` at which the disparity `d` is blocked. -/
def rungBlocked (N M d : ℕ) : Finset ℕ :=
  (rungUnits N).filter (fun i => ¬ ClassClear8 N M i d)

/-- **The rung budget.**  At the flank `N·M` (not required to be a disparity): if the blocked units,
counted over the disparities, number fewer than `φ(N)`, some unit `i` is blocked by none, and the
instant `i/N + 1/(8·N·M)` is lonely. -/
theorem lonely_eight_of_rung_budget {S : Finset ℕ} {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (hbud : ∑ d ∈ S, (rungBlocked N M d).card < N.totient) :
    ∃ t : ℝ, 0 < t ∧ ∀ d ∈ S, (8 : ℝ)⁻¹ ≤ circDist ((d : ℝ) * t) := by
  classical
  have hcard : (S.biUnion (rungBlocked N M)).card < (rungUnits N).card :=
    lt_of_le_of_lt Finset.card_biUnion_le (by rwa [card_rungUnits])
  obtain ⟨i, hiU, hiB⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  refine lonely_eight_of_rationalOpening (i := i) hN hM fun d hd => ?_
  by_contra h
  exact hiB (Finset.mem_biUnion.mpr ⟨d, hd, Finset.mem_filter.mpr ⟨hiU, h⟩⟩)

/-- **The link lemma.**  If `N ∣ d' − c·d`, then at every opening `a = 8·(i·M) + 1` of the rung
`(N, M)`, `d'·a ≡ c·(d·a) + (d' − c·d)` modulo `8·N·M`: the difference `(d' − c·d)·(a − 1)` is
`(d' − c·d)·8·i·M`, a multiple of `8·N·M`. -/
theorem link_reading (N M i : ℕ) {d d' c : ℤ} (h : (N : ℤ) ∣ d' - c * d) :
    d' * (8 * (i * M) + 1) ≡ c * (d * (8 * (i * M) + 1)) + (d' - c * d)
      [ZMOD 8 * ((N : ℤ) * M)] := by
  rw [Int.modEq_iff_dvd]
  obtain ⟨k, hk⟩ := h
  exact ⟨-(k * i), by linear_combination (-(8 * (i : ℤ) * M)) * hk⟩

/-- **A linked pair is blocked together, up to the offset.**  With `N ∣ d' − c·d`, the reading of
`d'` at every opening of the rung is fixed by the reading of `d` and the constant `d' − c·d`. -/
theorem link_reading_emod (N M i : ℕ) {d d' c : ℤ} (h : (N : ℤ) ∣ d' - c * d) :
    d' * (8 * (i * M) + 1) % (8 * ((N : ℤ) * M)) =
      (c * (d * (8 * (i * M) + 1) % (8 * ((N : ℤ) * M))) + (d' - c * d)) % (8 * ((N : ℤ) * M)) := by
  have := link_reading N M i h
  rw [Int.ModEq] at this
  rw [this]
  exact (((Int.mod_modEq _ _).mul_left c).add_right _).symm

end LRC.OrderEightN
