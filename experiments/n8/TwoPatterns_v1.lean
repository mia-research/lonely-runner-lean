import LonelyRunner.LRC.ConstructionN.LemmaPass

/-! # Two inverted patterns, and why they meet four times

The endpoints of the bad intervals form **two patterns**, not one:

* the `+1` pattern — points `x` with `s·x ≡ 1 (mod 8)` for some reading `s` (right endpoints);
* the `−1` pattern — points `x` with `s·x ≡ −1 (mod 8)` (left endpoints).

They are inverted images of one another under time reversal `x ↦ 8 − x`
(`TimeReversal.bad_reflect`). The AP's four global isolation events are exactly the points where the
two patterns **coincide** — and the coincidence is forced by the Klein identity.

For odd `u`: `u·u ≡ 1 (mod 8)`, so `x = u` lies on the `+1` pattern *via reading `u` itself*; and
`u·(8−u) ≡ −u² ≡ −1 (mod 8)`, so the **same point** lies on the `−1` pattern *via reading `8−u`*.

So the two patterns do not pair up points — each of the four points sits on **both** patterns at once,
and the two patterns attribute it to **reflected readings**:

```
    x = 1   +1 endpoint of reading 1      −1 endpoint of reading 7
    x = 3   +1 endpoint of reading 3      −1 endpoint of reading 5
    x = 5   +1 endpoint of reading 5      −1 endpoint of reading 3
    x = 7   +1 endpoint of reading 7      −1 endpoint of reading 1
```

There are four events because there are four units mod `8`. Checked: within `[1,7]`, over every
rational of denominator `≤ 12`, the two patterns coincide at exactly these four points and nowhere
else. -/

namespace TwoPatterns

/-- **The Klein identity forces the coincidence.**  For odd `u`, the point `x = u` lies on the `+1`
pattern through reading `u`, and on the `−1` pattern through reading `8 − u`. -/
theorem unit_on_both {u : ℤ} (hu : u % 2 = 1) :
    (u * u) % 8 = 1 ∧ (u * (8 - u)) % 8 = 7 := by
  have h : u % 8 = 1 ∨ u % 8 = 3 ∨ u % 8 = 5 ∨ u % 8 = 7 := by omega
  have hm1 : u * u % 8 = (u % 8) * (u % 8) % 8 := by rw [Int.mul_emod]
  have hm2 : u * (8 - u) % 8 = ((u % 8) * ((8 - u) % 8)) % 8 := by rw [Int.mul_emod]
  have h8 : (8 - u) % 8 = (8 - u % 8) % 8 := by omega
  rcases h with h | h | h | h <;> rw [hm1, hm2, h8, h] <;> norm_num

/-- **Reflected readings.**  The reading that puts `u` on the `−1` pattern is the time reversal of
the reading that puts it on the `+1` pattern. -/
theorem reflected_reading {u : ℤ} (hu : u % 2 = 1) :
    (u * u) % 8 = 1 ∧ (u * (8 - u)) % 8 = (8 - (u * u) % 8) % 8 := by
  obtain ⟨h1, h2⟩ := unit_on_both hu
  exact ⟨h1, by rw [h1, h2]; norm_num⟩

/-! ## The owed counting statement

`PAIR_STRUCTURE_v1` recorded, as `[VERIFIED — exact]`, that the blocked counts satisfy
`blocked(α') = blocked(8−α')` — so `{1,7}` always agree internally, and `{3,5}` do. That is the
reflection at the level of counts, and it is owed a proof.

It follows from an involution rather than a computation: `v ↦ 8β − v` permutes the residues mod `8β`,
sends the class `α'` to the class `8 − α'`, and leaves `min(v, 8β − v)` — hence blocking — unchanged.
-/

/-- The blocked residues of class `ap` at modulus `b`. -/
noncomputable def blockedSet (ap b : ℤ) : Finset ℤ :=
  (Finset.Ico 0 (8 * b)).filter (fun v => v % 8 = ap ∧ min v (8 * b - v) < b)

/-- **The count reflection.**  `blocked(α')` and `blocked(8 − α')` are equal, by the involution
`v ↦ 8β − v`. This is `{1,7}` agreeing internally, and `{3,5}` likewise. -/
theorem blocked_reflect {b ap : ℤ} (hb : 0 < b) (h1 : 1 ≤ ap) (h7 : ap ≤ 7) :
    (blockedSet ap b).card = (blockedSet (8 - ap) b).card := by
  classical
  refine Finset.card_bij' (fun v _ => 8 * b - v) (fun v _ => 8 * b - v) ?_ ?_ ?_ ?_
  · intro v hv
    simp only [blockedSet, Finset.mem_filter, Finset.mem_Ico] at hv ⊢
    obtain ⟨⟨hv0, hv8⟩, hvm, hvb⟩ := hv
    have hvpos : 0 < v := by
      rcases eq_or_lt_of_le hv0 with h | h
      · exfalso; rw [← h] at hvm; omega
      · exact h
    refine ⟨⟨by omega, by omega⟩, ?_, by rw [show 8*b - (8*b - v) = v by ring]; omega⟩
    omega
  · intro v hv
    simp only [blockedSet, Finset.mem_filter, Finset.mem_Ico] at hv ⊢
    obtain ⟨⟨hv0, hv8⟩, hvm, hvb⟩ := hv
    have hvpos : 0 < v := by
      rcases eq_or_lt_of_le hv0 with h | h
      · exfalso; rw [← h] at hvm; omega
      · exact h
    refine ⟨⟨by omega, by omega⟩, ?_, by rw [show 8*b - (8*b - v) = v by ring]; omega⟩
    omega
  · intro v _; ring
  · intro v _; ring

end TwoPatterns
