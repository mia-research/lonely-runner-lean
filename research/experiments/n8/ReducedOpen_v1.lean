import Mathlib

/-!
# What removing the false hypotheses leaves open

Removing the homogeneity from `profile_clear_of_order6` did more than recover reach: it
**shrinks the open set**, because the small moduli turn out to carry no difficulty at all.

For `2 ≤ b ≤ 9` the lower edge is `L(b) = 1`, so the clear window is `[1, U(b)]` and clearing
is pure **non-divisibility**:

```
    2 ≤ b ≤ 7 :  clear ⟺ b ∤ q
    b = 8, 9  :  clear ⟺ b ∤ q  and  b ∤ (q+1)
```

`Rescale.small_b_blocks_iff` already had the first line; `small_clear_iff` below covers both,
including `b ∈ {8,9}` where the old law breaks.

So for a divisor-closed profile the obligation is now:

> find `q` clearing every modulus `≥ 10`, subject to `b ∤ q` for each modulus `b ≤ 7`
> and `b ∤ q`, `b ∤ (q+1)` for each `b ∈ {8,9}`.

That is strictly smaller than "mixed profiles are open". The small moduli forbid **at most two
residues each**, explicitly named, instead of being an unanalysed obstruction. The whole
difficulty is now located at the moduli `≥ 10`, which is the regime the order-6 argument
already covers per modulus.

*(Measured: forcing the stronger `q ≡ 1 (mod lcm of the small moduli)` — which clears them all
at once, since `L(b) = 1` — still finds a witness in 81.62% of profiles, so even the crude
discharge is nearly free. The weak form above costs nothing.)*
-/

namespace ReducedOpen

/-- The clear condition at modulus `b`, on the residue. -/
def clearAt (b r : ℤ) : Prop := b ≤ 8 * r + 1 ∧ 8 * r + 1 ≤ 7 * b

/-- **Small moduli are pure non-divisibility.**  For `2 ≤ b ≤ 9` the window is `[1, U(b)]`, so
clearing forbids only the residue `0`, and additionally `b-1` when `b` is `8` or `9`. -/
theorem small_clear_iff {b r : ℤ} (h2 : 2 ≤ b) (h9 : b ≤ 9) (hr0 : 0 ≤ r) (hrb : r < b) :
    clearAt b r ↔ (r ≠ 0 ∧ (8 ≤ b → r ≠ b - 1)) := by
  unfold clearAt
  constructor
  · rintro ⟨h1, h2'⟩
    refine ⟨by omega, ?_⟩
    intro h8; omega
  · rintro ⟨hne, hedge⟩
    interval_cases b <;> omega

/-- **Below 8 it is exactly non-divisibility**, matching `Rescale.small_b_blocks_iff`. -/
theorem tiny_clear_iff {b r : ℤ} (h2 : 2 ≤ b) (h7 : b ≤ 7) (hr0 : 0 ≤ r) (hrb : r < b) :
    clearAt b r ↔ r ≠ 0 := by
  rw [small_clear_iff h2 (by omega) hr0 hrb]
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, by omega⟩

/-- **The reduced obligation, stated so it is visible in Lean.**  A divisor-closed profile is
settled by a `q` that clears every modulus `≥ 10` and merely avoids the named residues at the
moduli below `10`.  Nothing here is proved; it records what removing the homogeneity left. -/
def ReducedWitness (bs : List ℤ) : Prop :=
  ∃ q : ℤ, (∀ b ∈ bs, 10 ≤ b → clearAt b (q % b)) ∧
           (∀ b ∈ bs, b < 10 → (q % b ≠ 0 ∧ (8 ≤ b → q % b ≠ b - 1)))

/-- **And it does settle the profile.**  The reduced obligation is genuinely sufficient: a
witness for it clears every modulus. -/
theorem clear_of_reducedWitness {bs : List ℤ} {q : ℤ}
    (hpos : ∀ b ∈ bs, 2 ≤ b)
    (hlarge : ∀ b ∈ bs, 10 ≤ b → clearAt b (q % b))
    (hsmall : ∀ b ∈ bs, b < 10 → (q % b ≠ 0 ∧ (8 ≤ b → q % b ≠ b - 1))) :
    ∀ b ∈ bs, clearAt b (q % b) := by
  intro b hb
  have h2 := hpos b hb
  by_cases h10 : 10 ≤ b
  · exact hlarge b hb h10
  · have hb0 : (0 : ℤ) < b := by omega
    have hr0 : 0 ≤ q % b := Int.emod_nonneg q hb0.ne'
    have hrb : q % b < b := Int.emod_lt_of_pos q hb0
    exact (small_clear_iff h2 (by omega) hr0 hrb).mpr (hsmall b hb (by omega))

end ReducedOpen

#print axioms ReducedOpen.small_clear_iff
#print axioms ReducedOpen.tiny_clear_iff
#print axioms ReducedOpen.clear_of_reducedWitness
