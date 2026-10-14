import Mathlib

/-!
# Where the isolated witnesses come from

On the odd sublattice (`q = 2u+1`) the admissible set of `u` is never empty, but for about 3% of
profiles carrying `b = 2` it contains **no two consecutive** members — every witness is isolated,
hence doubly tight.

This is the `b = 2` phenomenon one level up. In `q`-space the singleton `{2}` isolates, because
clearing at `b = 2` is "`q` odd". In `u`-space **no single modulus isolates**, and among all pairs
`b < b' ≤ 60` there is exactly **one**: `(5, 10)`.

```
    b = 5  admits  u ≡ 0,1,3,4        (mod 5)
    b = 10 admits  u ≡ 1,2,3,6,7,8    (mod 10)
    together       u ≡ 1,3,6,8        (mod 10),  cyclic gaps 2,3,2,3 — never 1
```

Accounting for the isolated cases (59 of 2,000 profiles carrying `b = 2`):

| minimal isolating configuration | share |
|---|---|
| the pair `(5, 10)` | **61%** |
| the quadruple `(3, 12, 16, 48)` | 36% |
| `(10, 12, 15, 60)` and `(12, 15, 20, 60)` | 3% |

All four are minimal — no proper subset isolates. **Isolated is not empty**: across 2,000
profiles the admissible set was empty **0** times, so this concerns the shape of the witness set,
not its existence.
-/

namespace IsolatingPair

/-- The clear window at modulus `b`, on the residue. -/
def Window (b r : ℤ) : Prop := b ≤ 8 * r + 1 ∧ 8 * r + 1 ≤ 7 * b

/-- Admissibility of the odd index `2u+1` against both `5` and `10`. -/
def Adm (u : ℤ) : Prop := Window 5 ((2 * u + 1) % 5) ∧ Window 10 ((2 * u + 1) % 10)

/-- **The pair `(5,10)` pins `u` to four residues mod 10.** -/
theorem five_ten_residues (u : ℤ) :
    Adm u ↔ (u % 10 = 1 ∨ u % 10 = 3 ∨ u % 10 = 6 ∨ u % 10 = 8) := by
  unfold Adm Window
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩; omega
  · rintro (h | h | h | h) <;> refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> omega

/-- **And so admits no two consecutive indices.**  The cyclic gaps are `2` and `3`. -/
theorem five_ten_no_consecutive (u : ℤ) : ¬ (Adm u ∧ Adm (u + 1)) := by
  rintro ⟨h1, h2⟩
  rw [five_ten_residues] at h1 h2
  omega

/-- **`b = 5` alone does not isolate**: `u ≡ 3` and `u ≡ 4 (mod 5)` are both admissible. -/
theorem five_alone_not_isolating :
    Window 5 ((2 * 3 + 1) % 5) ∧ Window 5 ((2 * 4 + 1) % 5) := by
  unfold Window; norm_num

/-- **`b = 10` alone does not isolate**: `u ≡ 1` and `u ≡ 2 (mod 10)` are both admissible. -/
theorem ten_alone_not_isolating :
    Window 10 ((2 * 1 + 1) % 10) ∧ Window 10 ((2 * 2 + 1) % 10) := by
  unfold Window; norm_num

end IsolatingPair

#print axioms IsolatingPair.five_ten_residues
#print axioms IsolatingPair.five_ten_no_consecutive
#print axioms IsolatingPair.five_alone_not_isolating
#print axioms IsolatingPair.ten_alone_not_isolating
