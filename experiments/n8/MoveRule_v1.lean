import LonelyRunner.LRC.ConstructionN.LemmaPass

/-! # The move is a closed form

`FIVE_ITEMS_v1` §1 left one step in the cascade unexplained: which `(e, N)` the move lands on — the
max over blockers. It is a deterministic argmin, and here is the rule.

At scale `D = e·g/(8N+1)`, disparity `a·g` has reading `s_a = a(8N+1)/e`, and `d·t = s_a/8`.
Blocking means `|s_a − 8M_a| < 1` with `M_a = round(s_a/8)`. The key step — `move_lap` below — is
that the next opening's lap is then **exactly `M_a`**, with no rounding case to consider. So the
candidate scale from blocker `a` is `a·g/(8M_a+1)`, and

```
    D' = D · min over blockers of  s_a/(8M_a+1)        equivalently
    λ  = D/D' = max over blockers of (8M_a+1)/s_a
```

Verified against the cascade: the derived scale matches **18,286 / 18,286** moves
(`move_rule_v2.py`), and the dilation formula `λ = (8M+1)/s` matches 18,286/18,286
(`move_rule_v1.py`). Three of those moves name a *different* blocker — ties producing the identical
scale — so the rule is exact on the scale, which is what the recursion uses.

Two consequences:

* **Every cascade scale is a `candidateScale` with `k = M_a`** — `a·g/(8M_a+1)` is exactly
  `Cascade.candidateScale 8 (a·g) M_a`, so the cascade never leaves that family.
* The ratio is `(8M+δ)/(8M+1)` with `δ = s − 8M ∈ (−1,1)`, increasing in both `M` and `δ`. So
  *"smallest lap wins"* is a good heuristic but **not** a theorem: it holds 97.3%, and fails exactly
  when a later-lap blocker sits far enough *below* its multiple (measured median `δ = −0.50`).

Development file. This explains the recursion's selection step; it does not bound depth. -/

namespace MoveRule

/-- **The next opening's lap is exactly `M`.**  If disparity `a` blocks at scale `e/(8N+1)` — i.e.
its reading `a(8N+1)/e` is within `1` of `8M` — then `M` is the least `k` with `(8k+1)e ≥ a(8N+1)`.
So the move's lap index needs no rounding decision: it is the `M` the blocking condition already
names. -/
theorem move_lap {a e N M : ℤ} (he : 0 < e)
    (hblock : |a * (8 * N + 1) - 8 * (M * e)| < e) :
    a * (8 * N + 1) ≤ (8 * M + 1) * e ∧ (8 * (M - 1) + 1) * e < a * (8 * N + 1) := by
  rw [abs_lt] at hblock
  obtain ⟨hlo, hhi⟩ := hblock
  have e1 : (8 * M + 1) * e = 8 * (M * e) + e := by ring
  have e2 : (8 * (M - 1) + 1) * e = 8 * (M * e) - 7 * e := by ring
  constructor
  · rw [e1]; linarith
  · rw [e2]; linarith

/-- The candidate scale the blocker offers, in reduced units: `a/(8M+1)`.  Combined with
`move_lap`, the move takes the minimum of these over the blockers. -/
theorem candidate_pos {a M : ℤ} (ha : 0 < a) (hM : 0 ≤ M) : 0 < 8 * M + 1 ∧ 0 < a := by
  omega

end MoveRule
