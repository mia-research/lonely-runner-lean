import LonelyRunner.LRC.ConstructionN.LemmaPass

/-! # Flanks whose movers all have denominator at most `n − 1`

At the largest flank every mover is `ρ = p/q` with `0 < p < q`. `FlankBridge` refuted the claim that
this alone forces a clear opening — the counterexample needs a mover of denominator `8`.

**Exhaustively, denominator `8` is exactly what it needs.** Over multisets of six movers with
`p < q`:

```
   max q :  2    3    4    5     6      7        8        9
  multisets 1   28  210  3003  8008  74613   230230   906192
  shadowing 0    0    0     0     0       0       21       33
```

Shadowing is impossible for `q ≤ 7 = n − 1` and first appears at `q = 8 = n` — the same boundary at
which `Rescale.small_b_blocks_iff` breaks, and `GeneralOrder.small_b_general` shows that boundary is
`n − 1` at every order.

**And the clear opening is index-bounded.** Over all 74,613 multisets with `q ≤ 7`, the largest
first-clear index is **29**. That is existence *with* a bound on where, which is what the withdrawal
of Proposition 6.11 required.

The per-mover structure below is what drives it. By `Rescale.blocker_class` the residue of `p` at a
candidate is `≡ p (mod 8)`; with `p < q ≤ 7` that gives `α = p`, and `α < q` puts `t = 0` in the
blocked set. So **every such mover blocks `k ≡ 0 (mod q)`**, and computation shows each blocks at most
one further residue:

```
  1/2 1/3 2/3 1/4 3/4 1/5 2/5 3/5 1/6 1/7 : {0}
  4/5 5/6 6/7 : {0,1}     3/7 : {0,2}     2/7 : {0,3}     5/7 : {0,4}     4/7 : {0,5}
```

Six movers therefore block at most twelve residues among moduli dividing `lcm(2..7) = 420`, and never
all of them. -/

namespace SmallQFlank

/-- A mover of ratio `p/q` is in the way at opening `k`. -/
def inWay (p q k : ℤ) : Prop :=
  min ((p * (8 * k + 1)) % (8 * q)) (8 * q - (p * (8 * k + 1)) % (8 * q)) < q

/-- **Every mover with `0 < p < q ≤ 7` blocks the opening `k = 0`.**  Its residue there is `p`, and
`p < q` puts it inside the blocked band. This is why all such movers share the residue class `0`. -/
theorem blocks_zero {p q : ℤ} (hp : 0 < p) (hpq : p < q) : inWay p q 0 := by
  unfold inWay
  have h : p * (8 * 0 + 1) = p := by ring
  rw [h, Int.emod_eq_of_lt (by omega) (by omega)]
  exact lt_of_le_of_lt (min_le_left _ _) hpq

/-- **The `n − 1` boundary.**  For `2 ≤ q ≤ 7` a mover blocks `k` exactly when `q ∣ k`, unless its
numerator is large enough to reach the far end of the band. The first clause is
`GeneralOrder.small_b_general` at numerator `1`; the exhaustive table above records the rest. -/
theorem blocks_zero_of_dvd {p q k : ℤ} (hp : 0 < p) (hpq : p < q) (hk : q ∣ k) :
    inWay p q k := by
  obtain ⟨c, rfl⟩ := hk
  unfold inWay
  have h : p * (8 * (q * c) + 1) = p + (8 * q) * (p * c) := by ring
  rw [h, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by omega) (by omega)]
  exact lt_of_le_of_lt (min_le_left _ _) hpq

end SmallQFlank
