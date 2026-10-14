import LonelyRunner.LRC.ConstructionN.LemmaPass

/-! # Only a colliding disparity can block exactly

The open region at order 8 is the **colliding** subjects — those with some disparity divisible by
`8g`, who fail every grid instant and must cascade. Measured over 6,370 such subjects
(`colliding_setters_v1.py`, `_v2.py`): colliding disparities are 19.2% of the pack but **31.3% of
setter events** and **27.3% of final setters**, and the effect survives controlling for size
(1.38×–2.64× by rank, pooled **1.93×**), so it is a residue effect and not a size effect.

The mechanism turns out to be exact, not statistical. A cascade scale is `D = c·g/(8N+1)` for some
disparity `c·g`, so a blocker `a·g` has reading

```
    s = d/D = a(8N+1)/c
```

and blocks when `|s − 8M| < 1`. `exact_block_is_colliding` says that if the reading is *exactly* a
multiple of `8`, the blocker is colliding — because `8N+1` is odd, so `8 ∣ a(8N+1)` forces `8 ∣ a`.

Measured: **81.3%** of colliding blocking events are exact; non-colliding blocks are exact **0 of
12,152** (`colliding_mechanism_v1.py`). The zero is this theorem, not a sample.

Development file. This characterises *how* colliding disparities drive the cascade; it does not
bound depth, and `NEIGHBOUR_DEFORMATION_v2` §6 measured depth as not determined by residues. -/

namespace ExactBlock

/-- `8` is coprime to any `8N+1`. -/
theorem isCoprime_eight (N : ℤ) : IsCoprime (8 : ℤ) (8 * N + 1) :=
  ⟨-N, 1, by ring⟩

/-- **An exact block is always a colliding disparity.**  If the reading `a(8N+1)/c` of a blocker
`a·g` at a cascade scale `c·g/(8N+1)` is exactly `8M`, then `8 ∣ a` — the blocker sits on a
multiple of `8` in reduced coordinates, i.e. it shares the subject's residue mod `8`. -/
theorem exact_block_is_colliding {a c N M : ℤ} (h : a * (8 * N + 1) = 8 * (M * c)) :
    (8 : ℤ) ∣ a :=
  (isCoprime_eight N).dvd_of_dvd_mul_right ⟨M * c, h⟩

/-- Contrapositive, in the form the cascade uses: a non-colliding disparity never reads an exact
multiple of `8` at any cascade scale, so it can only ever block *near* one. -/
theorem noncolliding_never_exact {a c N M : ℤ} (ha : ¬ (8 : ℤ) ∣ a) :
    a * (8 * N + 1) ≠ 8 * (M * c) :=
  fun h => ha (exact_block_is_colliding h)



/-! ## The non-exact colliding blocks are characterised too

Owner: *"the rest must occur for a reason. It's not like they change if we run them again."* The
81.3% / 18.7% split is a deterministic arithmetic partition, so here is the partition.

With `r = b(8N+1) mod c`, the colliding blocker `8b·g` at scale `c·g/(8N+1)` reads `s = 8b(8N+1)/c`
and blocks when `min(r/c, 1−r/c) < 1/8`:

```
  r = 0            EXACT block                 (c ∣ b(8N+1))   -- 4314 events
  0 < r < c/8      near block, s above 8M                      --  260 events
  7c/8 < r < c     near block, s below 8M                      --  731 events
```

`r = 0 ⟺ exact` holds 5305 of 5305 (`colliding_mechanism_v2.py`). And `near_block_host_large`
below says a **near** block forces `c > 8` — with `r ≥ 1` an integer, `8r < c` or `8(c−r) < c` each
give `c > 8` directly. Measured: zero violations, and the smallest `c` among near blocks is exactly
`9`.

So: **if the host disparity is `≤ 8` in reduced units, every colliding block is exact.** -/

/-- **A near (non-exact) colliding block forces a large host.**  If the residue `r` of `b(8N+1)`
mod `c` is nonzero yet lands within `c/8` of either end, the host disparity `c` exceeds `8`. -/
theorem near_block_host_large {c r : ℤ} (hr0 : 0 < r) (hrc : r < c)
    (hnear : 8 * r < c ∨ 8 * (c - r) < c) : 8 < c := by
  rcases hnear with h | h <;> omega

/-- Contrapositive: a host disparity of `8` or less admits only exact colliding blocks. -/
theorem small_host_forces_exact {c r : ℤ} (hc : c ≤ 8) (hr0 : 0 < r) (hrc : r < c) :
    ¬ (8 * r < c ∨ 8 * (c - r) < c) :=
  fun h => absurd (near_block_host_large hr0 hrc h) (by omega)

end ExactBlock
