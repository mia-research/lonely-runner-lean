# The five unexplored consequences, explored

From `THEOREM_INTERACTIONS_v1` §4. Outcome: **one large positive, one uniformity, three negatives.**
The negatives are recorded as findings, not omissions.

---

## Item 1 — the k=1 rung ✅ **and it generalises much further than asked**

The question was whether depth ≤ 1 reduces to a residue band like depth 0. Working it out shows
`clear_iff` **was never about `d_min`**.

A cascade scale is `D = e·g/(8N+1)`, where disparity `a·g` reads `a(8N+1)/e`. Blocking is
`|a(8N+1) − 8Me| < e` — which is `clear_iff`'s statement with `a ↦ a(8N+1)` and `c ↦ e`. So:

> **clear at scale `e/(8N+1)` ⟺ for every disparity `a`,  `e ≤ a(8N+1) mod 8e ≤ 7e`**

`DminClearance.clear_at_scale_iff` — *literally `clear_iff` at different arguments*, which is why it
is a one-line proof. Verified against the cascade at **every scale it visits**: **46,353 / 46,353**.

**The cascade is therefore a sequence of applications of one residue-band test**, with the host `e`
and multiplier `8N+1` updating at each move. The depth stratification that follows:

```
  k=0  0.5298      k≤1  0.7476      k≤2  0.8795      k≤3  0.9496      k≤4  0.9772
```

So the k=1 rung exists and is the same band; what is *not* resolved is a closed form for which
`(e, N)` the move lands on, which is where the max over blockers sits.

## Item 2 — does general `slot_gcd` simplify the n=7 tree? ❌ **No**

The tree never states BS eq. (2) (`ν(λx) = ν(x)`). It carries the level as **divisibility
hypotheses** `7^j ∣ d` — 9 occurrences in `PrimeFiltering.lean`, 3 in `Defs.lean` — which are
preserved trivially under multiplication by a multiplier. `slot_gcd` is the stronger gcd identity,
and the tree has no place that needs it. No simplification available.

## Item 3 — does the cage improve Localisation's bound? ❌ **No**

`ConstructionN.localisation_free` (`LemmaPass.lean:404`) is a **windowing** statement: given `1 ∈ S`,
whole-lap shift invariance confines the instant to `[1/n, 1−1/n]`. It contains no per-runner slack
bound. The cage bounds *distances at grid instants*; `localisation_free` bounds *the instant*.
Different objects, nothing to sharpen.

## Item 4 — what does `clear_of_reading_le_gen` say at closed orders? ✅ **Uniform across `n`**

```
   n   clear at d_min   S ≤ n−1   S ≤ n−1 ⟹ clear
   3        0.6330       0.4637     0 violations
   4        0.5864       0.3829     0 violations
   5        0.5708       0.3498     0 violations
   6        0.5505       0.3233     0 violations
   7        0.5584       0.3149     0 violations
   8        0.5538       0.3088     0 violations
```

The implication holds at every order, as the theorem requires. The clear rate is **stable near
0.55–0.63** across orders — the fraction of subjects needing no cascade at all barely moves with `n`.

**Honest scope:** `n = 3..7` are closed, so this is not new mathematics there. What it is, is a
*uniform* statement those individual proofs do not have — one criterion, one constant `n−1`, every
order. Whether that uniformity is useful is not established.

## Item 5 — the failure-count ceiling ❌ **negative on the interesting part**

`d_min` never fails, so at most `n−2` of the `n−1` disparities can. The hoped-for consequence was
that a **single** failure makes the first move forced (a max over one candidate), which might make
the k=1 rung more tractable for that class. Measured:

```
  exactly one failure : 7387 subjects, depth == 1 in 0.4620
  two or more         : 3913 subjects, depth == 1 in 0.4833
```

**No difference.** The move being forced does not make clearance more likely — if anything slightly
less. The structural point survives (the first move is deterministic for ~65% of failing subjects,
which simplifies analysis) but it buys no probability.

Incidental: this sample contained **one 6-failure subject**, confirming by sampling what
`dmin_balance_v2.py` had to construct, and confirming the ceiling is attained rather than merely
attainable-in-principle.

---

## What this leaves

The one thing worth pursuing from these five is **Item 1's residual**: the band test is uniform
across scales, so the cascade's whole trajectory is a sequence of one test — but which `(e, N)` the
move selects is a max over blockers and has no closed form yet. That max is now the only unexplained
step in the recursion.

Nothing here proves anything at order 8, and the depth figures are from one sampler (speeds `1..89`,
24,000 subjects; orders 3–8 from speeds `1..59`, 4,000 arrangements each).

```bash
cd LonelyRunner && lake env lean ../experiments/n8/DminClearance_v1.lean   # 8 thms
python3 experiments/n8/scale_criterion_v1.py   # 46,353/46,353 at every scale
python3 experiments/n8/items_4_5_v1.py         # orders 3..8; the single-failure class
```
