# The flank bridge, and why I cannot close Existence

Pushing the largest-flank route to its conclusion. **It does not close.** What follows is what the
push produced, and exactly where it stops.

## Proved: the two languages are one

§6.8 works in flanks and openings; §13–§14 work in candidates `A = 8k+1` and `blocks`. The bridge is
an identity:

```
    ρⱼ·(k + 1/8) = (dⱼ/e)·((8k+1)/8) = dⱼ·A / (8e)
```

so "within `1/8` of an integer" is exactly `blocks dⱼ A e`. **Checked on 19,971 random `(e, d, k)`:
0 mismatches.** `FlankBridge.inWay_mod` (Lean, `[propext]` only) proves the residue invariance that
makes the two descriptions the same object.

**This reconciles an apparent conflict in the record.** The rule *"take the largest reading"* was
refuted with 794 counterexamples, while the largest **flank** is observed always clear. The tests
differ: the refutation searched only `s ≤ A ≤ 7s` — band 0, `R ≤ 7` — whereas a flank admits every
`k ≥ 0`. The counterexamples are profiles needing a witness **above band 0**, not shadowed flanks.

## Corrected: high `|J|` is the easy case, not the hard one

`FLANK_J3_v1` treated `|J| ≥ 3` as the open region. Measured over 221,374 live flanks, the shadow rate
by `|J|`:

| `|J|` | 0 | 1 | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|---|---|
| shadowed | 0% | 0% | 8.58% | **13.89%** | 9.47% | 2.96% | **0.36%** |

**The rate peaks at `|J| = 3` and falls.** And the largest flank always carries `|J| = 6` — the
maximum — because every other ratio there satisfies `0 < |ρ| < 1` and so is non-integer. My framing
had it backwards.

## Where the push stops, precisely

The largest flank's distinguishing feature is **`|ρⱼ| ≤ 1` for all `j`**, not its mover count — 740
other `|J| = 6` flanks do shadow. So the claim is: *a flank with every `|ρ| ≤ 1` is clear.*

Attacked in **ratio space** rather than arrangement space: 200,000 random 6-sets of rationals in
`(−1,1)` with denominators `≤ 6` gave **0 shadowing sets**, and adversarial hill-climbing reached
first-clear index 17 there, 91 from arrangements.

**Both mechanisms I proposed for it are dead:**

1. **Counting fails.** At the largest flank there are six movers, each with bad-set density exactly
   `1/4` (half-width `1/(8|ρ|)`, spacing `1/|ρ|`, independent of `ρ`). Six give `6/4 = 1.5 > 1`.
2. **The `|ρ|` estimate was wrong by two orders of magnitude.** Estimating the first clear index as
   `1/(8|ρ_min|)` gives `≈ 0.64` on the arrangement where the observed value is `91`.

So the claim has no mechanism, only evidence.

## The obligation, in Lean

`FlankBridge.LargestFlankClear` states it as a `Prop`: if every difference is bounded by `e` in
absolute value, some opening `k ≥ 0` clears the flank. It is a definition, **not a theorem** — written
so the gap sits in Lean where it can be discharged, rather than in prose where it can be mistaken for
a result. This is the same device as `RCapObligation`.

## Status, stated plainly

**Existence at order 8 is not proved, and this route does not prove it.**

`[PROVED]`: `FlankBridge.inWay_mod`, axiom-clean; witness now 72 declarations.
`[VERIFIED]`: the largest flank clear in 48,000 subjects, adversarial search to index 91, 200,000
ratio-space sets, five structured families — no shadowed case found.
`[OPEN]`: the claim, its mechanism, and any index bound.
`[CORRECTED]`: `|J| ≥ 3` is not the hard region; the shadow rate peaks at `|J| = 3` and the maximum
`|J| = 6` is the safest.
