# Shared cell dynamics, 2026-10-20

This investigation establishes general relations between failed cells, rather than
another divisibility family. It does **not** close the primitive one-multiple
problem or the exceptional-disparity-divisible-by-32 residual.

## The proved relation

Let `x > 0` be the added disparity and `[u,w]` an eighth-clear base cell. Failure
means that no point in this entire cell clears `x`. The midpoint criterion from
E457 gives the exact equivalent condition

```
circDist(x*(u+w)/2) + x*(w-u)/2 < 1/8.
```

The new proof places the **whole closed cell** strictly in a single open blocked
band, with a unique integer label `q`:

```
q - 1/8 < x*u ≤ x*w < q + 1/8.
```

For ordered failed cells `[u,w]`, `[v,z]`, labelled `q,r`:

1. `q ≤ r`.
2. Writing `E_q(u) = (q+1/8)/x-u`, the exact distance-to-exit transfer is
   `E_r(v)-E_q(u) = (r-q)/x-(v-u)`.
3. If `q=r`, this distance strictly decreases when the opener advances.
4. A band change satisfies
   `x*(v-w) > (r-q)-1/4`, hence `x*(v-w)>3/4` when `r>q`.
5. Each exceptional clear interval
   `[(k+1/8)/x,(k+7/8)/x]`, `q≤k<r`, lies **strictly inside the gap** `(w,v)`.

For adjacent maximal base cells the gap contains no base-clear point. The six
base disparities must therefore collectively block every such exceptional clear
interval. No single base disparity is required to do all this blocking.

The proof also handles the wrap around one integer period. Translating a cell by
one shifts its band label by the integer `x`. Thus a full period of failed cells
must contain a gap longer than `3/(4*x)`. The finite-chain theorem proves this
without a bound on the number of cells. It is a **necessary condition for total
failure**, not a contradiction: actual base-blocked gaps can be this long.

For `x=8c`, a base disparity `d` not divisible by eight cannot share an eighth-band
boundary with `x`. The kernel proves the integer obstruction
`8*c*a ≠ d*(8*q±1)`. This applies to both openers and closers; it excludes exact
coincidence, not strict covering by several blockers.

## What the difficult examples rule out

All observations below use exact integer/Fraction arithmetic. They are bounded
diagnostics, except for the explicitly identified kernel statements.

* **A short fixed chain does not describe all failures.** For primitive base
  `{9,13,28,45,87,125}` and `x=32`, four consecutive cells fail:
  `[41/696,63/1000]`, `[65/696,19/200]`, `[97/1000,7/72]`, and `[1/8,1/8]`.
  Their labels are `2,3,3,4`. The complete exact cell construction verifies
  adjacency. Lean verifies clearance of the whole base on each supplied interval
  and failure of `x` there; adjacency/maximality in this example is diagnostic.
* **Even before the first survivor, two failures is not a general bound.** For
  primitive base `{3,36,45,100,125,233}`, `x=96`, the initial three cells fail:
  `[1/24,1/24]`, `[97/1864,5/96]`, `[49/800,63/1000]`.
  The fourth cell survives at `19/256`. Lean verifies the three failures and the
  full seven-disparity witness. The initial-cell ordering is exact diagnostic.
  E455's maximum of two remains a correct observation about its smaller population.
* **A blocking chain can reuse a disparity.** For `x=32`, the full exceptional
  clear interval `[17/256,23/256]` is blocked by 45 at lap 3, then 13 at lap 1,
  then 45 at lap 4. Lean proves that at every point of this interval either 13 or
  45 is blocked. In particular, the base with the four-failure example supplies
  such a repeated use inside an actual gap.
* A greedy exact bridge can use nine blocking intervals from six disparities:
  base `{121,149,155,178,196,238}`, `x=64`, exceptional lap `14`. The sequence is
  `149,121,178,155,238,149,196,178,121`. This records the greedy construction;
  no universal maximum or minimality theorem is claimed.
* **Clearance at a base opener is insufficient as a universal search rule.** For
  `{1,2,3,4,5,6}` and `x=480`, no base-cell opener clears `x`, although surviving
  cells exist by displacement. This is a fast-case control, not a new difficult
  residual input.

The sample contains 12,000 seeded inputs: six nonmultiples of eight drawn from
`[1,N]`, `N` cycling through `32,64,128,256`, and `x=32*j`, `1≤j≤16`.
Three named controls are added. Total: 12,003 inputs, 11,947 primitive,
1,046,379 base cells, 103,735 failed cells, 10,303 adjacent failed pairs.
The 5,120 adjacent band changes contain 25,222 exceptional clear intervals;
131 greedy bridges reuse a disparity. The exact transfer and containment tests
have no discrepancies. Fraction-based interval and witness controls cover 49
inputs. No input lacks a survivor; no input lacks a surviving full eighth-clear
cell containing a seven-clear instant. This last candidate remains unproved.

## Why the local law is not yet the proof

The proof also supplies artificial periodic failed intervals
`[(q-1/16)/x,(q+1/16)/x]`. They obey the local band laws and still all fail.
They are **not** asserted to be cells generated by six base disparities.
This control shows precisely why monotone progress within a band is insufficient:
band changes can replenish the distance to the exit.

The remaining mathematical work is to constrain those replenishments using the
**same six interval trains**: base disparity `d` contributes the open blocked
intervals `((j-1/8)/d,(j+1/8)/d)` for integer laps `j`. Their phases cannot be
chosen independently in successive exceptional clear intervals. Repetition of a
base reading at different laps must be retained. Neither a fixed bound on chain
length nor the impossibility of a single local bridge can supply that argument.
No theorem excluding all globally compatible blocking chains has been proved.

## Artifacts and reproduction

* Lean: `LonelyRunner/LonelyRunner/LRC/Spec/OrderEightCellDynamicsN.lean`.
  Sixteen public general theorems, plus the private window helper.
* From the nested `LonelyRunner` repo, run
  `python3 scripts/check_order_eight_cell_dynamics.py`.
  The build, exact controls, 16 standard-axiom reports, three transitive dependency
  exclusions, and source fingerprints are recorded under
  `experiments/nN/native_eight_cell_dynamics/`.
* Exact diagnostics, from the parent workspace:
  `python3 experiments/n8/shared_cell_dynamics_v1.py --output experiments/n8/shared_cell_dynamics_v1.json`.
  Seed `20261020`; no floats; sampled scope explicitly recorded in the JSON.

Earlier Lean sources and gates are unchanged. New work is local, uncommitted and
unpushed. `Fresh.SecondStage.OneMultipleCellExists` and full n=8 remain open.
