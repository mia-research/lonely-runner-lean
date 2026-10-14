# Depth is a cell-wise constant function, and the cell walls are band edges

**Owner:** *"we haven't found the cause yet, just means we need to try other things to perturb it."*

Perturbing **resolution** — the one parameter not yet varied — found it, and corrected a claim I had
made twice.

---

## 1. The correction: "23 is a knife-edge" was an artifact of integer steps

Depth is scale-invariant, so scaling the baseline by 10 and stepping by 1 views the *same* function
at 10× resolution. At that resolution:

```
   25.0 – 29.8 : depth 18
   29.9 – 30.4 : depth 23      <- a PLATEAU of width ~0.6, not a spike
   30.5 – 31.0 : depth 18
   31.1 – 31.9 : depth 19
   32.0 +      : depth 0
```

Only **four distinct values** across the whole scan: `{0, 18, 19, 23}`. Depth is a **step function
with wide plateaus**, not a wild arithmetic function. I called 23 a knife-edge in
`DEPTH_RESPONSE_v1` §2 and repeated it; that was integer-grid aliasing, and it is withdrawn.

## 2. The walls are exact rationals of band-edge form

Bisecting each transition to the exact boundary:

```
   18 → 23  at  c* = 1225/41 = 29.878049…
   23 → 19  at  c* = 1431/47 = 30.446809…
   19 → 18  at  c* =  518/17 = 30.470588…
```

Small denominators, and two factor immediately into the **band-edge form** `c = e(8M ± 1)/(8N + 1)`
with `e` an actual disparity:

```
   1225/41 = 175 · 7/41      175 a disparity,  7 = 8·1 − 1,  41 = 8·5 + 1
    518/17 =  74 · 7/17       74 a disparity,  7 = 8·1 − 1,  17 = 8·2 + 1
```

Tracing either side of `518/17` confirms the event directly: below the wall the blocker set is
`{175}`; above it is `{c, 175}` — **`c` itself crosses into the bad band** of the scale hosted by
`74` at `N = 2`, lap `M = 1`. That is the wall.

The middle wall `1431/47` is a *later*-step event: `c` is the setter on both sides, so the
divergence at step 18 is the continuous effect of `c` on the scale it sets, with the discrete
crossing occurring further down the trajectory. Its `e` is a derived scale, not an original
disparity, which is why it does not factor against the seven.

## 3. So the cause of depth 23

```
  depth 23  ⟺  c ∈ (1225/41, 1431/47),  the others fixed
  cell width = 1096/1927 ≈ 0.5687,  about 1.9% of c
```

Its left wall is where `c` enters the bad band of the `175`-hosted scale at `N = 5`, `M = 1`. That
is a cause, and it is exact.

## 4. The general shape this implies

Depth is constant on the cells cut out by the band-edge hypersurfaces

```
      a_i  =  e (8M ± 1) / (8N + 1)
```

over disparities `a_i`, visited scales `e`, and integers `M, N`. **Deep cases are cells, not
points** — so they have positive width and can be hit by construction, which is why band-directed
search worked.

This is the framework's own object: *cells decided by interior points* is BSM vocabulary, and the
walls here are exactly clear-interval endpoints. Depth being cell-wise constant is the statement
that the cascade's combinatorics are fixed inside a cell.

## 5. What this does and does not settle

**Does.** It replaces "depth spikes unpredictably" with "depth is constant on cells whose walls are
exact band edges", gives the walls of the depth-23 cell in closed form, and explains why deep cases
are constructible in the aggregate (they are regions) while remaining unpredictable in detail (which
cell has which depth is still the cascade's arithmetic).

**Does not.** It does not bound depth, and it does not bound the *number* of cells — a bound on
either would be `CascadeCapped`, hence Existence. It also does not predict a cell's depth from its
walls; §2's middle wall shows walls can come from arbitrarily deep in the trajectory.

## 6. Scope

Figures are exact — one fixed disparity set, boundaries bisected to rationals and verified by
retracing either side. The step-function picture is established on this scan (`c ∈ [25, 34]`, the
other six disparities fixed); it is not shown that depth is cell-wise constant in general, only that
it is here and that the walls found have band-edge form.

```bash
python3 experiments/n8/fine_scan_v1.py   # the 0.1-resolution step function
python3 experiments/n8/fine_scan_v2.py   # bisection to 1225/41, 1431/47, 518/17
python3 experiments/n8/fine_scan_v3.py   # the band-edge identity and the blocker-set flip
```
