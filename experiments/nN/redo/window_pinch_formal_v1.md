# Fixed-lap windows and first pinch: Lean formalization

Source: `LonelyRunner/LRC/Spec/WindowPinchN.lean`.
Audit and exact regressions: `experiments/nN/window_pinch_axioms_v1.lean`.

## Proved

- A finite family of closed intervals intersects iff every lower endpoint is
  below every upper endpoint, equivalently maximum lower <= minimum upper.
- For positive subject disparities d_i and specified integer laps q_i, the
  clear bands intersect iff
  `(8*q_i+1)*d_j <= (8*q_j+7)*d_i` for every pair i,j.
- For an injective eight-speed arrangement and nonnegative laps, those
  inequalities produce a positive time satisfying the existing
  `Arrangement.LonelyAt` predicate. Absolute disparities treat both directions.
- The rescaled AP window criterion is exact for its specified laps. A positive
  scale exists iff every `rho_i/U_i <= rho_j/L_j`. The AP-window-to-reading
  identity connects these inequalities to ordinary lap bands.
- Along an order-preserving straight deformation, each absolute-disparity
  ratio is exactly `1+s*beta_i`. Boundary ordering for s>0 depends only on
  the beta values, not the magnitude of s.
- Every pairwise scale slack is exactly `A_ij+s*B_ij`. If some slope is
  negative and all initial slacks are nonnegative, a finite minimum selects
  the first pinching pair with parameter `tau=A_ij/(-B_ij)`.
- `first_scale_pinch` proves that, wherever disparities remain positive and
  s>=0, the specified windows are feasible exactly when s<=tau. If all
  slopes are nonnegative, no subsequent pinch occurs on that ray.

Equality endpoints, simultaneous roots, and tau=0 are retained. On a deformation
restricted to [0,1], a computed root beyond 1 is not a failure on the segment.

## Not asserted

No theorem here says another lap assignment restores isolation after the pinch.
There is no finite quotient of all future cascade histories and no global
termination theorem. The finite minimum is over the endpoint constraints of ONE
fixed lap assignment, not over unbounded lap histories.

## Verification commands

```
lake build LonelyRunner.LRC.Spec.WindowPinchN
lake env lean experiments/nN/window_pinch_axioms_v1.lean
```

The audit names every theorem in the new module. Exact regression proofs include
a singleton time window, an immediate pinch, tied roots, and isolation at 3/8
for `(0, 99/100, 2, 3, 4, 5, 6, 7)`. That last regression proves the witness,
not the intervening cascade history. These checks are scoped to this module;
they are not a claim that the entire working tree passed the full Spec gate.
