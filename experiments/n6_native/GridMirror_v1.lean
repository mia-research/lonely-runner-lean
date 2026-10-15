import Mathlib

/-!
# The mirror at an integer degenerate point (n6_native, E23)

At integer speeds `D_e, D_l` a lonely point `p` where runner `e` enters (`D_e p = k_e + 1/6`) and runner
`l` leaves (`D_l p = k_l + 5/6`) has the mirror `1 - p`, where `l` enters at lap `D_l - k_l - 1` and
`e` leaves at lap `D_e - k_e - 1`. For perturbed speeds `d_e, d_l > 0` (laps held), the point opens
iff the entry precedes the exit. `mirror_opening`: at `p` that reads `D_e d_l < D_l d_e`, at `1 - p`
it reads `D_l d_e < D_e d_l`. So no perturbation closes both points.
-/

namespace N6Native

theorem mirror_opening {De Dl de dl p : ℝ} {ke kl : ℤ} (hp : 0 < p) (hp1 : p < 1)
    (he : De * p = ke + 1 / 6) (hl : Dl * p = kl + 5 / 6) (hde : 0 < de) (hdl : 0 < dl) :
    ((ke + 1 / 6) / de < (kl + 5 / 6) / dl ↔ De * dl < Dl * de) ∧
    (((Dl - kl - 1 : ℝ) + 1 / 6) / dl < ((De - ke - 1 : ℝ) + 5 / 6) / de ↔ Dl * de < De * dl) := by
  have h1p : 0 < 1 - p := by linarith
  constructor
  · rw [div_lt_div_iff₀ hde hdl, ← he, ← hl]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith
  · rw [div_lt_div_iff₀ hdl hde]
    have e1 : (Dl - kl - 1 : ℝ) + 1 / 6 = Dl * (1 - p) := by linarith
    have e2 : (De - ke - 1 : ℝ) + 5 / 6 = De * (1 - p) := by linarith
    rw [e1, e2]
    constructor
    · intro h; nlinarith
    · intro h; nlinarith

end N6Native

#print axioms N6Native.mirror_opening
