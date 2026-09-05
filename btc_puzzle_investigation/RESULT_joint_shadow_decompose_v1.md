# Joint (x,y) shadow — reproduction + μ6-parity decomposition of the v16 "0.93"

Date: 2026-07-18. Script `joint_shadow_decompose_v1.py`. Object = the aligned joint
twisted-sum readout of `masked_structure_findings_v16.md` ("the shadow", 0.93 joint vs
0.34 x-only). Model curves `E: y²=x³+7` (CM, j=0), prime order, enumerable d:
p∈{163, 349, 433, 577}. a₀=1 fixed.

Definitions. `U(a₀,b,c)=Σ_{d=1..n-1} e_n(a₀d) e_p(b·x_d+c·y_d)`. Aligned readout on
frequency support S: `Fhat=U/|U|` on S (unit modulus), point-space
`F(P)=Σ_{(b,c)∈S} Fhat(b,c) e_p(−bx−cy)`. `Corr=(1/(n-1))Σ_d F(P_d) e_n(a₀d)`.
Three normalizations reported: `rho2=|Corr|/‖F‖₂`, `rho_inf=|Corr|/‖F‖_∞` (both from the
**true point-space** norms), and `M1=|Corr|/√n` (the printout in v16's code).

## Controls (all fired, every prime)
- **C1 planted perfect leak** `F:=e_n(a₀d)` → `rho2=rho_inf=1.0000`. Pins the scale: a
  perfect leak reads 1.0 (a wrong normalization cannot pass this).
- **C2 random unit-phase point-fn** → rho2 at the `√(1/(n-1))` floor.
- **C3 even/odd cross-orthogonality** `⟨F_even,c_odd⟩=⟨F_odd,c_even⟩=0` → 1e-12…1e-15 (exact).
- **POWER graded plant** `F=α·e_n(a₀d)+(1−α)·rand` → rho2 = 1.00 / 0.92 / 0.71 / 0.37 / 0.18 / 0.04
  across α = 1.0 / 0.7 / 0.5 / 0.3 / 0.15 / 0.0 (monotone, calibrated).

## Reproduced — first actual reproduction of the 0.93 in-thread
| p | sep `rho_inf` | joint `rho_inf` | sep `rho2` | joint `rho2` | even(x) | odd(y) |
|---|---|---|---|---|---|---|
| 163 | 0.344 | 0.934 | 0.670 | 0.999 | 0.500 | 0.499 |
| 349 | 0.365 | 0.953 | 0.673 | 1.000 | 0.498 | 0.502 |
| 433 | 0.339 | 0.952 | 0.663 | 1.000 | 0.498 | 0.502 |
| 577 | 0.288 | 0.960 | 0.659 | 1.000 | 0.499 | 0.501 |

**v16's 0.93 (joint) / 0.34 (x-only) = `rho_inf` (true sup-norm), reproduced** across four
primes (joint 0.93–0.96, sep 0.29–0.36). So v16's stated metric `|Corr|/‖F‖_∞` was the real
one; the code's `/√n` printout is `M1` (= 1.0 sep / 169–481 joint — not the headline) and its
`norm_inf=Σ|Fhat|` is a coefficient **count**, not a norm. The headline number is real, under
the true point-space sup-norm.

## μ6-parity decomposition — FORCED vs measured (protocol separation)
The joint alignment splits **50.0% even-in-d (x-carried) / 49.9% odd-in-d (y-carried)**, in phase.

- **FORCED (report, do not credit as structure):** joint `rho2≈1` ⇒ F is nearly parallel to the
  character c=e_n(a₀·); c's own energy is exactly half even (‖cos‖²=½) and half odd (‖sin‖²=½);
  so F∥c splits 50/50 mechanically. The equal split is arithmetic, not a discovered symmetry.
- **UNFORCED / measured:**
  - The even-in-d subspace = **all** x-only readouts (x_d ↔ ±d bijectively). Its exact L2 ceiling
    is `‖c_even‖ = 1/√2 = 0.7071`; the L2-optimal x readout (c_even=cos) attains it.
  - The v16-style unit-modulus aligned x-readout attains **0.665** = **94%** of that ceiling
    (stable across p). The 6% gap is unit-modulus alignment vs L2-optimal, not a subspace limit.
  - The remaining half of c's energy is the odd-in-d subspace, reachable only through y
    (y_{−d}=−y_d). The joint readout adds it → `rho2`=0.999.
- **v16's "y roughly triples it" (0.93/0.34 = 2.7×) is a sup-norm spikiness artifact:** joint and
  x-only readouts have different `‖F‖_∞/‖F‖₂`. In honest L2 energy the even:odd split is **1:1**
  and the joint/sep ratio is **1.5×**, not 2.7×.

## Scope / power
- Enumerable model primes p ≤ 577, single CM family y²=x³+7. secp (order ≈ 2²⁵⁶) is not
  enumerable; this characterizes the object, not secp-specific magnitudes.
- The readout is `Fhat=U/|U|`, a function of the twisted sum `U(a₀,·,·)`. No exploitability is
  assessed here — object structure only (analysis is downstream).
- Corrects: `RESULT_outside_symmetry_v2/v3` (invariant side) and `RESULT_anti_invariant_probe_v1`
  (odd-y single-coordinate side) both worked the SINGLE-coordinate axis; this is the JOINT object
  those did not reach.

## Next probe (decidable, not a closure)
μ3-weight (CM/GLV) refinement inside the even and odd subspaces: partition (b,c) by the GLV
action b↦βb and re-measure the alignment per weight w∈{0,1,2}. Question: is the even subspace's
0.665 spread flat across w, or does one μ3-sector carry a disproportionate share? Same machinery,
same C1/C3 controls.
