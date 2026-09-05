# μ6-isotype decomposition of the aligned readouts — conservation hunt

Date: 2026-07-18. Script `joint_shadow_mu3_v1.py`. Model curves `E: y²=x³+7`, prime order,
p ∈ {163, 349, 433}. a₀=1. Aut(E)=μ6 acts on d by d↦λd (GLV, λ³≡1 mod n) and d↦−d.
Follows `RESULT_joint_shadow_decompose_v2` (the joint-shadow magnitudes are generic; the
d-specific content is the exact even/odd constraint + the untested isotype pattern — this file
takes the pattern).

## Exact conservations found (each with the symmetry that enforces it)
1. **Coordinate identities** (0 error, β paired to λ from data: β=104/226/234 at the three p):
   `x_{λd}=βx_d`, `y_{λd}=y_d`, `x_{−d}=x_d`, `y_{−d}=−y_d`.  ← the μ6=Aut(E) action on coords.
2. **Cross-isotype orthogonality** `⟨F_w, c_{w'}⟩ = 0` for w≠w' (≤1.6e-15), and even/odd
   cross-parity = 0.  ← μ6 Schur.
3. **Character equipartition.** Energy of c=e_n(a₀d) per μ6-isotype = exactly **1/6** in five
   isotypes; the trivial isotype (w=0, parity +) carries **1/6 − (5/6)/(n−1)** (0.1606 / 0.1640 /
   0.1646, matching the formula at each n). The sole departure from equipartition is the excluded
   point d=0 = **O**, the unique μ6-**fixed point**, which lives in the trivial isotype and whose
   weight → 0 as p→∞.  ← μ6 acting freely on the orbit {±a₀,±λa₀,±λ²a₀}; O the only fixed point.
4. **w1 = w2 exactly** in every readout's weight split (0.2264=0.2264, …).  ← complex conjugation
   ω↔ω² (Galois), exact.

## The posed question: is the x-only 0.665 flat across CM weight w, or concentrated?
**Flat.** Per-weight `|⟨F_w,c⟩|/‖F‖` (channels add in phase ⇒ sum = rho2):

| p | w0 | w1 | w2 | sum (=rho2) |
|---|---|---|---|---|
| 163 | 0.2173 | 0.2264 | 0.2264 | 0.6700 |
| 349 | 0.2149 | 0.2292 | 0.2292 | 0.6734 |
| 433 | 0.2146 | 0.2244 | 0.2244 | 0.6634 |

Each ≈ rho2/3; w1=w2 exact; w0 low only by the fixed-point term. **No CM sector carries more.**
The joint readout (rho2=0.999) is likewise flat: w0=0.331, w1=w2=0.334.

## char vs random per-weight (60-draw ensemble null, statistic = std across w0,w1,w2)
- char weight-imbalance: **0.0043 / 0.0067 / 0.0046**; random: **0.034 / 0.024 / 0.020** (mean±);
  char ≤ random in **0 / 2 / 1** of 60 draws.
- The character's per-weight alignment is far flatter than a random target's — but this is
  **μ6-enforced**: the character's weight energies are exactly equal (conservation #3), so its
  aligned readout distributes exactly flat; a random target's are equal only on average
  (O(1/√n) fluctuation). This is the symmetry showing, not structure outside it.

## Structure map (what this locates and what it does not)
The aligned readout is built from `U`, which is μ6-equivariant (`U(a,b,c)=U(λa,βb,c)`), so its
alignment is **forced** to be fully μ6-symmetric: equipartitioned, flat across CM weights,
cross-isotype-orthogonal, with the only departure the μ6-fixed point O (→0). Per the standing
principle (a μ6-invariant/equivariant readout is constant on the orbit {±d,±λd,±λ²d} and cannot
separate d from it), this symmetric skeleton is exactly the part that cannot distinguish d — and
the decomposition finds it carries no CM-sector concentration.

**Not tested here:** the non-equivariant complement — readouts that do NOT factor through U. That
is where the principle says any d-distinguishing concentration would have to sit.

## Scope / power
Enumerable primes p ≤ 433, single CM family y²=x³+7 (j=0). Controls: identities = 0; cross-isotype
≤ 1.6e-15; 60-draw ensemble null. No secp-magnitude claim; no exploitability assessed.

## Next (the outside-complement this sets up)
Take a **cheap, non-U readout** carrying a definite μ3-weight — e.g. the raw x-coordinate is
weight-1, x² is weight-2 — project it to a single isotype and measure its alignment with c
against the same ensemble null. Question: does any single-isotype channel of a cheap
(non-equivariant) readout depart from the ensemble null, where the equivariant aligned readout
(forced flat) cannot? Same conservation-hunt controls.
