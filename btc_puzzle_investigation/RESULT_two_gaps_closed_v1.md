# RESULT — the two gaps closed by measurement. One of my prior conclusions is RETRACTED.

**Date:** 2026-08-01. **Scripts:** `centered_shortscalar_boundary_v1.py`,
`intensity_parseval_orbit_null_v1.py`. Both gaps were closed by running, not by argument.

---

## GAP 1 — the centered short-scalar statistic at the GLV boundaries

`S_cent = Σ_i r_i·(N_i − mean N)`, `r_i = χ₂(x_{[d₀+i]G})`. Stripping the `N₀·T` mass removes the
permutation-invariant term that made the earlier harness anti-powered (a 100% plant read `p = 1.0`).

**Instrument validated.** Boundaries located exactly by integer arithmetic; the **boundary arm's 40/40
intervals contain a lattice-vector-scale jump in `δ`**, the **control arm's 0/40** do. The arms are
genuinely separated. **C-PLANT fires 40/40 at 100% and 50% planted, 22/40 at 25%** — real power.

| arm | `p ≤ 0.05` | expected | min p |
|---|---|---|---|
| BOUNDARY (`W=64`, 40 intervals, `[2^128, 2^136)`) | **0/40** | 2.0 | 0.108 |
| CONTROL (no boundary, matched width/scale) | 4/40 | 2.0 | 0.006 |

> **NULL at the boundaries**, with power down to ~25% planted coupling.

**A secondary statistic popped and died.** The readout's partial-sum difference before vs after the
boundary read **+2.60, z = +2.66** in-sample (control −1.19). Pre-committed OOS on three fresh
octave ranges:

| range | boundary z | control z |
|---|---|---|
| `[2^136, 2^144)` | −0.04 | −1.06 |
| `[2^144, 2^152)` | +0.20 | +0.00 |
| `[2^152, 2^160)` | −1.23 | −0.25 |

**Dead.** 8th chance pattern killed by the pre-committed OOS rule.

---

## GAP 2 — the Parseval + parity + μ₃ null for `|T(a,b)|²`

Built exactly as specified. **`C-INV` verifies all three constraints on every checked draw: 0
violations.** Construction: permutations act on `a`-CLASSES `{a,−a}` **within** a row (Parseval and
parity), and for the μ₃ constraint `I(λa, βb) = I(a,b)` the permutation for row `βb` is **forced** to
be `λ∘σ_b∘λ⁻¹` — derived, not chosen. One free permutation per μ₃ orbit; nothing else is free.
**C-PLANT fires at `p = 0.005` on all four primes** — the tight null has power.

### ⚠ RETRACTION

`RESULT_intensity_field_spatial_item2b_v1.md` §2(C) concluded *"the effect is Parseval, not curve
structure."* **That was wrong**, and the user was right to refuse it. Under a null that respects
Parseval exactly, the Parseval effect is *inside the null* and `C_a1` still separates:

| p | n | `C_a1` obs | null mean ± sd | z | p |
|---|---|---|---|---|---|
| 127 | 127 | 0.99705 | 0.99992 ± 0.01084 | −0.26 | 0.76 |
| 163 | 139 | 0.97681 | 0.99797 ± 0.00976 | **−2.17** | **0.010** |
| 211 | 199 | 0.98140 | 0.99857 ± 0.00667 | **−2.57** | **0.020** |
| 349 | 313 | 0.99503 | 0.99930 ± 0.00374 | −1.14 | 0.26 |

The synthetic row-sum control I used to justify the retracted claim was **not** a matched null — it
matched one constraint and ignored two. **A constraint-by-constraint argument is not a null.**

### But it does not replicate out of sample

Pre-committed: statistic `C_a1`, direction negative. Discovery set `p ≤ 349`; everything above is OOS.

| p | n | z | in/out |
|---|---|---|---|
| 397 | 397 | −1.39 | OUT |
| 433 | 397 | −0.87 | OUT |
| 547 | 547 | +0.71 | OUT |
| 577 | 613 | +0.24 | OUT |

In-sample mean z **−1.54**; **OOS mean z −0.33, pooled −0.65, 2/4 signs, 0/4 at `p ≤ 0.05`.**
The effect is confined to the small-`n` cells (`n = 139, 199`) and vanishes by `n ≈ 400` — a
finite-size signature, not a structural one.

> **Verdict: no structure established. `C_a1` is NOT a Parseval artifact — that claim is withdrawn —
> but it does not replicate OOS at the stated power.** 7th chance pattern killed.

---

## Method note

Both gaps were closed by building the exact instrument rather than by reasoning about it, and in one
case the instrument overturned my conclusion. **The retracted claim was defended with a
constraint-by-constraint plausibility argument; the actual null contradicted it.** When a forced
constraint is suspected of explaining an effect, the test is a null that imposes *all* the forced
constraints simultaneously — not a synthetic field that imposes the one under suspicion.
