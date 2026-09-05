# PREREG — Route A crux: does Semaev summation STRUCTURE lower the solving degree vs a degree/support-matched generic system, and does the advantage GROW with m?

**Status:** FROZEN before the structure-vs-generic numbers are read. Model scale.
**Date:** 2026-08-31. **Harness:** `semaev_elimination_v1.py` (Sage 10.9, exact GF(p) Macaulay
ranks, integer degrees — float-free). **Runner (to be built):**
`semaev_structure_solvingdegree_vs_m_v1.py`.
**Gate:** `experiment-designer` read owed BEFORE the run (this is a sweep-over-m with a matched
control and an advantage question). No grade promotes on this run.

---

## 0. Why this, and why it is not already done

The named hard route is **subexponential prime-field ECDLP**. Its literal crux is the *solving-degree
growth* of the Semaev index-calculus decomposition system as the number of summands m grows — the
"first-fall-degree assumption." If the summation structure holds the solving degree **below** a generic
system of the same shape, and that gap **grows** with m, that is a genuine asymptotic lever toward
subexponential relation-finding (and secp is a prime-field curve, so it would apply to secp). If the
solving degree **tracks** generic, the obstruction is real and honestly located.

**Not already covered.** `PROJECT_SUMMARY §123` (M9) reports first-fall & solving degree *identical
across curves* (secp / non-CM / j=1728) at fixed small m — a **curve-independence** null. `§553`
(§XI.4) marks the m-scaling **open at m≥5**. Neither reports the object here: the **structure-vs-generic
solving-degree gap as a function of m**. Retraction 8 (`§577`) downgraded "isobaric ⇒ first-fall
curve-independence" to `[HEURISTIC+CITED]`; this prereg does not rely on that claim — it measures the
gap directly and treats curve-independence as scope, not assumption.

## 1. Object (one sentence)
For the m-summand prime-field Semaev decomposition system {S_{m+1}(x₁..x_m, t)=0} ∪ {∏(xᵢ−v)=0 : v∈V},
does the true summation-polynomial coefficient set yield a **lower** solving degree d_solv (and
first-fall d_ff) than a **generic** system identical in every structural respect (same variables, same
field equations, same monomial support in the S-slot, same planted decomposition) but with **randomized
coefficients**, and does d_solv(generic) − d_solv(Semaev) grow / hold / shrink as m increases?

## 2. Statistic (pre-committed)
Primary: **Δd_solv(m) = d_solv(generic) − d_solv(Semaev)** and its trend in m.
Secondary: **Δd_ff(m) = d_ff(generic) − d_ff(Semaev)** (first-fall; syzygy-structure read).
All degrees are integers from exact GF(p) Macaulay ranks (`first_fall_and_solving`, `quo` target =
`I.vector_space_dimension()` for the consistent 0-dim ideal). No float anywhere in the degree read-out.

## 3. Matched control (the null)
Generic system G shares with Semaev: (a) the m decomposition variables; (b) the field equations
∏(xᵢ−v)=0 over the SAME factor base V (same Vroots); (c) the EXACT monomial support of the Semaev
S-polynomial in x-space (`Sx.dict().keys()`); (d) a planted decomposition — G is forced to vanish at
the same tuple (v₁,…,v_m) that solves the Semaev relation, by subtracting G(v₁,…,v_m) (a constant,
support-preserving). Only the S-slot **coefficients** are randomized (uniform nonzero in GF(p)). This is
the tightest possible null: it asks whether the *group law's specific coefficients* — not the degree,
sparsity, field, or variety size — buy a solving-degree advantage. ≥ K_null random-coefficient draws per
m; report min / median / max d_solv(generic) so the Semaev value is ranked against the generic
distribution, not a single draw.

## 4. Firing control (plant that MUST register lower)
A system engineered to have a genuinely low solving degree — S-slot replaced by a product of the m
linear field-consistent factors' first factor, i.e. an equation of degree 1 in x₁ that is satisfied by
the plant (`x₁ − v₁`) — must yield d_solv strictly below both Semaev and generic. If the statistic does
NOT drop for this plant, the read-out is broken and the run is void (report VOID, do not interpret).

## 5. Scope & power (stated BEFORE the run)
- **Tractable m this session:** m ∈ {2,3,4}; **attempt m=5** with a wall-clock cap (S₆ is degree 16 per
  variable — this is exactly the §XI.4 "open at m≥5" frontier; if it does not complete, that is the
  honest wall, reported as such, NOT as a null).
- **p:** model primes (a few hundred), curve in j=0/secp form (A=0) for relevance; d_ff/d_solv are the
  same object across curves at this scope (M9), so p and the curve are model knobs, not the variable.
- **Power ceiling (hard, stated up front):** secp-scale |FB| and m are unreachable; a model-scale
  degree trend is a **mechanism signal with an explicit extrapolation barrier**. A monotone trend over
  m∈{2,3,4} is 3 points — it can **suggest** a growth law, it cannot **prove** the asymptotic. No grade
  above `[EMPIRICAL, model scale]` may be claimed from this run regardless of outcome.

## 6. Decision rule (pre-committed — both directions)
- **LEVER (escalate):** Δd_solv(m) > 0 for m∈{3,4} AND non-decreasing in m (generic strictly harder than
  Semaev, gap holding or widening). ⇒ the summation structure is an asymptotic solving-degree lever;
  write it up as a live frontier, prereg an m=5(/6) confirmation, do NOT close. This is the outcome the
  counter-prior is looking for; it will not be pre-deflated.
- **NO STRUCTURAL LEVER (scoped component null):** Δd_solv(m) ≤ 0 or trendless (Semaev tracks or exceeds
  generic). ⇒ the group-law coefficients give no solving-degree advantage over random-on-same-support at
  this scope; a **scoped component null** on ONE factor of index-calculus cost — explicitly NOT an
  avenue closure (total IC cost also has relation-yield and factor-base-size factors; both out of frame
  here). Record magnitude + scope; keep the m≥5 regime named-open.
- **VOID:** firing control fails, or the generic system is not 0-dim/consistent (planted vanish failed),
  or m=4/5 does not complete — report the wall, interpret nothing.

## 7. Falsification of the LEVER reading specifically
Even a positive Δd_solv is NOT a lever if it is an artifact of the random control being *degenerate*
(e.g. random coeffs making the ideal lower-dimensional / inconsistent, inflating a fake gap). Guard:
require the generic ideal to be 0-dimensional with the SAME `quo` (variety size) as Semaev at the
planted point; discard and redraw any generic sample that is not variety-matched. A gap survives only if
it is between two 0-dim, variety-size-matched systems.

## 8. Exactness / fence
All arithmetic exact GF(p) (integers); `check_no_float` must pass on the runner. The PRNG/generation
boundary is not touched — this is pure curve-arithmetic (summation polynomial) structure.
