# DEVIATIONS — `PREREG_xdomain_ports_v1.md`

*2026-07-24. Filed at write-up time. **Eleven** deviations (D1–D7 from the first three arms,
D8–D11 from ARM 4); read them before the result document.*

---

## D1 — ⚠ Real-data runs executed BEFORE the spec was frozen

The spec was drafted concurrently with the instrument builds, and three runs touched real curve data
before it landed:

| run | pre-committed reading existed? | where |
|---|---|---|
| ARM B (`n1_twisted_eigenvalues_v1.sage`), `p = 13, 43` | **YES** | `NEXT_DIRECTIONS_v1.md §3 #1`, written **2026-07-23**, states both branches verbatim. This run is covered by an on-file pre-commitment that pre-dates it. |
| ARM A2 (`ct_boundary_stratified_v1.py`), `p = 1051, 1669, 2143` | partially | frozen in the script docstring before the run; **not** in the spec, and its enumeration was incomplete (see D5). |
| ARM C (`forced_readout_multiples_v1.py`), 19 primes | **YES** | frozen in the script docstring before the sweep; the μ₆ expectation was DERIVED first. |

Nothing here licenses reading an unregistered outcome as confirmatory. Where the pre-commitment does
not cover the outcome, the outcome is filed as `EXPLORATORY`, not promoted.

## D2 — ARM A2 is **not** the spec's ARM 2; the spec's ARM 2 has not been run

Different object, different statistic:

| | spec ARM 2 | what was run (ARM A2) |
|---|---|---|
| primary | `T₂ = ‖ΠDΠ‖_F²` on the near-degenerate block, ranked against a `B=200` surrogate ensemble | pooled `G²/df` **gradient across exact-boundary-margin strata** |
| ordering | calibration + plant sweep **hashed before** real data | no hash gate |
| scope | 9 primary curves + 6 holdout, frozen list of 37 | 3 curves, chosen for speed |

**The spec's ARM 2, ARM 3 and ARM 4 remain unrun.** ARM A2 is an additional, exploratory arm aimed at
the *idea* (localisation) rather than the *method* (power). It is graded `EXPLORATORY` throughout.

## D3 — ⚠⚠ Off-by-one on the group order: `n = len(pts) - 1`

`prime_order_curve` returned the **affine-point count**, not the group order, while every index in the
enumeration is taken **mod the group order**. Caught only because it made `n` even for every candidate,
so the primality filter rejected all 37 curves and the script printed `skipped` for everything.

**Had the wrong `n` been odd and prime, the run would have completed silently with every modular index
wrong.** Fixed, with an added assertion that the orbit actually closes (`[n−1]G + G = O`). This is the
**fourth** instrument bug of exactly this class on this record (cube-root valid only for `p≡2 mod 3`;
the power-residue vs character index in the Kummer run; the unconditional `FLOOR curve` print). Same
signature each time: **my own code producing a result one step from being written up.**

## D4 — ⚠⚠ Two forced symmetries I did not see, and a power claim that was a premise

The spec derived, and I then verified exactly at `p = 1051, 1669`:

- `(d,g) ↦ (d+2g, −g)` exchanges source and destination state (using `state(z₁,z₂)` symmetric in its
  arguments and `Z[−d] = Z[d]`) ⇒ **the count matrix is exactly symmetric, `C == Cᵀ`, verified**;
  all eigenvalues real (`max|Im| = 0`).
- `(d,g) ↦ (−d,−g)` preserves both states ⇒ **all counts even, verified**.

**Consequence — a correction to what I claimed.** I described this instrument as "the complete
population of the operator, generator scope removed". It is **not the same operator**: the `g=1` drill
measured a *directed* chain; the all-`g` enumeration is **reversible by construction**, so every
antisymmetric statistic is identically zero and `λ₂, λ₃` are real by construction, not by measurement.

**And the "6–30× power gain" I stated was a premise, not a measurement.** It assumed `n²` independent
transitions; the `n²` triples are built from `≤ (n+1)/2` distinct lattice values. D7's K3 ensemble now
shows the pooled statistic is dependence-dominated — the pooled `G²/df ≈ 155` at `p=1669` is
**reproduced at 155.6 by a control with the arithmetic destroyed.** The gain claim is **withdrawn**;
it is a quantity to be measured (spec §2.5), not one to be assumed.

## D5 — ARM A2's pre-committed reading did not enumerate the observed outcome

Frozen before the run were two cases: *excess concentrates at low margin* (idea supported) and
*`G²/df` flat in `M`* (not supported). **The observed outcome is neither:** the excess is strongly
margin-dependent (`z = −3.3…−4.5` vs the K1 margin-permutation null, 3/3 primes) but with the
**opposite sign** — largest **far from** the boundary — and is reproduced by the geometry-only control.

Per the abstention rule, **no conclusion is retro-fitted onto the frozen reading.** The result is
reported as an unregistered characterisation, graded `EXPLORATORY`, and the sign reversal is stated as
what it is: the stated idea's prediction did not occur, and a different, geometric, localisation did.

## D6 — a tautological column printed in `n1_twisted_eigenvalues_v1.sage` v1

v1 printed *"max attainable |Σ|/√p" = Σ|αᵢ|/√p* beside the weight check. **If every `|αᵢ| = √p` that
column is identically `4`** — it is the weight check restated, and printing both would count one fact
twice. Removed and replaced by the **phases**, which are the part of the configuration the weights do
not determine. **No conclusion rested on the removed column**; the reading below uses only the weights.

## D7 — K3 initially run as a single draw, with no error bar

The first K3 pass was one permutation, and the "arithmetic remainder" `real − K3` was therefore
unmeasurable. Corrected to a **20-draw ensemble** *before* any reading was taken. Single-draw K3
would have shown `−19.8` vs real `−20.4` at `p=1669` and `−4.6` vs `−11.4` at `p=2143` — i.e. it would
have supported "partly arithmetic" at one prime purely from noise. The ensemble sd is `±2.2…±5.0`.

---

# ARM 4 deviations (D8–D11)

## D8 — `ε*` is **0.5%**, not the predicted 0.36%; and the sweep has a gap

Spec §4.6 predicted `ε* ≈ 3.6×10⁻³` from a normal approximation to the non-central `χ²`, and said the
run replaces it with the empirical plant curve. It did:

| copy-fraction `ε` | 0.001 | 0.002 | **0.005** | 0.01 | 0.02 |
|---|---|---|---|---|---|
| detected (of 20) | 0 | 0 | **20** | 20 | 20 |

**`ε* = 0.005`** — a factor `1.4` worse than predicted, and the jump from `0/20` to `20/20` between
`0.002` and `0.005` means **the threshold is bracketed, not located**. The bound below is stated at
`0.005`, the value actually demonstrated. No interpolated figure is claimed.

**Plant nulls used `B = 99`, not `999`** (20 draws × 5 `ε` × a fresh null each). Declared; it affects
only the plant calibration's resolution (`α = 0.01` is representable at `B = 99`), not the primary.

## D9 — ⚠ a derived quantity printed an IMPOSSIBLE value; caught by its own impossibility

`arm4_stage3_primary_v1.py` v1 printed `implied per-isotype |ρ| ≈ 2.06`. **A correlation cannot exceed
1.** The formula assumed `|U|² ~ K` per isotype (uniform-marginal random walk); the marginals are not
uniform — `|U_{2,4}| = |U_{4,2}| ≈ 2.28×10⁴` against `√K ≈ 6.3×10²`, so the scaling is wrong by orders
of magnitude.

**Nothing rested on it** — the decision is rank-based and never used the line — and the impossible
value is what exposed it. Removed; the effect size is now read off the empirical plant curve, which is
what §4.6 specified in the first place. **This is the same failure mode as D3 and as the record's three
prior instrument bugs: my own code emitting a number one step from being reported.** The tell here was
that the quantity was *out of its own range*; that check should be standard on any derived effect size.

## D10 — the rotation (secondary) null ran at `B = 99`

Spec §4.4 fixes `B = 999` for the pair-permutation null (honoured) but did not pin `B` for the
multiplicative-rotation null. Run at `B = 99` for cost: each draw recomputes `eis_n(c·d mod n)` for all
`2×10⁵` scalars. Resolution is therefore `0.01` at best. `T₄` rank-p `= 0.4500` is far from any
threshold, so the coarser resolution does not affect the reading.

## D11 — `T_off` contains 4 pairing-INVARIANT isotypes (a spec defect, harmless to the decision)

`OFF = {(j,k) : j+k even, ≠(0,0), k ≠ −j}` includes `(0,2), (0,4), (2,0), (4,0)`. But
`U_{0,k} = Σ_d ζ₆^{k·s_w(d)}` depends on the `s_w` **marginal only** and is *identical* under every
pairing — it carries no coupling information and simply adds a constant to `T_off`. That is why the
`T_off` null is narrow relative to its median (`3.744e10` median, `3.758e10` at the 99th percentile).

**The rank-based p-value is unaffected**, since an additive constant common to the observation and to
every null draw cannot change a rank. So the reported `T_off` rank-p `= 0.78` stands. But the
statistic's **effective df is 8, not 12**, and its power is diluted accordingly. Any successor spec
should define `T_off` over `j ≥ 1, k ≥ 1` only.
