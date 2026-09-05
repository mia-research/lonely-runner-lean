# PREREG — μ₃-channel POSITIVE CONTROL repair, group-law difference-set moment battery (v1)

**Status:** FROZEN before any statistic is computed on any studied set. Gate: `experiment-designer`
(isolated context). Date: 2026-07-30. Scope of this document: it replaces the *positive control* of
the μ₃ channel of `difference_set_xy_geometry_v1.py` and fixes the statistic, null, power, decision
regions and pre-committed conclusions. **No value of the statistic on real-82 or constructed-36k was
observed while writing this spec.**

**What was computed at spec-writing time (disclosed so the ordering is auditable).** Only public
curve constants and analytic sizing, no studied set touched: `(p−1) mod 9 = 6`; `χ₃(−1)=1`;
`7` is a non-residue mod `p`; `−7` is a non-cube mod `p`; `χ₃(y)=χ₃((x³+7)²)` verified on 50 random
curve points; `C(82,2)=3321`, `C(160,2)=12720`; the AP multiplicity scale `√(Σw²/Σw)=10.3118…`;
the analytic power table in §5. Nothing else.

---

## §0 The defect this repairs (decidable, not a judgment)

`masked_structure_findings_v32.md` §(2)+(3) reports `M3(μ₃-x)` and `M3xy(μ₃-xy)` at the random level
for real-82 and constructed-36k and concludes *"Real-82 and constructed-36k difference sets are
generic"* and *"the xy odd+μ₃ harmonic adds nothing"*. The battery's declared μ₃-aimed positive
control is the GLV-triple set (`difference_set_xy_geometry_v1.py` docstring: *"CONTROLS (must fire):
… a GLV-triple set (keys closed under d→λ·d → μ₃ resonance)"*).

**That control is algebraically forced to zero and therefore cannot fire.** For a λ̂-closed point set
`S`, λ̂ permutes the unordered pairs of `S` and `x(λ̂P − λ̂Q) = β·x(P−Q)`, so the multiset
`V = {x(P_i−P_j)}` satisfies `βV = V`; hence `Σ_V χ₃ = χ₃(β)·Σ_V χ₃` and, since `(p−1) mod 9 = 6`
forces `χ₃(β)` to be a *primitive* cube root of unity, `Σ_V χ₃ = 0` exactly in `Z[ω]`. Verified:
1770/1770 pairs of a 60-point λ̂-closed set give `M3 = M3xy = (0,0)` exactly
(`…/scratchpad/m3_glv_control_forcing_v1.py`). This is the `_field_bigrading_v1.py` weight-mismatch
rule (χ₃ has μ₃-weight 1; the indicator of a β-invariant multiset has weight 0 ⇒ exact zero),
restricted from `F_p` to `V`.

**Consequence:** the μ₃-channel null has **no validated power**. The remaining control that did fire
(AP) is diagnosed in §4.4 as a *multiplicity* control, not a μ₃ control. The real-82 and
constructed-36k sets are **not** λ̂-closed, so their own values are not forced — the defect is
calibration, not contamination, and no reported number is retracted by this document. What is
retracted is the *power* attached to them, pending this run.

---

## §1 OBJECT

The **group-law difference multiset** of a point set on secp256k1 and the μ₃-isotypic weight on it.

```
S      = {P_1,…,P_m} ⊂ E(F_p)\{O},  P_i = [d_i]G,  all distinct
D      = { P_i − P_j : i<j }                     (group-law difference, |D| = C(m,2))
V_x    = multiset { x(R) : R ∈ D }               (the object of the primary cell)
V_xy   = multiset { x(R)·y(R) mod p : R ∈ D }    (the object of the secondary cell)
```

`p = 2²⁵⁶−2³²−977`, `E: y²=x³+7`, `j=0`, `|Aut(E)|=6`, `λ̂(x,y)=(βx,y)`, `β³=1`, `β≠1`.

**Not** the field difference set `{x_i − x_j}`. That is the object of
`PREREG_diffset_cubic_v1.md` / `PREREG_diffset_cubic_cmvanishing_v1.md` (statistic `E3`, real value
13125, p≈0.033). The two objects have the *same statistic form* but are different objects and stay
in separate ledgers; §5 borrows only the plant parametrization from that lineage, and §3 forbids
reusing its frozen region.

**Tautology audit (feature vs target construction).** The statistic is a character sum over `V_x`;
the tested property is a cubic-class imbalance of `V_x`. Feature and target are the *same* object, so
this is a **descriptive** measurement of one set, not a feature→target leakage test — there is no
`r = v − w` style shared-construction hazard here, and no key/target pair is correlated. The positive
control PC-B (§4.2) is *by construction* a set carrying the imbalance the statistic reads: that is
what a positive control is, and it licenses **no** mechanism inference.

**Forced structure (derived pre-data; the run must re-derive each clause literally, §10).**

| # | Forced fact | Reason | Run must |
|---|---|---|---|
| S1 | `x(R) ≠ 0` for every `R ∈ D` | a point with `x=0` needs `y²=7`; `7` is a non-residue mod `p` (verified) | assert `a+b+c == C(m,2)` in the x-cell |
| S2 | `y(R) ≠ 0` for every `R ∈ D` | `y=0` needs `−7` a cube mod `p` (verified false; also 2-torsion is impossible for prime odd `n`) | assert `a+b+c == C(m,2)` in the xy-cell |
| S3 | both readouts are **orientation-even** | `x(−R)=x(R)`; `y(−R)=−y(R)` and `χ₃(−1)=1` (verified) ⇒ `χ₃(x·y)` is unchanged by `R↦−R` | never form ordered pairs (§3 trap) |
| S4 | `E3 ≡ 0 (mod 3)` | `E3=(a+b+c)²−3(ab+bc+ca)` and `3 ∣ C(82,2)=3321`, `3 ∣ C(160,2)=12720` | assert; a non-multiple of 3 is a path bug |
| S5 | **the xy readout is a function of `x` alone** | on `E`, `χ₃(y)=χ₃(y²)²=χ₃((x³+7)²)`, so `χ₃(x·y)=χ₃(x·(x³+7)²)` (verified on 50 points) | assert on all `R ∈ D`; report |
| S6 | the xy readout has μ₃-weight 1, like the x readout | `(βx)³+7 = x³+7`, so `χ₃(βx·((βx)³+7)²) = χ₃(β)·χ₃(x·(x³+7)²)` | assert; explains why **both** are forced on λ̂-closed sets |

S5/S6 are load-bearing for interpretation: the "xy **odd**+μ₃ harmonic" is not odd and is not a
second harmonic — it is a second weight-1 character on the *same* multiset `V_x`. Any statement that
it "adds nothing" is in part an algebraic identity (it cannot carry orientation-odd information at
all), not an empirical null. The two cells are therefore **not independent tests**; §3 requires
their null correlation to be measured from the frozen null.

---

## §2 STATISTIC — exactly one per cell, named now, no maximum taken

```
PRIMARY  (cell x):   E3x  = N(M3x),   M3x  = Σ_{i<j} χ₃( x(P_i−P_j) )            ∈ Z[ω]
SECONDARY(cell xy):  E3xy = N(M3xy),  M3xy = Σ_{i<j} χ₃( x(P_i−P_j)·y(P_i−P_j) ) ∈ Z[ω]
```

with `χ₃(v) = ω^t` where `pow(v,(p−1)//3,p) = β^t` (`t ∈ {0,1,2}`, β fixed once, §8), Z[ω] element
`(a,b)` meaning `a+bω`, and the **exact integer norm** `N(a,b) = a²−ab+b²`. Equivalently, with
`(n₀,n₁,n₂)` the counts of the three cubic classes over the `C(m,2)` pairs,
`E3 = n₀²+n₁²+n₂² − n₀n₁ − n₁n₂ − n₂n₀`. Integer throughout; **no `abs`, no `sqrt`, no
`|M|/√pairs`** anywhere in the decision path (that normalization was float and is retired).

**Null distribution.** Under the null the `C(m,2)` values of `χ₃` behave as i.i.d. uniform cube roots
of unity, so `M3/√n_p → ` a standard complex Gaussian and `E3/n_p → Exp(1)`. This is used only as a
*shape reference*; every decision uses the empirical integer order statistics of that cell's own
null (§3). Cross-validation of the reference: the independently measured field-difference `E3` null at
`n_p=3321` reported mean ≈ 3321 and 97.5% ≈ 11997 against the reference's `3321` and `12251` — the
reference is good to ≈2%.

**Both cells are decided and both are reported. No max over cells, no post-hoc cell selection.**
Four decision cells (2 sets × 2 readouts), each with a two-sided α=0.05 region from its own null, plus
a family-wise ×4 corrected p reported alongside each. Both readings are pre-committed in §9 so no
choice is made after the fact.

**Aimed at the symmetry, per the drill rule.** The μ₃ weight is the predicted structure, so the
statistic is the weight-1 character sum itself, not a max over a battery of moments.

---

## §3 MATCHED NULL — what it must preserve, per set, and the recorded trap

**The trap (recorded).** A free shuffle that destroys an invariance the readout has *by definition*
manufactured a 6–7σ phantom on this project. In this channel the invariance is S3
(orientation-evenness). Concretely: if the null were built over **ordered** pairs with independently
drawn labels it would have `E|M3|² = 2n_p`, while the real statistic over ordered pairs is
deterministically `2·M3` with `E|2M3|² = 4n_p` — a phantom factor-2 excess (z of order √n_p) from
nothing but the ordering convention. **The null uses unordered pairs, one term per pair, identical
code path to the real set.** Likewise no label shuffling over pairs: that would destroy the pair-graph
constraint (the `C(m,2)` values are not independent — they come from `m` points) which the real
statistic has by construction.

### 3.1 Null for the studied sets (cells A, B)

Resample the **point set**, never the difference values.

| Structure | Null must | Why |
|---|---|---|
| `m` distinct points on `E(F_p)`, valid curve `x` | PRESERVE | the population the real set is drawn from |
| bit-length profile of the `d`'s | PRESERVE (cell A: one draw per real bit-length 1..82; cell B: uniform from the same 36k pool, i.e. the pool's own full-range profile) | bit-length is the only known generation-side covariate; keeps the curve variable isolated |
| the pair-graph (`C(m,2)` differences of `m` points, group-law) | PRESERVE — recompute differences by the same code | destroying it is the phantom route above |
| orientation convention (`i<j`) | PRESERVE (it is a no-op by S3; never randomized) | see trap |
| repeated-difference multiplicity spectrum | NOT constrained — measured and compared (§4.4) | multiplicity is a *rival* explanation, isolated by surrogate, not assumed away |
| which `d`'s | DESTROY (this is the tested variable) | — |
| λ̂-closure | neither set has it; nothing to preserve | — |

- Cell A pool: `constructed_keys_1to160_100k.csv` (`d`, cached `X`,`Y`), known-MT19937, bit-lengths
  1..160. Draw one row per real bit-length `1..82`. **N = 10,000** resamples, seed `20260730`.
- Cell B pool: `constructed_keys_fullrange_v1.csv` (36,000 rows, cached `X`,`Y`), `m = 160` drawn
  uniformly **from the whole pool**. **N = 2,000** resamples, seed `20260730`.
  *Disclosure:* the v32 script sliced the pool to its first 4000 rows before sampling (an undisclosed
  filter). This spec uses the whole pool for both the studied draw and its null; the two are matched,
  which is what the decision needs.
- Frozen regions: sort each cell's null array `A`; `L = A[⌊0.025N⌋]`, `U = A[⌈0.975N⌉−1]`. Written to
  `mu3_diffset_frozen_null_v1.npz` (integers) + `…_meta_v1.json` before any studied value is computed.
- **The field-difference `E3` region `[84, 11997]` is NOT reused.** Different object; each cell gets
  its own null.
- Also recorded from the frozen null, at zero extra cost: (i) the empirical correlation between `E3x`
  and `E3xy` (S5/S6 say they are not independent); (ii) the null's multiplicity spectrum of repeated
  difference values; (iii) mean and 97.5% vs the `Exp(n_p)` reference (gate F4).

### 3.2 Null for the λ̂-closed control cell (the retired positive control)

For a λ̂-closed set `M3x = M3xy = (0,0)` **exactly**, for every such set. The null is therefore a
point mass at 0: *no statistical test exists in this cell.* The null must **preserve λ̂-closure**
(any null that breaks it does not reproduce the forced zero and would manufacture significance in
either direction). This cell is retained as an **exact instrument assertion**, not a control:
`E3x == 0 and E3xy == 0` on the complete pair set, computed literally (never asserted), following
`lbe_harness_v1.py`'s forced-null discipline. Its role is to test the code path, not the hypothesis.

---

## §4 PLANTED CONTROL — adjudication and the adopted design

### 4.0 Adjudication of the four candidates

**(b) is ADOPTED**, in two tiers (PC-A instrument plant, PC-B set-level plant). (a), (c), (d) are
rejected as controls for stated, computed reasons; (c) is *deferred* as a statistic in its own right.

**(a) Partial orbits (2 of 3 per GLV triple) — REJECTED, with a number.** Removing the forcing is not
the same as planting an effect. For `S = ⋃_t {P_t, λ̂P_t}` over `m/2` independent `d_t`, the four
cross-differences of a block `(s,t)` have x-values `{x(A), βx(A), x(B), βx(C)}` where
`A=P_s−P_t, B=P_s−λ̂P_t, C=P_s−λ̂²P_t`, so the block's χ₃ sum is
`(1+ω)χ₃(A) + χ₃(B) + ωχ₃(C)`. Its mean is 0 (no coherent effect) and its energy is
`|1+ω|²+1+1 = 3` instead of 4 — a *suppression*. Predicted
`E[E3x] = (m/2)·1 + C(m/2,2)·3 = 80 + 9480 = 9560 = 0.752·n_p` at `m=160`, i.e. inside the null's
bulk (`P(Exp(n_p) < 0.752n_p) = 0.53`). A control predicted to land at 0.75× the null mean cannot
fire. Retained as an optional **mechanism diagnostic** with pre-registered predicted value
`0.752·n_p ± MC`: confirming it shows the residual of the forcing is understood.

**(b) A difference set with a real cubic-class imbalance — ADOPTED.** This is the only candidate whose
effect is the *same* observable the statistic reads, with a tunable, exactly measurable size, on a
genuine curve point set, evaluated by the same statistic used on the studied sets. §4.1–4.2.

**(c) `M3^{(j)} = Σ χ₃(x)·ω^{−j·pos}`, `pos` = rank within the β-orbit — REJECTED as a control,
DEFERRED as a statistic.** As a control it is a *statistic swap*: it does not calibrate `E3x`. And it
cannot fire even on its own terms. On a λ̂-closed set each β-orbit `{v,βv,β²v}` carries χ₃ values
`ω^c, ω^{c+1}, ω^{c+2}` (`glv_orbit_structure_proof_v1.py` clause B), and with `π` the
β-power→rank permutation the orbit contributes `ω^c·Σ_t ω^{t−π(t)}`, which is `3ω^{c+s}` for the
three even `π` and exactly `0` for the three odd `π`. The per-orbit **phase `ω^c` stays random**, so
with `N_orb = n_p/3` and `f` the fraction of even-`π` orbits,
`E[E3^{(1)}] = 9f·n_p/3 = 3f·n_p ≤ 3n_p < U = 3.689·n_p` **for every `f ≤ 1`**. Best-case power
`≈ exp(−3.689/3) = 0.29` at `f=1` (`0.086` at `f=1/2`). A ≤29%-power control is not a control.
Deferred, in its own prereg, in the **phase-blind quadratic** form (per-orbit energy), which is the
version that could fire — and which needs its own cross-set comparability argument, since orbit
completeness exists only for λ̂-closed sets.

**(d) Replace the readout with the β-invariant `χ₂` — REJECTED.** `χ₂` is the μ₃-**weight-0** channel:
adopting it abandons the object rather than calibrating it (the μ₃ channel would then be untested,
which is the defect, restated). It also does not fire: the recorded measurement on the λ̂-closed set is
`Σχ₂ = 12` at `√n_p = 42`, i.e. `0.29×` the random scale — the same random level the retired control
sat at. `χ₂` on this difference set is a legitimate object (weight-0 / twist channel) and belongs in
its own prereg, not here.

### 4.1 PC-A — instrument plant (establishes the power curve of the statistic)

Take a genuine null point set, compute `V_x` by the real code path, then for a uniformly chosen subset
of exactly `⌈ε·n_p⌉` pairs replace `v` by `v·g^{−t}` where `ω^t = χ₃(v)` and `g` is a fixed non-cube
(`g = β` is not usable; take the smallest `g` with `pow(g,(p−1)//3,p) ≠ 1`, recorded in meta). This
maps every selected value into class 0 exactly; all integer, no float.

- Ladder `ε ∈ {0, 0.010, 0.015, 0.020, 0.025, 0.030, 0.040, 0.050, 0.100}`, 10,000 realizations per
  rung per cell → **measured** power curve vs the frozen region.
- PC-A calibrates the statistic and the decision region, **not** the point-set→statistic pipeline.
  Its plant multiset is not the difference set of any point set; that is what PC-B is for.

### 4.2 PC-B — set-level plant on real curve points (the load-bearing "can fire" control)

Greedy construction, integer-exact, same code path as the studied sets:

```
seeds: d drawn from the SAME pool and bit-length profile as that cell's null
S ← {[d]G} for one seed
repeat until |S| = m:
    draw a candidate d' (matched profile), Q = [d']G, Q ∉ S
    let c = #{ P ∈ S : χ₃(x(Q−P)) = 1 }              (class 0 of the ω-labelling; convention fixed in meta)
    accept Q iff  3·c ≥ |S| + ⌈δ·|S|·3⌉             (integer test; no float)
```

`δ` = targeted excess of the dominant class frequency over `1/3`; it maps to the §5 plant parameter by
`ε = 1.5·δ` (class frequency `1/3 + (2/3)ε`). Feasibility computed pre-data: acceptance rate
≈ 0.26 (`m=82`, δ=0.0333) and ≈ 0.19 (`m=160`, δ=0.0333) ⇒ ≈4–5 candidates per accepted point,
≈5·C(m,2) point subtractions per construction.

- Ladder `δ ∈ {0, 0.0094, 0.0141, 0.0207, 0.0277, 0.0333}` (i.e. `ε ≈ 0, 0.0141, 0.0212, 0.031,
  0.0415, 0.05`). **200** independent constructions per rung for cell A, **50** for cell B.
- Report per rung: the exact `(n₀,n₁,n₂)`, the **measured** `ε̂ = (3n₀ − n_p)/(2n_p)` (exact rational),
  `E3`, and the fire rate against the frozen region ⇒ the empirical power curve of the *end-to-end
  pipeline*.
- **Fire gate (must pass or every null in this run is uninformative):** at `δ = 0.0333`
  (`ε ≈ 0.05`), fire rate ≥ 0.95 in both cells.
- **Margin gate (§5):** at `δ = 0.0333`, median `E3(PC-B)/U ≥ 2.0` (cell A) and `≥ 5.0` (cell B).
- **Minimum-detectable gate:** at `δ = 0.0141` (`ε ≈ 0.0212`), fire rate ≥ 0.80 in cell B; at
  `δ = 0.0277` (`ε ≈ 0.0415`), fire rate ≥ 0.80 in cell A. These are the §5 numbers, measured.
- PC-B is run for **both** readouts (the xy version greedily biases `χ₃(x·y(Q−P))`), since a control
  must fire on the same statistic as the cell it calibrates.

### 4.3 Retired / instrument-only cells (reported, never used as positive controls)

| cell | role | pass condition |
|---|---|---|
| λ̂-closed set, `m = 60` and `m = 162` | **exact instrument assertion** (§3.2) | `E3x == 0` and `E3xy == 0` exactly, all `C(m,2)` pairs |
| random-curve set, `m = 82` and `m = 160` | null-shape instrument | `E3` inside its own cell's frozen region; class counts consistent with `Multinomial(n_p,1/3)` |
| partial-orbit set (§4.0(a)) | mechanism diagnostic | `E3x ≈ 0.752·n_p` (predicted pre-data) |
| AP set, `m = 160`, `δ_AP` random `< 2⁴⁰` | **multiplicity** control, reclassified — see 4.4 | fires; and its firing is reproduced by the multiplicity surrogate |

### 4.4 The multiplicity surrogate (matched surrogate; the rival explanation, isolated)

The AP fires on `M3` (v32: 9.76) but its firing is accounted for by *repeated differences alone*: the
AP's `C(160,2)=12720` pairs realize only 159 distinct differences with weights `w_j = 160−j`, and a
random-phase χ₃ over that weight multiset has scale `√(Σw²/Σw) = √(1352560/12720) = 10.3118`, against
the reported 9.76 at 94.3% pair retention. So the AP calibrates a *degenerate-multiplicity* channel
that any bounded character readout would detect — it carries no information about sensitivity to a
cubic-class imbalance among multiplicity-1 differences, which is the studied sets' regime.

**Surrogate (required, applied to every set including real-82 and constructed-160):** keep the set's
observed multiset of difference-value multiplicities; replace each *distinct* value's χ₃ by an
independent uniform cube root; recompute `E3`; 10,000 draws ⇒ a multiplicity-matched reference
distribution. Needs no fit and no exponent.
- AP inside its surrogate ⇒ AP is a multiplicity control (recorded; its μ₃-channel role is retired).
- PC-B inside its surrogate ⇒ **PC-B is defective** (F2 in §7).
- A studied set outside its surrogate ⇒ the excess is cubic-class structure, not repeated differences.
- A studied set inside its surrogate but outside the §3.1 null ⇒ the excess is repeated differences;
  report as a multiplicity finding, explicitly not a μ₃ finding.

---

## §5 POWER — numbers, fixed now

Plant parametrization (identical to the field-difference `E3` lineage, so the two ledgers are
comparable): a coherent fraction `ε` of pairs in one cubic class, the rest uniform ⇒
`E[M3] = ε·n_p`, dominant class frequency `1/3 + (2/3)ε`. Reference null `E3/n_p ~ Exp(1)`;
one-sided upper threshold `U = 3.6889·n_p`; power from noncentral χ²₂ with
`λ = 2ε²n_p/(1−ε)` (analytic sizing only, float, no key on the path).

| cell | `m` | `n_p = C(m,2)` | `L` (ref) | `U` (ref) | `ε₅₀` | `ε₈₀` | `ε₉₅` | class freq. at `ε₈₀` |
|---|---|---|---|---|---|---|---|---|
| A (real-82-matched) | 82 | 3,321 | 84 | 12,251 | 0.0310 | **0.0415** | 0.0513 | 0.3610 |
| B (constructed-160) | 160 | 12,720 | 322 | 46,923 | 0.0158 | **0.0212** | 0.0263 | 0.3475 |

Power at fixed rungs (analytic; PC-A/PC-B must reproduce these within MC error):

| `ε` | power, cell A | `E[E3]/U`, A | power, cell B | `E[E3]/U`, B |
|---|---|---|---|---|
| 0.010 | 0.058 | 0.36 | 0.189 | 0.61 |
| 0.020 | 0.196 | 0.63 | 0.742 | 1.64 |
| 0.030 | 0.468 | 1.07 | 0.987 | 3.37 |
| 0.050 | 0.938 | **2.51** | 1.000 | **8.88** |
| 0.100 | 1.000 | 9.25 | 1.000 | 34.73 |

**Smallest detectable μ₃-channel effect (the number this repair buys):** at 80% power,
`ε₈₀ = 0.0415` on 82 points (dominant cubic class of the 3,321 group-law differences at 36.10%
instead of 33.33%) and `ε₈₀ = 0.0212` on 160 points (34.75% instead of 33.33%). Anything smaller is
**not measured** by this battery at this `m`, and no statement about it may be made.

**Margin (firing is necessary, not sufficient).** Required margins at `ε ≈ 0.05`: median
`E3(PC-B)/U ≥ 2.0` (A), `≥ 5.0` (B) — analytic expectations 2.51 and 8.88. A control that fires only
at `E3/U ≈ 1` is disclosed as *marginal calibration* and the cell's `ε₈₀` is re-stated from the
measured PC-B curve, not the analytic one.

**Power against the alternatives this statistic cannot see: zero.** `E3` is a function of the marginal
class counts only. Named blind subspaces, each with its own next probe, in §9.4.

---

## §6 SCOPE — inherited by every number this run produces

- **Prime:** `p = 2²⁵⁶−2³²−977` only. One curve, `E: y²=x³+7`. No other prime, no other curve. No
  claim extends past this scope; results at small `p` (§10 R3) are instrument checks only.
- **Sets:** (A) the 82 solved puzzle keys, `solved_keys_augmented_v1.csv`, all 82, `n_p = 3321`;
  (B) `m = 160` drawn uniformly from all 36,000 rows of `constructed_keys_fullrange_v1.csv`
  (bit-lengths 1..256), `n_p = 12720`. Nulls from `constructed_keys_1to160_100k.csv` (A) and the same
  36k pool (B).
- **Pair subsampling is FORBIDDEN.** Every cell uses all `C(m,2)` pairs; the run asserts
  `n_pairs == C(m,2)`. The retired `maxpairs=12000` cap (12000/12720 = 94.3%) is the reason the
  forced zero read as `|M3|/√n ≈ 0.23` instead of 0: partial pair sets are not β-invariant, so
  subsampling *destroys the forcing* and silently converts an exact algebraic zero into a small
  nonzero residual. Any future variant that subsamples must re-derive its own forced structure.
- **Set size is fixed pre-run** at `m ∈ {82, 160}` (plus `m ∈ {60,162}` for the λ̂ instrument cell,
  chosen as multiples of 3 so λ̂-closure is exact). No post-hoc `m`.
- **`β` and the ω-labelling convention are fixed once** and recorded in meta; every cell uses the same.
- **Language.** `secure` / `closure` / `dead` / `generic` / `wall` / `proven hard` are forbidden in the
  result. Output is a characterization plus a bounded magnitude with power and scope
  (`feedback_closure_grade`, `feedback_negative_bias_enlarge_nulls`).

---

## §7 FALSIFICATION

### 7.1 Of the hypothesis under test
A cubic-class imbalance in the group-law difference multiset of the studied sets, at this `m` and this
`p`, is falsified *at the stated power* if both studied cells land inside their frozen regions while
PC-B fires at `ε₈₀` with the required margin and the multiplicity surrogate is clean. The conclusion
is then a **bounded magnitude** (`ε < 0.0415` at 82 points / `ε < 0.0212` at 160 points, 80% power),
never "generic" and never a closure of the μ₃ channel (§9.4 lists what remains unprobed).

### 7.2 Of the repaired control itself (any one of these voids the run)

| id | condition | reading |
|---|---|---|
| F1 | PC-B's measured `ε̂ ≥ ε₈₀` but its fire rate < 0.80 | instrument insensitive at the claimed power ⇒ the `ε₈₀` numbers are wrong; re-derive from the measured curve, do not report a null |
| F2 | PC-B fires **and** its multiplicity surrogate (§4.4) also fires at the same level | PC-B's firing is a multiplicity artifact, exactly the AP's defect ⇒ PC-B is not a μ₃ control; the channel stays uncalibrated |
| F3 | PC-B's multiplicity spectrum differs from its cell's null spectrum | the greedy is selecting for repeated differences, not for cubic class ⇒ same defect as F2 |
| F4 | a cell's null deviates from the `Exp(n_p)` reference beyond a pre-set rank/KS check (mean outside `n_p·[0.95,1.05]`, or 97.5% outside `U·[0.9,1.1]`) | the decision region is not the assumed one; report the empirical region and the deviation, do not report a z |
| F5 | any clause of §10 R1/R2 fails | path bug; nothing in the run is trusted, fix first |
| F6 | PC-B's planted excess is not confirmable by an independent witness (second χ₃ implementation and an independently recomputed difference list) | the "plant" is only visible to the instrument that made it ⇒ tautology, void |
| F7 | PC-A's measured power curve and PC-B's differ by more than one ladder rung at the 0.8 crossing | the point-set→statistic pipeline loses sensitivity the statistic has ⇒ disclose; the pipeline number (PC-B) governs |

A void run is reported as **"no validated power in this channel"** — the same status §0 assigns to the
v32 μ₃ null. It is not a null result, and it does not close anything.

---

## §8 EXACTNESS

- Signal path is `int` / `Z[ω]`-as-integer-pairs only: field arithmetic mod `p`, `pow(v,(p−1)//3,p)`,
  the Z[ω] accumulator `(a,b)`, `N(a,b)=a²−ab+b²`, class counts, and all comparisons against integer
  order statistics. `check_no_float.py` must pass on every new script:
  `mu3_diffset_control_repair_v1.py`, `mu3_diffset_null_v1.py`, `mu3_diffset_apply_v1.py`.
- `x(P−Q)`/`y(P−Q)` via the affine group law with **batch (Montgomery) inversion** over each pair
  batch — exact modular inverses, integer only. Budget: cell A null ≈ 33.2M pair operations with
  10,000 batched inversions; `gmpy2` 2.3.1 is available and permitted (integer only).
- Float carve-out, **analytic size only, never on the signal path and never deciding anything**: the
  §5 power table (`ncx2`, `exp`, `log`), the AP multiplicity scale `10.3118`, and cosmetic percentages
  in the report. Every decision is an integer comparison. No `|M|/√pairs` anywhere.
- The `random` module is used only to draw indices/seeds for nulls and controls (a null model, not a
  key path), with seeds frozen in meta: `20260730`.
- Path note carried forward: `difference_set_xy_geometry_v1.py:95-97` computes λ as
  `pow(2,(n−1)//3,n)` with a fallback search over `range(2,10000)`. The fallback cannot succeed (no
  small cube root of unity mod `n`) and would raise `IndexError`; the primary expression is correct at
  secp's `n` (`λ³≡1`, `λ²+λ+1≡0` verified). The new scripts must assert both properties of λ and of β
  rather than rely on a fallback.

---

## §9 PRE-COMMITMENT — filled in before the run

### 9.1 Gate order (a later step may not be run until the earlier one passes)
1. §10 R1–R2 forced-zero reproduction and forced-structure assertions S1–S6.
2. §10 R3 cross-implementation of χ₃; §10 R4 AP multiplicity surrogate.
3. Freeze both nulls, write `mu3_diffset_frozen_null_v1.npz` + meta; F4 shape gate.
4. PC-A and PC-B ladders; fire / margin / minimum-detectable gates; F1–F3, F6, F7.
5. **Only then** compute `E3x`, `E3xy` on real-82 and constructed-160 and decide.

### 9.2 Outcome table (controls passing = gates 1–4 all green)

| outcome | pre-committed conclusion |
|---|---|
| Both studied cells inside their regions, all 4 cells | The μ₃ weight-1 channel of the **group-law** difference multiset carries no cubic-class concentration above `ε = 0.0415` (82 pts, 80% power) / `ε = 0.0212` (160 pts) at `p` = secp's prime. Stated as a bounded magnitude with power and scope. The v32 sentences "difference sets are generic" and "the xy harmonic adds nothing" are **replaced** by this bounded statement plus the S5/S6 algebraic facts (the xy readout is a second weight-1 character on the same multiset and is orientation-even by identity — part of "adds nothing" is an identity, not a measurement). No closure; §9.4 stands. |
| A studied cell **outside** its region and outside its multiplicity surrogate | **A fired cell. Its pre-committed conclusion is the primary section of the result** (`feedback_prereg_abstention_is_the_finding`): a cubic-class concentration in the group-law difference multiset at the stated scope, `[EMPIRICAL]`, with the exact `(n₀,n₁,n₂)`, `E3`, rank-p, ×4 family-wise p, and the measured `ε̂` against the power table. Follow-ups (band split, out-of-sample retest on unsolved-range constructed sets, the `E′` non-CM curve swap) go under `EXPLORATORY`; none may override this cell. |
| A studied cell outside its region but **inside** its multiplicity surrogate | A repeated-difference (multiplicity) finding, explicitly **not** a μ₃ finding: report the multiplicity spectrum and the coincidences `d_i−d_j = ±(d_k−d_l)` that produced it. The μ₃ cell is *not* declared fired. |
| Both studied cells inside their regions **but** any gate F1–F7 tripped | **No validated power.** The channel remains uncalibrated; the v32 μ₃ null is re-tagged `[NO VALIDATED POWER]`; the named defect and its next probe are the output. No bound is stated. |
| §10 R1/R2 fails (F5) | Path bug. Nothing reported. Fix and re-run from gate 1. |
| PC-B cannot reach `ε₈₀` at any ladder rung | The end-to-end pipeline is less sensitive than the statistic: report the measured pipeline `ε₈₀`, restate §5 from it, and state the bound only at that (weaker) power — or, if no rung fires, `[NO VALIDATED POWER]`. |

### 9.3 What no outcome licenses
No outcome supports a security verdict, and no outcome closes the μ₃ channel, the difference-set
object, or any avenue. The retired GLV control's forced zero is a **characterization** (a μ₃-weight
selection rule on β-invariant multisets, §0), not evidence about the studied sets — dissolution is a
positive result and is reported as one.

### 9.4 If the effect lives in a subspace this statistic does not project onto
`E3` is a function of the marginal class counts `(n₀,n₁,n₂)` only. Provably blind to, each with its
named next probe (separate preregs, not decided here):

| blind subspace | why blind | next probe |
|---|---|---|
| joint / triangle structure among overlapping pairs with balanced marginals | marginal-count statistic | 3-cycle statistic `Σ_{i<j<k} χ₃(x_ij x_jk x_ki)` — needs its own forced-structure derivation first |
| μ₆ component `(j,k)=(1,1)`: `Σ sgn(y_diff)·χ₃(x_diff)` | S3: `χ₃(−1)=1` makes both readouts orientation-**even**, so no orientation-odd content can appear | the `(1,1)` isotypic sum, which needs a convention-invariance argument before it is measurable (an arbitrary `i<j` convention is exactly where the recorded 6–7σ phantom entered) |
| β-orbit-position grading | `pos` is not in the statistic | the deferred (c) statistic, phase-blind quadratic form (§4.0(c)) |
| μ₃-weight-0 / twist channel (`χ₂`) | different weight | the deferred (d) object, as an object |
| bit-length-band-localized concentration | pooling over all pairs dilutes it | banded `E3` with per-band nulls and an explicit multiple-comparison budget |
| effects below `ε₈₀` | power | larger `m` (power scales as `ε√n_p`; `m=1000` gives `ε₈₀ ≈ 0.0053`) |

---

## §10 REPRODUCTION CHECK — required before the repaired control is trusted

The forced-zero result of §0 must be **re-derived independently**, in a new script, not imported and
not asserted. Gate 1 of §9.1.

- **R1 (end-to-end forced zero).** Freshly generate λ̂-closed sets at `m = 60` and `m = 162` (seeds
  distinct from the scratchpad script's), all `C(m,2)` pairs, no subsampling: assert
  `M3x == (0,0)` and `M3xy == (0,0)` exactly in `Z[ω]`. Also assert the residual reappears under
  subsampling (drop 720 of 12720-style retention) — confirming §6's account of the 0.23 reading.
- **R2 (mechanism, clause by clause, each computed literally).**
  (i) `(p−1) mod 9 == 6`; (ii) `pow(β,(p−1)//3,p) ≠ 1`, i.e. `χ₃(β)` primitive;
  (iii) `1 + χ₃(β) + χ₃(β)² == (0,0)` in `Z[ω]`; (iv) **exact multiset equality** `βV_x == V_x` on the
  complete difference multiset of a λ̂-closed set (a `Counter` comparison, not a spot check);
  (v) `χ₃(−1) == 1`; (vi) `y(λ̂Q) == y(Q)` and `x(λ̂Q) == βx(Q)` on actual curve points;
  (vii) `λ³ ≡ 1`, `λ²+λ+1 ≡ 0 (mod n)`; (viii) S1, S2, S5, S6 of §1.
- **R3 (cross-implementation of χ₃).** (a) multiplicativity `χ₃(uv)=χ₃(u)χ₃(v)` and `χ₃(u³)=1` on 10⁴
  random `u,v` mod `p`, exact; (b) at a small prime `p₀ ≡ 1 (mod 6)` with `y²=x³+7` nonsingular, run
  the whole pipeline and check the `pow`-based χ₃ agrees with the discrete-log-index χ₃ of
  `isotypic_selection_rule_v1.py` / `_field_bigrading_v1.py` on **all** `x ∈ F_{p₀}`, and that the
  weight-mismatch rule reproduces the forced zero there too. Small-`p₀` results are instrument checks
  and inherit no scope (§6).
- **R4 (AP reclassification).** Reproduce the multiplicity-only account of the AP's firing: build the
  AP's difference-multiplicity multiset, verify `Σw = C(160,2)`, `Σw² = 1,352,560`, and check the AP's
  observed `E3x` lies inside the multiplicity surrogate distribution (§4.4). If it does, the AP is
  recorded as a multiplicity control and its "μ₃ detector validated" role in v32 is corrected.

If any of R1–R4 fails, F5 applies: nothing else in the run is trusted.

---

## §11 Artifacts

- `mu3_diffset_forced_zero_reproduce_v1.py` — §10 R1–R3
- `mu3_diffset_null_v1.py` — §3 frozen nulls + F4 shape gate + null diagnostics (cell correlation,
  multiplicity spectrum)
- `mu3_diffset_control_repair_v1.py` — §4 PC-A, PC-B, instrument cells, §4.4 surrogates, §10 R4
- `mu3_diffset_apply_v1.py` — §9.1 gate 5 only (refuses to run unless the meta records gates 1–4 green)
- `mu3_diffset_frozen_null_v1.npz`, `mu3_diffset_meta_v1.json` (β, ω-labelling, `g`, seeds, `m`,
  `n_pairs`, pool paths, row counts, SHA-256 of this file, gate statuses)
- `RESULT_mu3_diffset_control_repair_v1.md` (after the run) and
  `PREREG_mu3_diffset_control_repair_v1_DEVIATIONS.md` (mandatory, even if empty: statistic changed?
  sample filtered? subset chosen post-hoc? control fired? power stated? scope on every number?
  conclusion matches §9.2?)
