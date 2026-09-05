# GATE REVIEW (isolated) — PREREG_brick_e_cd_degree_v1

**Reviewer role:** experiment-designer, isolated (given only the spec + DEVIATIONS + engine + the named
grounding docs; not the session narrative). **Object of review:** whether the FROZEN spec has a
frame-layer defect that would make its eventual run uninterpretable. **Conclusion up front:**

> **NOT adequate as frozen.** One primary frame defect (F1: the matched null omits a forced symmetry of
> the real `φ`), plus a linked identifiability defect (F2: the primary-domain single-valued `c(d)` /
> "one modulus M" is not well-posed and is in tension with that same symmetry). Both are fixable
> pre-run. Three secondary items (F3–F5). The mechanical layers the spec claims covered (engine fit,
> planted-degree recovery, None-vs-numeric via D1) are indeed sound. Firing-control validity (F4) and
> power/falsification (F5) are conditionally sound *once the null is fixed*.

The two primary findings are the exact defect class the spec's own §3 flags as un-self-clearable, and
the class that voided `VOID_anew_cartier_c4_adjudication_v1`.

---

## F1 — MATCHED-NULL OMITS THE FORCED ζ₄ / μ₆ COVARIANCE  [primary; §3 "matched-control adequacy"]

**Clause.** Q4: *"Draw random maps `c'` satisfying `c'(λd)=κc'(d)` EXACTLY … otherwise random in
`A_new`. This preserves (F1)-consistency and (F2) exactly and varies only the UNFORCED degree content."*
And F2 (§0) is asserted to be the *only* forced symmetry the null must carry.

**The omitted symmetry — forced, derived from the construction, not measured.** The cover
`C: w⁴ = x³+7` carries TWO commuting automorphisms, not one:
- `ζ₃` (GLV): `(x,w) ↦ (βx, w)` — descends to `[λ]` on `E`; source of the null's `c(λd)=κc(d)`.
- `ζ₄` (biquadratic): `(x,w) ↦ (x, i·w)`, `i²=−1` — a genuine automorphism ((`iw`)⁴ = `w`⁴ = `x³+7`).

`ζ₄` descends under `C→E, (x,w)↦(x,y=w²)` to `(x,y)↦(x,−y) = [−1]_E`, and `ζ₄²:(x,w)↦(x,−w)` is the
deck involution of `C→E`. Since `A_new = Prym(C/E)` is the `(−1)`-eigenspace of that deck involution,
`ζ₄² = [−1]_{A_new}`, so `ζ₄` acts on `A_new` as an order-4 endomorphism `ρ` with `ρ² = [−1]` (i.e.
`Z[i] ⊆ End(A_new)` — the standard CM of a `w⁴`-cover Jacobian; this is the "`ζ₄`/biquadratic channel"
of `ANALYSIS_zeta4_cartier_manin_ideas_improvements_v1`). `ρ` commutes with `ζ₃`, hence preserves the
`ζ₃`-isotypic factor and the `M5` eigenvector line used to build `φ`. Because `ζ₄` maps `fibre(P)`
bijectively onto `fibre([−1]_E P)`,

> **`φ([−d]G) = ρ · φ([d]G)`  — a FORCED covariance of the real `φ` under `d ↦ −d`.**

Together with `c(λd)=κc(d)`, the real `c` is covariant under the **full `μ₆ = ⟨−λ⟩`**, not `μ₃`.

**Why the null misses it, and why it is not already implied by F2.** `−1 ∉ ⟨λ⟩` (verified: at `n=31`,
`⟨λ⟩={1,5,25}`, `−1≡30 ∉`), so `−d` lies in a *different* `μ₃`-orbit from `d`; the F2 relation places no
constraint linking `c(−d)` to `c(d)`. A Q4 draw is free on one rep per `μ₃`-orbit → **11 free values** at
`n=31`; the real `c`, `μ₆`-covariant, has only **6** (verified: 11 `μ₃`-orbits vs 6 `μ₆`-orbits). The
null carries ~1.8× the degrees of freedom of the signal.

**Concrete failure it causes.** The permutation p-value `π = Pr_null[D' ≤ D_obs]` is computed against a
null that is *less constrained than the signal by a forced symmetry the signal has by definition*. The
real `c` inherits the `μ₆` monomial restriction (interpolant supported on degrees `≡ i₀ (mod 6)`); the
`μ₃` null only restricts to `≡ i₀ (mod 3)`. So `D_obs` runs systematically below `D'_null` for reasons
that have **nothing to do with a cover-scramble channel** — `π` is biased downward a priori. This is the
same failure that produced the project's "6–7σ soft shadow" (shuffle destroyed a symmetry the readout
has by definition) and the class named in `VOID_anew_...` (a null that does not reproduce a forced
structure of the signal). A downward-biased `π` cannot be read as evidence of low-degree solvability.
The bottom row of the §2 outcome table (a raw degree *bound*) survives — `D_obs` is still the real
degree — but the **top row (solvable channel, gated on `π≤0.01`) is uninterpretable under this null.**

**Minimal fix — fold `ζ₄` into the null (make it `μ₆`-invariant).**
Replace Q4 with: *draw `c'` freely on one representative per `⟨−λ⟩` (`μ₆`) orbit; propagate to the whole
orbit by BOTH the `μ₃` law (`c'(λd)=κc'(d)`) AND the `ζ₄` law (`c'(−d)=ρ·c'(d)`, `ρ` = the measured
order-4 `ζ₄`-action on `A_new`, `ρ²=[−1]`).* The null then shares every forced symmetry of `φ` and
varies only the genuinely unforced degree content. Recompute `π` against this `μ₆`-null. A real channel
still shows (`π` small); an artifact of the omitted symmetry gives `π ≈ uniform`. (Determine `ρ`'s action
empirically on the instrument — see F2; it is NOT a scalar, see below — but that is null-side machinery,
computable without reading the real `c`.)

---

## F2 — PRIMARY DOMAIN: "one modulus M / single-valued `c(d)`" IS NOT WELL-POSED  [primary; identifiability]

**Clause.** Q1: *"Primary domain: the FULL group `E(F_p)`, all `n` points, with every dlog taken in
`A_new(F_{p²})` … so all `c(d)` share ONE modulus `M` …"* and its gate-confirm note *"embedding into
`A_new(F_{p²})` does not itself introduce structure — the null runs in the same group."*

**The failure.** A single-valued `dlog_{A_new}` to a base `S(G)` requires every `φ([d]G)` to lie in the
cyclic group `⟨S(G)⟩`. `⟨S(G)⟩` (order `1893`) sits in `A_new(F_p)`. The non-QR-lift half (`y_P` a
non-residue) — which is exactly the `−d` half, since `−1` is a non-residue at `p=43` — lifts only over
`F_{p²}` and its `φ`-images lie in `A_new(F_{p²}) \ A_new(F_p)`, hence **not in `⟨S(G)⟩`**. The
single-base dlog is undefined for them. Moreover a scalar form of the `ζ₄` action is *arithmetically
impossible* on a cyclic order-`M` group: `ρ²=[−1]` would need `μ²≡−1 (mod M)`, but `√−1` does **not
exist mod 3, mod 631, or mod 1893** (all `≡3 mod4`; verified). So `ρ` acts as a genuine 2-dimensional
endomorphism pairing the `±d` halves, i.e. `φ` on the primary domain is naturally a **2-component
`A_new(F_{p²})`-element, not a scalar** — and "the degree of `c(d)`" (Q3, defined for scalar `c`) is
under-specified there.

**Consequence.** The primary arm as written does not define the statistic it feeds to Q3. The
*rational-lift* arm (QR half, `A_new(F_p)`, modulus `1893`, single-valued) IS well-posed — but it is
`μ₃`-closed and never `⟨−1⟩`-closed (verified: the OPEN-doc 15-point set is `λ`-closed, not `−1`-closed),
so it contains no `±d` pair and by construction cannot exhibit the F1 symmetry; and it has ~15 points
(weaker still). The Q1 requirement *"the two arms must agree on `D`"* therefore compares two
structurally different objects (one with the `ζ₄` pairing, one without) and is not a valid cross-check.

**Minimal fix.** Before freezing the statistic, resolve the group structure of the relevant part of
`A_new(F_{p²})` (cyclic vs `Z[i]`-module of rank 2). If non-cyclic, define `c(d)` as a fixed-basis
coordinate *vector* and state the degree statistic per component (matched by the same `ρ`-covariant null
of F1); OR restrict the primary domain to a genuinely cyclic `ρ`-stable subgroup containing both `±d`
images. Drop the "two arms agree on `D`" cross-check, or replace it with an arm-internal check that does
not equate the `ζ₄`-carrying and `ζ₄`-free domains.

---

## F3 — ABSOLUTE THRESHOLD `D ≤ N/3` IS CALIBRATED TO THE WRONG NULL  [secondary; ties to F1/DEVIATIONS D1]

**Clause.** Q3: *"'Low degree' is asserted only if `D ≤ N/3` AND `π ≤ 0.01` AND `INV` true …"*;
DEVIATIONS D1 asks the gate to confirm `D_q ≤ N/3` per factor for small `n`.

**Issue.** A `μ₆`-covariant interpolant on 31 points mod 631 generically has top degree `≈` the largest
`≤30` that is `≡ i₀ (mod 6)` (i.e. ~24–30), NOT `≤ N/3≈10`. So `D≤N/3` is not met by the forced symmetry
alone — good — but its justification requires the `D`-distribution of the **correct (`μ₆`) null**, which
the spec neither simulates nor states. As frozen, `N/3` is an uncalibrated absolute cut whose only
protection against F1's `π`-bias is coincidental. **Fix:** set the "low-D" call from the `μ₆`-null
`D`-distribution (e.g. `D_obs` below the null's 1st percentile) rather than a hard `N/3`; report the
`μ₆`-null `D`-histogram alongside `π`.

*(Credit: the None-vs-numeric asymmetry is genuinely resolved by D1 — on the large factor 631 all 31 `d`
are distinct so a numeric `D≤30` always exists for both real and null; None occurs only mod the small
factor 3, which D1 correctly excludes from the degree. This does not bias the headline `π`.)*

---

## F4 — FIRING CONTROL EXERCISES THE ENGINE, NOT THE NULL+p-VALUE PIPELINE  [secondary; §3 Q5]

**Clause.** Q5(i): planted `c*(d)=a₂d²+a₀` must return `D=2` and invert; the control is chosen so
"vanishing is not forced."

**Assessment.** As an **engine** firing control it is valid and un-forced (unlike the `VOID_anew` C4,
which could not fire on a supersingular `E`): `a₂=777,a₀=123≠0` is a genuine degree-2 signal, the fitter
returns `D=2`, `a₁≡0`, inversion recovers `d`. That clears the mechanical layer. **But** `c*` has
`a₀≠0`, so it does **not** satisfy `c(λd)=κc(d)` (that forces `a₀=0`), let alone the `ζ₄` law — so it
never exercises the **null-draw + permutation-`π`** code path under the covariance constraint, which is
where F1 lives and where a mis-implementation would hide. Q5's claim "exercise the same code path as the
real arm" is not met for the `π` pipeline. **Fix:** add (a) a `μ₆`-covariant *low-degree* plant run
through the FULL pipeline (fit + `μ₆`-null draws + `π`), requiring `π≤0.01` to fire; and (b) a
pure-`μ₆`-null calibration run requiring `π` uniform. Only then is the `π` machinery a validated
instrument.

---

## F5 — NO QUANTITATIVE POWER NUMBER; FALSIFICATION VIA `π` INHERITS F1  [secondary; §3 Q6]

**Clause.** Q6: `p=43` "weak power"; falsification `= high D OR π>0.01 OR INV false at p=43 OR D not
stable`.

**Issue.** (a) Power is stated only qualitatively ("weak"); no effect-size / detection-probability number
is given for any rung — a bound without a power number. (b) The `π>0.01` falsification arm is not
decisive while the null is the `μ₃` null (F1 biases `π` down); it becomes decisive only against the
`μ₆`-null. The `high D (>N/3)` and `D-not-stable` arms are null-independent and remain decisive.
**Fix:** state, per rung, the smallest `D`-gap the `μ₆`-null would flag at `π≤0.01` and with what
probability (compute now from the null `D`-histogram, F3); and mark the `π` falsification arm as
conditional on the F1 fix.

---

## Summary table

| # | layer | clause | defect | blocks run? |
|---|---|---|---|---|
| F1 | frame (matched null) | Q4 / §0 F2 | null omits forced `ζ₄`/`μ₆` covariance → `π` biased down a priori | **yes** — fix before run |
| F2 | frame/identifiability | Q1 | primary-domain single-valued `c(d)` not well-posed; `√−1 ∉ (Z/M)`; two-arms cross-check compares different objects | **yes** — fix before run |
| F3 | frame (threshold) | Q3 / D1 | `D≤N/3` uncalibrated to the correct null | recalibrate |
| F4 | mechanical (control) | Q5(i) | firing control tests engine, not null+`π` path | add controls |
| F5 | frame (power/falsif.) | Q6 | no power number; `π`-falsification inherits F1 | quantify + condition |

**Covered/sound as claimed:** exact-arithmetic CRT/Hensel fit (Q2), engine degree recovery on planted
data (Q5-i engine layer), the D1 per-large-factor reading and its resolution of the None asymmetry.

**One-line disposition.** Fold `ζ₄` into the null (F1) and well-pose `c(d)` on the primary domain (F2)
BEFORE unfreezing to run; with those two fixes the statistic becomes interpretable and F3–F5 are
mechanical follow-through. Until then a run's `π` (and the top row of the §2 outcome table) is
uninterpretable; only the raw degree-*bound* (bottom row) would survive.
