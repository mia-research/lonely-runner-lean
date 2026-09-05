# PRE-REGISTRATION — φ(n)-averaging / log-coordinate bridge for the amicable transfer (v1)

**Date 2026-07-23. Frozen before any statistic in §3 was evaluated on any curve.**
**Binding on:** any run reporting a "non-homomorphic amicable transfer", a "log-coordinate bridge", a
"Berry–Keating-type" or "φ(n)-averaging" result on the secp / amicable-pair object.

Computations permitted at spec time and performed: the §1 decidability analysis (algebra), the §2
forced-structure derivation (algebra), the §6 frame predicates, the §5 power arithmetic. **No statistic
of §3 has been evaluated on any curve.**

Inherited as given, verified against disk, **not re-tested here:** `RESULT_secp_amicable_pair_v1.md` /
§A1.2 (secp is a Silverman–Stange amicable pair; `t_N = 2 − t_p` is **correct but forced** by
`π_n = π_p − 1`); §A1.4 (the `log₂6` `Aut(E)` ceiling); `PREREG_amicable_correspondence_bits_v3.md` §1
T1 (the CM coordinate map **is** the discrete logarithm) and its Tier-A result; the recorded
`r = v − w` tautology failure (`feedback_residue_vs_component_tautology_2026_07_14`).

---

## 0. VERDICT ON THE HYPOTHESIS AS POSED — it is not decidable in the form given

The posed object is: *a φ(n)-averaging operator plus a logarithmic coordinate change providing a
non-homomorphic map carrying a localized geometric bias in `Z[ω]` on the field side (`F_p`) to the
scalar side (`F_n`), with the trace duality as matching boundary condition.* Three separate reasons it
cannot be registered in that form, each algebraic and pre-data:

**(0a) The φ(n)-average over the full group is the trivial operator.** `n` is prime, so `(Z/n)*` acts
**transitively** on `Z/n ∖ {0}`. For any `f`, `A f(d) := (1/φ(n))·Σ_{t ∈ (Z/n)*} f(td)` is a **constant
function**. The only non-degenerate versions average over a proper subgroup `H ≤ (Z/n)*`; in the log
coordinate these are **exactly** the isotypic projectors onto the multiplicative characters trivial on
`H`. "The φ(n)-averaging operator" is therefore not a new object — it is *the projection onto
characters of a fixed order*, and must be registered as such (which §3 does).

**(0b) The log coordinate cannot appear in a feature path.** The Berry–Keating coordinate change on the
scalar side is `ind_g : (Z/n)* → Z/(n−1)`. To apply it to a curve point `P` you must first produce
`d = dlog_G(P)` — the ECDLP. Per T1 the CM coordinate `φ : E(F_p) → Z[ω]/(π_p − 1) ≅ F_n` **is** that
discrete logarithm. So the "bridge", realized as an **evaluable map from points to partner-side
objects**, contains the ECDLP in its own construction. It is legal only on the **target / measurement**
side. Consequently: **no map, no attack shape, no bit statement.** What survives is a *dependence*
statement, and dependence is what §3 registers.

**(0c) "Non-homomorphic transfer" must be given a decidable rendering, since the homomorphic one is
proved absent.** `|E(F_p)| = n`, `|Ẽ(F_n)| = p`, `gcd(n,p) = 1` ⇒ every group homomorphism is trivial
(`Hom = 0`, §XII.4, correctly scoped). A non-homomorphic transfer is a **set map or correspondence not
required to respect either group law**. Exactly two decidable renderings are known to this project:

  - **(i) exact-symmetry rendering** — the group `Γ*(Φ)` of scalar multipliers under which a
    coordinate-computable label map is equivariant. **Already registered** in
    `PREREG_amicable_correspondence_bits_v3.md` ARM-A and run (Tier A: all four frozen features at
    their forced values, both arms). **Not re-registered here; this spec must not duplicate it.**
  - **(ii) graded-dependence rendering** — statistical dependence between a `d`-free, `Z[ω]`-valued
    field-side feature and a partner-side function of the scalar, measured on the μ₆-orbit quotient
    (which *is* the φ(n)-average over the `Aut`-subgroup, in the log coordinate). **This spec
    registers (ii).**

> **Therefore: the experiment as posed is replaced by the smallest decidable sub-question, specified in
> full below.** What the replacement does **not** cover is stated in §10 and is not to be quietly
> dropped: it does not construct a transfer map, does not evaluate anything without `d` in hand, does
> not test approximate (non-exact) equivariance of a label map, and produces **no bit and no attack**.

---

## 1. OBJECT (the registered sub-question)

### 1.1 Setting

`E_7 : y² = x³ + 7` over `F_p`, `p ≡ 1 mod 3`, `p > 7`, `n := #E_7(F_p)` **prime**. Then `Aut(E) = μ₆`,
`λ ∈ (Z/n)*` of order 3 is the GLV multiplier, and `n ≡ 1 mod 6` is forced (§Exp-1 §1.2 derivation).
`Ẽ := E_7` over `F_n`. The unit is **amicable** iff `#Ẽ(F_n) = p`.

**Where the trace duality enters, exactly.** `E` has CM by `Z[ω]`; `p = π π̄`, `π = π_p ∈ Z[ω]`,
`#E(F_p) = N(π − 1) = n`, and `t_n = 2 − t_p` is the universal identity `π_n = π_p − 1`. Hence there
are **two reductions of the same Eisenstein integer**:

```
Z[ω] ─→ Z[ω]/(π)     ≅ F_p        (field side)
Z[ω] ─→ Z[ω]/(π − 1) ≅ F_n        (scalar side)
```

The scalar side is a residue ring of `Z[ω]` **because of the trace duality** — that is the matching
boundary condition, in decidable form. Both fields therefore carry a cubic residue character
(`p ≡ 1 mod 3` and `n ≡ 1 mod 3`, both forced), valued in `μ₃ ⊂ Z[ω]`. This is the one legitimate sense
in which "a `Z[ω]` datum on the field side" and "a `Z[ω]` datum on the scalar side" are the **same kind
of object**.

### 1.2 Feature (field side) — `d`-free by construction

```
F(P) := χ₃^{(p)}( y(P) )  ∈ μ₃ ∪ {0}
```

computed from the **integer coordinate representative** `y ∈ [0,p)` and the public constants `(p, n, 7)`
only. `χ₃^{(p)}(a) := ω^k` where `a^{(p−1)/3} ≡ β^k`, `β` the fixed cube root chosen by the frozen rule
in §6.4 — pure integer exponentiation.

**Exact symmetry of `F` (derivation, pre-data):** `y(φP) = y(P)` (GLV fixes `y`) and
`χ₃(−y) = χ₃(−1)χ₃(y) = χ₃(y)` (since `−1` has order 2, coprime to 3, so `−1` is a cube).
⇒ **`F` is exactly constant on `μ₆ = ⟨λ,−1⟩` orbits of `d`.** This is *forced*, is declared here, and is
never counted as a finding.

### 1.3 Target (partner side) — uses `Ẽ`, built from the scalar

```
g(d) := χ₃^{(n)}( d³ + 7 )  ∈ μ₃ ∪ {0}
```

i.e. the cubic residue character over `F_n` of the **partner curve's right-hand side evaluated at
`x = d`**. It is a genuine partner-side object: `#Ẽ(F_n)` is exactly the count governed by
`χ₂^{(n)}(d³+7)`, and amicability is the statement that this count equals `p`.

**Exact symmetry of `g` (derivation, pre-data):** `λ³ ≡ 1 mod n` ⇒ `(λd)³ = d³` ⇒ **`g(λd) = g(d)`**;
and `g(−d) = χ₃^{(n)}(7 − d³) ≠ g(d)` in general. So `g` is μ₃-invariant, not μ₂-invariant.

### 1.4 The φ(n)-average, made explicit

Because `F` is exactly μ₆-invariant, `T` (§3) depends on `g` **only through its μ₆-orbit average**:

```
ĝ(d) := Σ_{h ∈ ⟨λ,−1⟩} g(h d) = 3·( g(d) + g(−d) ) = 3·( χ₃^{(n)}(d³+7) + χ₃^{(n)}(7−d³) )
```

**This is the φ(n)-averaging operator of the posed hypothesis, in its only non-degenerate form
(§0a): the average over the `Aut(E)`-subgroup `⟨λ,−1⟩ ≤ (Z/n)*`, which in the log coordinate is the
projection onto multiplicative characters trivial on that subgroup.** The registered test is exactly:
*does the field-side `Z[ω]` datum see the partner-side `Z[ω]` datum through that average?*

### 1.5 TAUTOLOGY HAZARD — addressed head-on

- **Disjoint construction.** `F` is a function of `(y mod p, p)` only; `g` is a function of
  `(d mod n, n, 7)` only. Neither is a sub-construction of the other; no residual of one is regressed
  on the other. The recorded failure mode — *never correlate `r = v − w` against `w`*, which produced
  `z ≈ +5000` and which **the shuffle control does not expose** — is structurally absent, because `F`
  and `g` share **no computed intermediate**.
- **Why the shuffle control alone would not have been enough.** Because the shuffle breaks an artifact
  exactly as it breaks signal, §4 does **not** rely on a shuffle. It uses (a) a **μ₆-equivariant**
  relabel null (which cannot break `F`'s forced symmetry) and (b) an **across-arm amicability control**
  (matched non-amicable curves, statistic defined identically). A tautology would survive (b) and would
  be exposed by it: an artifact of the `d ↔ P` bijection is present in **both** arms and cancels in the
  contrast.
- **Bijection is not leakage.** `d ↦ P_d` is a bijection, so an *injective* feature has saturated
  mutual information with `d` by construction; MI/"bits" statistics are therefore tautologically
  maximal here and are **barred** (the same reasoning as `PREREG_amicable_correspondence_bits_v3` §1A).
  `F` is 3-valued and `T` is a **character-pairing sum**, whose null distribution is fixed by the
  marginals — immune to that inflation.
- **`d` is used on the measurement side only.** `g(d)` requires `d`. That makes this a **dependence
  measurement**, not an evaluable feature, and it is labelled as such in every output. It licenses no
  statement of the form "an observer with `P` alone can compute anything".

### 1.6 What "non-homomorphic transfer" means here, decidably

> The registered decidable object is: **is the field-side cubic-residue class of a point's `y`-coordinate
> dependent on the partner-curve cubic-residue class of its scalar, after μ₆-averaging — beyond what
> matched non-amicable curves show?** A homomorphic transfer is excluded a priori (`Hom = 0`); a
> dependence of this kind requires no homomorphism, respects neither group law, and is exactly a
> non-homomorphic correspondence in the only sense that is measurable without constructing a map.

---

## 2. FORCED STRUCTURE (declared before the run; never counted as evidence)

With `F^i` and `g^j`, `i, j ∈ {1,2}`, reindexing `d ↦ λd` gives, using §1.2/§1.3:

```
T_{ij} = Σ_d F(P_{λd})^i · conj( g(λd)^j ) = 1^i · conj(1)^j · T_{ij}
```

— **no vanishing is forced**, because both `F` and `g` are μ₃-invariant. (Had the feature been
`χ₃^{(p)}(x(P))` instead, `F(P_{λd}) = χ₃(β)F(P_d)` and `T` would be **forced to 0** whenever
`χ₃^{(p)}(β) ≠ 1`, i.e. whenever `9 ∤ p−1`. That trap is recorded here so that a future run cannot
present a forced zero as a null.)

Reindexing `d ↦ −d` gives `T = Σ_d F(P_d)·conj(g(−d))`, hence `T` equals its own μ₂-symmetrisation —
**the identity of §1.4**, and again no vanishing.

**Forced rows that must behave (checked, reported, never counted as hits):**

| row | requirement |
|---|---|
| `F(P_{λd}) = F(P_d)` | exact, all `d`, all units |
| `F(P_{−d}) = F(P_d)` | exact, all `d`, all units |
| `g(λd) = g(d)` | exact, all `d`, all units |
| `Σ_d F(P_d)^i conj(g(λd)^j) = T_{ij}` | exact identity |
| `n ≡ 1 mod 6`, `3 \| n−1`, `3 \| p−1` | true on every unit |

Any failure ⇒ run **VOID**.

**Stratification variables, pre-computed and cheap:** `[9 | p−1]`, `[9 | n−1]`, `p mod 4`,
orientation (`p < n` or `p > n`). These are frame labels, computed before any `T`.

---

## 3. STATISTIC

### 3.1 Per-unit exact quantity (integers only, no float anywhere)

```
Σ_F  := Σ_{d=1}^{n−1} F(P_d)                     ∈ Z[ω]
Σ_g  := Σ_{d=1}^{n−1} g(d)                       ∈ Z[ω]
T(u) := (n−1)·Σ_{d=1}^{n−1} F(P_d)·conj(g(d))  −  Σ_F · conj(Σ_g)     ∈ Z[ω]
R(u) := N(T(u)) / ( (n−1)² · n )                 ∈ Q,  as an exact Fraction
```

`T` is the **exactly double-centred** pairing: the `Σ_F conj(Σ_g)` term removes the first-order marginal
product **exactly, in integers**, which matters because amicability pins `#Ẽ(F_n) = p` and therefore
constrains the partner-side marginal (a real confound, removed here by construction rather than by
matching alone). `N(a + bω) = a² − ab + b²` is the `Z[ω]` norm — an integer. Null scale: `E[R] ≈ 1`.

### 3.2 PRIMARY STATISTIC — exactly one

Per unit, the **exact permutation rank p-value** against NULL-A (§4.1) with `M = 9999` draws:

```
π(u) := ( 1 + #{ m : R^{σ_m}(u) ≥ R(u) } ) / (M + 1)          exact rational
```

**PRIMARY:** the **Mann–Whitney `W`** statistic comparing `{π(u) : u amicable}` against
`{π(u) : u matched control}` (§4.2), evaluated by the exact permutation distribution of `W`.
One statistic; pooled (not a max over cells); aimed at the amicability link, which is the only
structure the two arms differ in.

**Distribution under the null:** exactly the Mann–Whitney null (`W` uniform over the
`C(n₁+n₂, n₁)` labelings), computed exactly or by `10⁶` exact-integer resamples. No parametric
assumption anywhere.

### 3.3 Mandatory structural readouts (not tests; the anti-"bound-as-verdict" clause)

Reported for every unit, whatever `W` says:

1. `T(u)` itself, as an exact `Z[ω]` pair `(a,b)` — its **argument sector** among the 6 sectors of
   `Z[ω]` and its `μ₆`-class. A null in magnitude with a non-uniform **argument** distribution is a
   symmetry-type finding, and this readout is what makes it visible.
2. The exact 3×3 contingency table of `(F, g)` values over `d`, per unit (integer counts) — from which
   the *direction* of any dependence is readable, not just its size.
3. `R(u)` per stratum `([9|p−1], [9|n−1], p mod 4, orientation)`, reported separately, never pooled
   across strata in a verdict.
4. The measured `ε_min(u)` (§5), printed adjacent to every null statement together with
   `(p, n, orientation, stratum)`.

**Subspace clause.** If `W` is null, the report must state that the bound covers **the μ₆-averaged
cubic-character pairing only**, and list, in these words, what an effect living elsewhere would look
like: a different multiplicative order (`χ_k` for `k | n−1`, `k ≠ 3`); a non-μ₆-averaged component
(invisible here because `F` is forced μ₆-invariant — an effect supported on the μ₆-anti-invariant part
is **outside this statistic by construction**); a quadratic rather than cubic pairing; a joint
multi-point statistic.

### 3.4 Exploratory (declared now; cannot change any verdict)

The order-`k` sweep — `T_k := (n−1)Σ_d F(P_d)conj(χ_k^{(n)}(d³+7)) − …` for every `k | n−1`,
`k ≤ 12` — is the general φ(n)-averaging family. It is **EXPLORATORY**: it is a max/sweep over many
cells, upward-biased, and would require a max-matched null with the independent-cell count `#{k}` and
its dependence structure stated. It is reported under a heading `EXPLORATORY`, with the number of cells
printed, and it is barred from §9.

---

## 4. MATCHED CONTROLS

### 4.1 NULL-A (within unit) — μ₆-equivariant relabel

Draw `σ : (Z/n)* → (Z/n)*` uniformly from the bijections **commuting with the `⟨λ,−1⟩` action**:
choose a uniform permutation `τ` of the `(n−1)/6` orbit representatives and, independently per orbit,
a uniform `h_O ∈ ⟨λ,−1⟩`; set `σ(g·rep_O) := g·h_O·rep_{τ(O)}` for `g ∈ ⟨λ,−1⟩` (well defined; `μ₆`
abelian ⇒ `σ(gd) = gσ(d)`). Then `R^σ` is `R` computed with `F(P_{σ(d)})` in place of `F(P_d)`.

- **Preserves:** both marginals **exactly**; the exact μ₆-invariance of the feature (so the forced
  structure of §2 holds identically under the null — the §A2.7/D9 and M19 lesson); the `l²` scale.
- **Destroys:** only the pairing between a specific point's field-side class and its scalar's
  partner-side class.
- **Barred:** an unconstrained permutation of `d`. It destroys `F`'s μ₆-invariance, which `F` has **by
  definition of `Aut(E)`**, and would manufacture significance for every unit. Any run using it is VOID.

### 4.2 NULL-B (across units) — the amicability control, matched

For every amicable unit, one **non-amicable** control unit from the same family, matched on **all** of:

1. same frame conditions (§6.1), `n` prime;
2. same orientation class (`p < n` / `p > n`) — the D3 lesson from the prior amicable prereg;
3. same stratum `([9|p−1], [9|n−1], p mod 4)`;
4. `n` within a factor `1.25` of the amicable unit's `n`;
5. target-marginal vector `(#{g=1}, #{g=ω}, #{g=ω²})` within `2%` relative of the amicable unit's
   (a second line of defence; the §3.1 double-centring already removes the first-order term).

Matching is performed on **frame quantities only**, before any `T` is computed, by a deterministic
nearest-match rule logged in advance. **What NULL-B destroys: exactly the amicable / trace-duality
link. What it preserves: family, CM structure, μ₆ symmetry, marginals, size, orientation, stratum.**

### 4.3 Must-not-vary rows

- `T` computed by two independent code paths (direct sum vs. contingency-table contraction) must agree
  **bit-identically** as `Z[ω]` integers.
- `R` must be invariant under a generator swap `G → [s]G` **only after** the corresponding relabel of
  `d`; per §A6-1 a generator swap is a matched relabel and is **barred as a replication unit**.

---

## 5. PLANTED POSITIVE (must fire, or the arm is VOID)

**Synthetic transfer of tunable strength, exact, μ₆-preserving.** Fix `j* := 1`. Order the `(n−1)/6`
μ₆-orbits by a seeded deterministic rule; for level `ε` (exact `Fraction`), take the first
`⌊ε·(n−1)/6⌋` orbits and, on each, **overwrite** the feature by the orbit's target class:

```
F_plant(P_d) := χ₃^{(n)}( d³ + 7 )        (constant on the orbit, since g(λd)=g(d);
                                           and set to g(d) for the representative, extended
                                           μ₆-equivariantly — so F_plant stays μ₆-invariant)
```

Value counts are then re-matched to the original by a deterministic exact re-balancing pass, so the
plant changes **only** the pairing, not the marginal.

**Ladder, frozen:** `ε ∈ {1/2, 1/4, 1/10, 1/25, 1/50, 1/100, 1/250, 1/1000}`, 30 replicates per
`(ε, unit)`. **Detected** = `π(u) ≤ 0.005` in ≥ 24/30 replicates (power 0.8).
**`ε_min(u)` := smallest detected level, printed beside every null.**

**Analytic expectation, stated now (not a substitute for the measurement):** a planted fraction `ε`
contributes `|T| ≈ ε·(n−1)·(n−1)·c` with `c = Θ(1)`, giving `R ≈ ε²n`. Per-unit detection needs
`R ≳ 9` ⇒ **`ε_min ≈ 3/√n`**; at `n ≈ 8×10⁴`, `ε_min ≈ 1.1×10⁻²`. If the empirical `ε_min` exceeds
`3×` this the pipeline is attenuating and is repaired **before any null is read**.

**Second plant (tests the contrast, not just the detector):** inject `ε` into the **amicable arm only**
and require `W` to reject at `α = 0.01`; report the smallest such `ε`, `ε_min^W`.

---

## 6. SCOPE

### 6.1 Frame conditions

`E_7 : y² = x³ + 7`; `p` prime, `p ≡ 1 mod 3`, `p > 7`; `n = #E_7(F_p)` prime; `gcd(n, 42) = 1`.
Amicable iff `#Ẽ_7(F_n) = p` (verified by the exact CM point count, itself validated against the
`O(p)` character sum on the sub-`20000` range as in the prior run).

### 6.2 Units and the discovery / replication split — frozen now

The amicable frame below `p < 200000` (108 two-cycles × 2 orientations = 216 curves) already exists on
disk as a **frame enumeration** (`RESULT_amicable_correspondence_bits_tierA_v1.md`); no statistic of
this spec has been computed on it. To keep an out-of-sample arm:

- **DISCOVERY:** all frame units with `p < 50000`, plus their §4.2 controls.
- **REPLICATION (pre-committed, disjoint):** all frame units with `50000 ≤ p < 200000`, plus controls.
- **OUT-OF-SAMPLE (fresh, must be enumerated by the run):** all frame units with
  `200000 ≤ p < 2×10⁶`, plus controls.

**Replication criterion:** the sign of the `W` effect must agree between DISCOVERY and REPLICATION,
**and** the OUT-OF-SAMPLE arm must reject at `α = 0.01` on its own. Failing either ⇒
**chance pattern, not named** (two prior chance patterns died at this gate).

### 6.3 Counting rule

Report **distinct configurations**, not rows: a two-cycle contributes 2 orientations, and orientations
within a cycle are **not independent units** for the purpose of any invariance tally. Any statement of
the form "`k/k` units" must be preceded by the count of distinct configurations and the list of
algebraically forced agreements (§2), with only the **unforced** tally appearing in a conclusion.

### 6.4 Frozen conventions

`β :=` the cube root of unity in `F_p` given by `g^{(p−1)/3}` for `g` the least positive primitive root
mod `p`; `χ₃^{(p)}(a) := ω^k` with `a^{(p−1)/3} ≡ β^k`. Identically on the `n` side with `λ_n :=`
`h^{(n−1)/3}`, `h` the least positive primitive root mod `n`. `G :=` the first point produced by the
frozen rule (least `x ≥ 1` with `x³+7` a nonzero QR; `y` the smaller root as an integer).
**Convention dependence is real** (flipping a cube-root choice conjugates `T`), so: the conventions
above are frozen here, and `N(T)` — the primary input — is **convention-independent**, while the
§3.3-1 argument readout is reported **together with the convention**.

### 6.5 Toy-scale statement — what this does and does NOT license

> Every number this run produces is scoped to `y² = x³ + 7`, `p < 2×10⁶`, `n` prime, this generator
> rule, this statistic, these controls. secp's `p = 2²⁵⁶ − 2³² − 977` is **~236 binary orders of
> magnitude** outside that range. **A result at `p ~ 10³–10⁶` says nothing automatic at `2²⁵⁶`** — that
> is the project's standing rule and it governs every line of any result document from this spec.
> The one full-scale inherited fact (secp *is* an amicable pair, §A1.2) is **not** evidence about the
> statistic registered here.
> **No ECDLP, key-recovery, extraction, bit, or security claim is made or implied**, and none is
> derivable from a dependence measurement that requires `d` as an input (§0b).

---

## 7. FALSIFICATION (written before the run)

**The bridge hypothesis is dead if:** the plant fires (`ε_min ≤ 3×` analytic; `ε_min^W` finite) **and**
the primary `W` lies inside its exact null band (`α = 0.01`, two-sided) on the DISCOVERY set **and**
the per-stratum `R` distributions of the two arms are indistinguishable at the same level. Conclusion
then: *the μ₆-averaged cubic-character pairing between the field-side `Z[ω]` class of `y` and the
partner-curve `Z[ω]` class of the scalar shows no amicability-specific dependence above `ε_min`, at
`p < 2×10⁶`, this family.* Recorded as a **scoped magnitude bound with a power number**, never as a
closure, and never with the words *closed / no leakage / benign / generic / tautological /
at-the-floor*.

**The hypothesis is also dead** if the effect appears **equally in both arms** — that indicates a
property of the CM family, not of amicability, and must be reported as such (the honest positive
outcome of a null contrast).

**The run is VOID (no verdict in either direction) if:** any §2 forced row fails; the plant fails at
`ε = 1/2`; the two independent code paths for `T` disagree; NULL-A is implemented without the μ₆
equivariance; or `check_no_float.sh` fails.

---

## 8. EXACTNESS

**No float appears anywhere in this experiment's signal path, and no carve-out is required.**

- `χ₃`, cubic-residue symbols, primitive roots, point arithmetic, `d³ + 7 mod n`: Python `int`.
- `T ∈ Z[ω]` is stored as an integer pair `(a,b)`; `N(T) = a² − ab + b²` is an integer.
- `R = N(T)/((n−1)²n)` is an exact `Fraction`; the comparison `R^σ ≥ R` is an **integer
  cross-product** comparison (`N(T^σ)·(n−1)²n ≥ N(T)·(n−1)²n` reduces to comparing integers).
- `π(u)` is an exact integer ratio; `W` is an integer; its null is an exact combinatorial
  distribution.
- Banned operators (`/`, `float(...)`, `round`, `**0.5`, `math.*`/`np.*` on curve-derived values,
  `.astype(float)`) do not appear in feature, target, null, plant, or p-value code.

`check_no_float.sh` must pass before any `T` is computed.

---

## 9. PRE-COMMITMENT — outcome table (filled in BEFORE the run)

| # | Outcome | Pre-committed conclusion |
|---|---|---|
| **V** | Any §2 forced row fails, or plant fails at `ε = 1/2`, or the dual code paths disagree, or NULL-A lacks μ₆ equivariance | **VOID / PIPELINE DEFECT.** No verdict, no null, no positive. The failing control is the reported finding. |
| **1** | Plant fires; `W` rejects on DISCOVERY **and** sign replicates **and** OUT-OF-SAMPLE rejects at `α = 0.01` | **Amicability-specific dependence SUPPORTED** in the μ₆-averaged cubic pairing. Deliverable is the **characterization**: §3.3-1 argument sectors, §3.3-2 contingency direction, per-stratum sizes, `ε_min`, distinct-configuration count, scope banner. Explicitly: this is a dependence, **not** a map and **not** a bit (§0b). Next probe named: the order-`k` family with a proper max-matched null, and the quadratic (`χ₂`) analogue where amicability pins the marginal. |
| **2** | Plant fires; `W` rejects on DISCOVERY; replication or out-of-sample fails | **CHANCE PATTERN — NOT NAMED.** Reported with the failed replication printed; no ledger entry. |
| **3** | Plant fires; `W` inside band everywhere; both arms at the null level | **Bridge hypothesis FALSIFIED at the measured power.** Statement scoped exactly as §7, with `ε_min` and `ε_min^W` attached to the sentence. §3.3 readouts published so the result is a *shape*, not an absence. §10 exclusions restated verbatim. |
| **4** | Plant fires; `W` inside band, but **both** arms show `R` significantly above the NULL-A level | **A CM-family effect, not an amicable one.** Reported as a positive finding about the family with the amicability contrast explicitly null; a new prereg is required before any amicability language is used. |
| **5** | A stratum shows the effect and others do not | **Split before explaining** (the 122/206 = 67/67 \| 0/59 lesson). The rate is reported split by stratum; no pooled number is stated; the stratum boundary becomes the next object. |
| **6** | `T` is exactly `0` on some unit | Check §2 first — a forced zero from a convention slip is a **bug**, not a finding. Reported as an aborted unit until resolved. |

---

## 10. WHAT THIS EXPERIMENT DOES NOT COVER

Stated so the replacement in §0 cannot be quietly upgraded to the posed hypothesis.

1. **It builds no transfer map.** No object is produced that takes `P` to a partner-side element
   without `d`. §0b is the reason and it is algebraic, not practical.
2. **It says nothing about approximate equivariance.** Exact symmetry groups of label maps are
   `PREREG_amicable_correspondence_bits_v3` ARM-A's object (and its §2b names approximate symmetry as
   its own blind spot); this spec does not touch either.
3. **It cannot see a μ₆-anti-invariant effect.** `F` is forced μ₆-invariant (§1.2), so any dependence
   supported on the μ₆-anti-invariant part of the scalar side is **outside the statistic by
   construction**. That complement is named here, is untested, and is not bounded by any outcome above.
4. **It tests one character order (3) and one coordinate (`y`).** Orders `k ≠ 3` are EXPLORATORY only;
   `x`-based features are excluded here because they would be forced to zero whenever `9 ∤ p−1` (§2) —
   a separate spec with the `9 | p−1` stratum as its frame would be required.
5. **It is silent about `Hom = 0`.** That theorem is inherited and untouched; nothing here weakens or
   extends it.
6. **It licenses nothing at `2²⁵⁶`** (§6.5), and **no ECDLP / key / security statement** follows from
   any cell of §9.
