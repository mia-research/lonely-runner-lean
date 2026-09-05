# PRE-REGISTRATION — Orthogonal spectral projection onto the μ₃-complement (v1)

**Date 2026-07-23. Frozen before any statistic in §2 was evaluated on any curve.**
**Binding on:** any run reporting a μ₃-isotypic / GLV-projection result for the χ₂(y) twisted sum,
and on any run reporting an extremal-magnitude ("saturation", "½", "2√p cap") number for a χ₂ readout
on `y² = x³ + B`.

Computations performed at spec time and permitted: the §1.3 equivariance derivation (algebra, no
curve data), the §1.4 dimension count, the §6 frame-membership predicates, the §5 power arithmetic.
**No `V(a)` for any prime, readout, or frequency has been computed for this spec.**

Prior artifacts read and inherited as given (not re-tested here): `POSITIVE_FINDINGS_ADDENDUM_1_v1.md`
§A1.1, §A1.7, §A2.3, §A2.6; `RESULT_N1_reframed_2sqrtp_cap_v1.md` §1 and §4 (its §2/§3 are
**withdrawn as findings** and are treated here as **non-evidence**: no number from them is used to set
a threshold, a cell, a prime, or an expectation).

---

## 0. RELATION TO THE DISQUALIFIED STATISTIC CLASS (run-blocking preamble)

`PREREG_N1_eigenvalue_starvation_v1.md` §1a chose a **pooled exact 4th spectral moment**. §A2.6-2
records why that class is disqualified a priori:

> "dim 4" is a Weil bound on `max|V(a)|`. It is **not** a statement about DFT support. `χ₂(y_d)` has
> full-support, random-looking spectrum with `|V(a)| ~ √p` at typical `a`; the dimension manifests only
> in how few frequencies approach the ceiling — `O(1)` out of `n`, contributing `O(n)` against a bulk of
> `O(n²)`. **No bulk average over all frequencies can ever detect it.**

**Why the statistic of this spec escapes that disqualification, stated explicitly.**
The primary statistic (§2.1) is the **mean of the `k = 16` largest** values of `Q(a) = |V(a)|²/p` over a
frozen index set of independent frequency representatives. It is an **order statistic of fixed rank
depth**, not an average over the index set. Every frequency below the 16th order statistic contributes
**zero weight by construction**, so the `O(n²)` bulk that swamped the 4th moment is *excluded from the
functional*, not merely down-weighted. The `O(1)` ceiling-approaching frequencies §A2.6 identifies as
the carrier of the dimension are exactly the arguments of the functional. A top-`k` mean is also
**strictly lower-variance than a max** at the same tail depth (it averages `k` order statistics), which
is the project's stated preference over a max-of-noisy-cells; the residual upward selection bias is
removed because the identical `top-k`-of-`m` selection is applied to every matched-null draw (§3).

**Independent-frequency count, fixed now (§1.3 derivation, pre-data).** The number of independent
frequencies for a μ₃-invariant χ₂ readout is `m_eff = (n−1)/6`, **not** `n−1` and **not** `(n−1)/2`. Any
max- or tail-statistic null that uses `n/2` independent samples is mis-specified. This spec uses the
**same** index set of size `(n−1)/6` for **every** readout in every cell (§2.2), so the selection depth
is identical across cells by construction.

---

## 1. OBJECT

### 1.1 The curve object

`E_B : y² = x³ + B` over `F_p`, `B = 7` (primary family), `p` prime, `p ≡ 1 mod 3`, `n := #E(F_p)`
**prime**, `G` a fixed generator (the first generator returned by the frozen enumeration rule in §6.4).
`P_d := [d]G`, `x_d := x(P_d)`, `y_d := y(P_d)`.

For a function `f` on `E` with `f` not a square in the function field, the readout and its twisted sum:

```
c^f_d := χ₂( f(P_d) )   ∈ {−1, 0, +1}          (exact: Legendre symbol by integer exponentiation)
V_f(a) := Σ_{d=1}^{n−1} c^f_d · e_n(a d),        a ∈ Z/n
Q_f(a) := |V_f(a)|² / p
```

`dim H¹_c` of the associated Kummer sheaf `= #R(f)` (Euler characteristic on a genus-1 curve with a
tame rank-1 sheaf: `χ_c = 2 − 2g − #R = −#R`, `H⁰_c = H²_c = 0`), giving the ceiling
`max_a |V_f(a)| ≤ #R(f) · √p` in the convention used throughout this project. `#R(f)` is the number of
points of `E(F̄_p)` at which `ord(f)` is **odd**.

### 1.2 The μ₃ action, exactly

`p ≡ 1 mod 3` ⇒ `β ∈ F_p` with `β³ = 1, β ≠ 1`; `φ(x,y) = (βx, y)` is an `F_p`-endomorphism of `E`
(`(βx)³ + B = x³ + B`), `φ³ = 1`. Since `n` is prime, `φ` acts on `E(F_p)` as multiplication by
`λ ∈ (Z/n)*` with `λ² + λ + 1 ≡ 0 mod n`; in particular `3 | n − 1` and `n ≡ 1 mod 6` are **forced**.

**Orbit structure on `Z/n`.** `⟨λ⟩ ≅ μ₃` acts on `Z/n` by multiplication. `0` is fixed; on `Z/n ∖ {0}`
the action is **free** (`λd = d` with `d` invertible forces `λ = 1`), so there are exactly `(n−1)/3`
orbits, each of size 3. Adjoining negation, `⟨λ, −1⟩ ≅ μ₆` acts freely on `Z/n ∖ {0}` with exactly
`(n−1)/6` orbits of size 6.

**Dual action on frequencies.** The character group of `Z/n` is `Z/n` via `a ↦ e_n(a·)`; multiplication
by `λ` on `d` induces multiplication by `λ` (equivalently `λ⁻¹ = λ²`) on `a`, with the **same** orbit
structure: `(n−1)/3` free `μ₃`-orbits on the nonzero frequencies.

**"The coherent μ₃-residue modes", defined as a subspace.** Let `W = C[Z/n]` be the frequency space.

```
I  := { v ∈ W : v(λa) = v(a) for all a }          the μ₃-invariant (trivial-isotype) subspace,
                                                   dim I = (n−1)/3 + 1
I^⊥ = W_ω ⊕ W_{ω²},  W_ω := { v : v(λa) = ω·v(a) },  dim W_ω = dim W_{ω²} = (n−1)/3
```

`I` is the span of the μ₃-orbit indicator vectors; `I^⊥` is the orthogonal complement, the non-trivial
isotypes. **This is the subspace the hypothesis proposes to project onto.**

### 1.3 THE FORCED-ZERO THEOREM (tautology declaration — the hypothesis's mechanism is unavailable)

`φ(x,y) = (βx, y)` leaves `y` **unchanged**, so `y_{λd} = y(φ(P_d)) = y_d` **exactly**, hence
`c^{χ₂(y)}_{λd} = c^{χ₂(y)}_d`. Reindexing `d ↦ λd` (a bijection of `Z/n ∖ {0}`):

```
V_{χ₂(y)}(a) = Σ_d c_{λd} e_n(a λ d) = Σ_d c_d e_n((λa) d) = V_{χ₂(y)}(λa)      exactly.
```

Also `β` has odd order 3 ⇒ `β = (β²)²` is a square ⇒ `χ₂(β) = 1` ⇒ `c^{χ₂(x)}_{λd} = χ₂(βx_d) = c^{χ₂(x)}_d`,
so the same identity holds for `χ₂(x)`.

> **Theorem (pre-data, algebraic).** `V_{χ₂(y)}` and `V_{χ₂(x)}` lie **entirely in `I`**. Their
> orthogonal projection onto `I^⊥` is **identically zero, for every prime, at every frequency.**

**Consequence, stated as the design constraint.** The experiment "project the χ₂(y) readout onto the
orthogonal complement of the coherent μ₃-residue modes and measure the surviving mass" has a
**forced answer of exactly 0**. It is a tautology in the precise sense this project's rules name: the
feature (the μ₃-isotype decomposition) and the target (a readout whose μ₃-invariance is an identity of
the GLV endomorphism) **share construction**. Zero information; the statistic cannot fire; **any
"dilution factor" read off that projection is an artifact of the automorphism, not a measurement.**
The projection hypothesis, *in its literal form*, is therefore **not registered as testable and no run
may report it.** §1.5 registers the non-tautological shadow that remains.

Second consequence, carried into every null: `|V(−a)| = |V(a)|` (from `V(−a) = χ₂(−1)V(a)`, given) and
`V(λa) = V(a)` together mean the map `a ↦ |V(a)|` is constant on `μ₆`-orbits ⇒ **`m_eff = (n−1)/6`**.

### 1.4 What is NOT forced: readouts outside `I`

For `x₀ ∈ F_p*` with `x₀³ + B ≠ 0`, put `f_{x₀} := x − x₀`. Then `div(f_{x₀}) = (P) + (−P) − 2(O)` with
`x(P) = x₀`, so `#R = 2` (the pole at `O` has even order) — **the same ceiling `2√p` as `χ₂(x)`.** And

```
c^{f_{x₀}}_{λd} = χ₂(βx_d − x₀) = χ₂(β)·χ₂(x_d − β²x₀) = c^{f_{β²x₀}}_d
⇒ V_{f_{x₀}}(λa) = V_{f_{β²x₀}}(a),
```

i.e. `μ₃` **permutes the three readouts** `f_{x₀}, f_{βx₀}, f_{β²x₀}` rather than fixing any one of
them. So `V_{f_{x₀}} ∉ I` (unless `x₀ = 0`), and its energy is distributed over all three isotypes.

Analogously, with `x₁ ≠ x₂` in `F_p*`, `x_i³ + B ≠ 0`, and `{x₁,x₂} ≠ {βx₁, βx₂}` as sets:
`g_{x₁,x₂} := (x−x₁)(x−x₂)` has four simple zeros and a pole of order 4 at `O` ⇒ **`#R = 4`, ceiling
`4√p` — the same ceiling as `χ₂(y)`** — and is **not** μ₃-invariant.

And `h := x·y` has `div = (T₁)+(T₂)+(T₃)+(P)+(−P) − 5(O)` (all odd) ⇒ **`#R = 6`**, and
`χ₂(βx·y) = χ₂(x y)` ⇒ **μ₃-invariant**; while `h_{x₀} := y·(x − x₀)` has `#R = 6` and is **not**
μ₃-invariant.

**This yields a 3×2 design in which the nominal ceiling is held FIXED within each row.**

### 1.5 THE HYPOTHESIS ACTUALLY REGISTERED

> **H_proj (registered).** At **fixed** `#R` (fixed nominal ceiling, fixed `dim H¹`), the μ₃-isotype
> content of a χ₂ readout controls its **extremal** spectral magnitude: a readout confined to `I`
> attains a systematically smaller top-of-tail than a readout of identical `#R` spread across all
> three isotypes, by an amount **exceeding** what the symmetry constraint alone produces in a matched
> random ensemble.

> **H_pair (registered, Arm 2).** The twisted `H¹(a)` for `a ≠ 0` inherits an **even** Frobenius
> characteristic polynomial (eigenvalues pairing `{α, −α, γ, −γ}`) or another exact eigenvalue
> relation that caps the attainable trace below `#R·√p`.

H_proj is the only form of the projection idea that is not settled by §1.3. H_pair is the object-level
question left open by `RESULT_N1_reframed_2sqrtp_cap_v1.md` §3, restated as a decidable computation on
the eigenvalues themselves rather than on a magnitude.

---

## 2. STATISTIC

### 2.1 PRIMARY STATISTIC — exactly one

Frozen index set (§2.2) `A_rep`, `|A_rep| = m_eff = (n−1)/6`. For a readout `f` on a unit `u`:

```
S_f(u) := (1/16) · Σ of the 16 largest values of Q_f(a) over a ∈ A_rep          [k = 16, frozen]
```

**PRIMARY CONTRAST (the single number the run is judged on):**

```
D₄(u) := S_{χ₂(y)}(u)  −  S_{χ₂(g_{x₁,x₂})}(u)          (row #R = 4)
```

pooled over units by the **exact permutation rank** of `D₄(u)` in its matched-null distribution
(§3.1), combined across units by Stouffer `Z_pooled` computed from the exact rank p-values.
`Z_pooled` at row `#R = 4` is the primary readout. Nothing else is primary.

Null distribution of `D₄` under the matched null: empirical, from `M = 2000` matched draws per unit
(§3.1). No parametric distribution is assumed anywhere.

### 2.2 Frozen index set (identical across all cells — removes the selection-depth confound)

```
A_rep := { a ∈ [1, n−1] : a = min( orbit of a under ⟨λ, −1⟩, as integers in [1,n−1] ) }
```

`|A_rep| = (n−1)/6` exactly. Every cell — invariant and non-invariant, every `#R` — is evaluated on
**this same set**. For μ₃-invariant readouts this loses nothing (`Q` is orbit-constant); for
non-invariant readouts it is a deterministic fair subsample. **Consequence: `k = 16` out of the same
`m_eff` in every cell, so the top-`k` selection bias is identical and cancels in `D₄`.**

### 2.3 Cells (frozen). Rows are ceilings; columns are μ₃-isotype content.

| row | `#R` = dim `H¹` | ceiling | **`I`-confined (μ₃-invariant)** | **spread over `I^⊥` too** |
|---|---|---|---|---|
| **R2** | 2 | `2√p` | `χ₂(x)` | `χ₂(x − x₀)` |
| **R4 (PRIMARY)** | 4 | `4√p` | `χ₂(y)` | `χ₂((x−x₁)(x−x₂))` |
| **R6** | 6 | `6√p` | `χ₂(xy)` | `χ₂(y(x − x₀))` |

Parameter rule, frozen, deterministic: `x₀ :=` least integer `≥ 1` with `x₀ ≢ 0`, `x₀³ + B ≢ 0`,
and `x₀ ∉ {βx₀, β²x₀}` (automatic for `x₀ ≠ 0`). `(x₁,x₂) :=` lexicographically least pair of integers
`1 ≤ x₁ < x₂` with `x_i³ + B ≢ 0` and `{x₁,x₂} ≠ {βx₁, βx₂}` and `{x₁,x₂} ≠ {β²x₁, β²x₂}`. **These are
frame computations, not statistics; they are logged before any `V` is computed.**

**Cross-row comparisons (R2 vs R4 vs R6) are ceiling-confounded by construction and are BARRED from
every verdict.** They may be reported only in the form `S_f / #R²` and only under the label
"ceiling-normalised, confounded, not a test". The design's answer to the ceiling-confound question is:
**the test lives entirely inside a row.** §2.4 adds the second, exact, reason a within-row contrast is
not a normalisation artifact.

### 2.4 Must-equal exactness row (the `l²` budget is matched within a row)

For every readout, exactly, as an integer identity:

```
Σ_{a mod n} |V_f(a)|²  =  n · #{ d : f(P_d) ≠ 0 }
```

(`Σ_a e_n(a(d−d')) = n·[d=d']`.) Within a row the right-hand sides differ by at most 4 (the count of
zeros of `f` on the orbit), i.e. by `O(1/n)` relatively. **So the two cells of a row share both the
nominal ceiling and the exact `l²` budget; any `D₄ ≠ 0` is pure tail shape, not normalisation.**
If this identity fails at the integer level for any readout the run is **VOID**.

### 2.5 Mandatory structural readout (not a test; the anti-"bound-as-verdict" clause)

Reported for every unit and every non-invariant readout, always, whatever the primary says:

1. the exact energy split of `V_f` across the three isotypes,
   `E_ρ := Σ_{a} |⟨V_f, proj_ρ⟩|²` for `ρ ∈ {1, ω, ω²}`, as exact integer ratios of the total;
2. **which** isotype the top-16 frequencies of the non-invariant readouts fall in (a 16-vector of
   isotype labels per unit);
3. the empirical distribution of `Q_f` restricted to `A_rep`, as a 20-bin exact integer histogram, for
   every cell — so that a null on `D₄` still yields a *shape characterization*, never a closure.

**Subspace clause (project rule 4).** If `D₄` is null, the run must additionally report whether the
top-of-tail difference lives in a *sub*space not projected onto here — concretely, the isotype label
histogram of item 2 and the `#R = 2` / `#R = 6` rows. A null on `D₄` bounds the μ₃-isotype effect at
row `#R = 4` **at the measured power**; it says nothing about isotypes of other groups (`μ₂`
sub-structure, the sextic `μ₆` refinement, the `(a,b)` joint action of §A2.3), and the report must say
so in those words.

### 2.6 ARM 2 statistic — the eigenvalue multiset (exact algebra, not a statistic)

For a unit in the Arm-2 frame (§6.3) and a frequency `a`, define the base-changed power sums

```
S_k(a) := Σ_{P ∈ E(F_{p^k})}  χ₂^{(p)}( N_{F_{p^k}/F_p}( f(P) ) ) · e_n( a · dlog_G( Tr_k(P) ) ),
          Tr_k(P) := Σ_{i=0}^{k−1} Frob^i(P) ∈ E(F_p),   k = 1 .. #R
```

(`Tr_k` is the norm map to `E(F_p)`; the twisting character is the Lang-torsor character of `E(F_p)`
pulled back, so base change composes it with `Tr_k` — this is the standard base change of the sheaf.)
Newton's identities on `S_1..S_{#R}` give the characteristic polynomial `L(a,T) = Π(1 − α_i T)` with
coefficients in `Z[ζ_n]`. **Arm-2 output, per `(unit, a)`:**

- **is `L(a,T)` even in `T`** (all odd-index coefficients exactly `0` in `Z[ζ_n]`)? — decidable exactly;
- the purity check `|α_i| = √p` for all `i` (certified interval arithmetic, §8);
- the multiset `{α_i/√p}` and its argument configuration;
- whether `|Σ α_i|` is capped below `#R√p` by an exact algebraic relation among the `α_i`.

This arm returns a **symmetry type**, not a magnitude. It is the object-level answer to
`RESULT_N1_reframed_2sqrtp_cap_v1.md` §3 ("whether the *twisted* `H¹(a)` inherits the pairing of the
even untwisted char poly `t⁴ + mpt² + p²`").

**Pre-registered algebraic caution, so it is not discovered later:** if `L(a,T)` were even for `a ≠ 0`
then `Σα_i = 0`, i.e. `V_f(a) = 0` identically — which is not the case for a generic frequency.
Therefore **the naive pairing hypothesis is refutable by inspection at the first frequency computed**,
and H_pair's live content is the *weaker* relation (e.g. two eigenvalues in near-antipodal argument, a
`±` pairing on a 2-dim sub-quotient, or a Galois relation over `Q(ζ_n)`) that caps `|Σα_i|` without
forcing it to vanish. The arm reports the actual configuration either way. **This caution is recorded
now precisely so that "the strict pairing is false" cannot later be sold as a finding of the run: it is
a pre-data derivation.**

### 2.7 Exploratory (declared now; may not change any verdict)

Any sweep over `k ∈ {4, 64}` in §2.1, over `x₀`/`(x₁,x₂)` beyond the frozen choice, over `B ∈ {2, 11}`,
or over further `#R` values, is **EXPLORATORY**, is reported in a section headed `EXPLORATORY`, and is
barred from the outcome table of §9.

---

## 3. MATCHED CONTROL

### 3.1 NULL-A (primary) — symmetry-matched sign ensemble

For each readout `f` and unit `u`, `M = 2000` null sequences `c̃` are drawn uniformly subject to
**all** of:

1. **exact value counts** `#{c̃ = +1}, #{c̃ = −1}, #{c̃ = 0}` equal to the real readout's;
2. **the exact μ₂ relation the real readout has**: for `x`-based `f` (even in `d`, since `x_{−d} = x_d`)
   `c̃_{−d} = c̃_d`; for `f` containing `y` to odd order, `c̃_{−d} = χ₂(−1)·c̃_d`;
3. **the exact μ₃ relation the real readout has**: for `I`-confined readouts, `c̃_{λd} = c̃_d`; for
   non-invariant readouts, no μ₃ constraint (correct: a single non-invariant readout carries no
   internal μ₃ constraint — the relation `V_{f_{x₀}}(λa) = V_{f_{β²x₀}}(a)` links *different*
   readouts, not entries of one sequence).

**What NULL-A preserves:** the readout's own symmetry group, its value marginal, its `l²` budget
(§2.4), the frequency-set size, the top-`k` selection depth.
**What it destroys:** the arrangement the curve's group law produced — i.e. everything that is not
forced by the symmetry.

**This is the point of the design.** H_proj asserts an isotype effect *beyond* the symmetry-counting
effect. `D₄^null` (the same contrast computed on NULL-A draws) measures the symmetry-counting effect
itself and is reported as a number in its own right. The test is `D₄^real` against the `D₄^null` band.

**Why a plain shuffle is invalid here and is barred:** an unconstrained permutation of `c_d` destroys
the μ₃-invariance that `χ₂(y)` has **by definition of the GLV endomorphism** (§1.3). Against such a
null every μ₃-invariant readout would show a large spurious "effect" — the exact shape of the recorded
soft-shadow phantom (§A2.7-2, D9) and of the M19 μ₂-mismatch retraction. **Any run reporting a number
against an unconstrained shuffle for these readouts is VOID by this spec.**

### 3.2 NULL-B (secondary) — generator relabel, as a *must-not-vary* row, never as a replicate

`G' = [s]G` gives `P^{G'}_d = P^{G}_{sd}`, so `V^{G'}(a) = V^{G}(s^{-1}a)` and `S_f` is **invariant**
(the index set `A_rep` is not `s`-stable, so a small deterministic variation is expected and bounded).
Per §A6-1, a generator swap is the matched relabel null and **selects against** any real hypothesis;
it is therefore logged as a stability row (`|ΔS_f| / S_f` must be below a pre-declared `5%`) and is
**barred from use as a replication unit**.

### 3.3 Arm-2 control — a known-value eigenvalue computation

At `a = 0` the twisted sheaf is untwisted and the same `L(0,T)` is obtainable **independently** by
counting points of the curve `C_f : w² = f` over `F_{p^k}`, `k = 1..#R` (for `f = y` on `y²=x³+B`,
`C_y` has genus 3 by Riemann–Hurwitz, `2g−2 = 2(2·1−2) + 4`, new part of dimension 4). The Arm-2
pipeline must reproduce this polynomial **exactly**, coefficient by coefficient, by a code path that
does not read the point count. **If it does not, Arm 2 is VOID and reports nothing.** This is a
firing control whose correct value is known before the run.

---

## 4. PLANTED POSITIVE CONTROLS (each must fire, else the arm is VOID)

### P-1 — synthetic known-rank ladder (tests that the statistic has tail/rank resolution)

Sequences `c^{(r)}` of length `n−1` over `{±1}` constructed exactly so that `Q` has exactly `r`
frequencies at a planted magnitude and noise elsewhere, `r ∈ {1, 2, 3, 4, 6}`, run through the
**identical** `A_rep → Q → S` pipeline. **Requirement: `S` must be strictly increasing in `r`, with
each consecutive pair separated by ≥ 5 NULL-A band widths.** If it is not, the statistic has no rank
resolution ⇒ **PIPELINE DEFECT, no verdict in either direction** (the §A2.6 failure mode, prevented).

### P-2 — μ₃-equivariant magnitude injection into the real readout (gives `e_min`, the power number)

Frozen exactly, integers only. Fix `a₀ :=` least element of `A_rep`. Define the **μ₆-invariant** plant

```
r(d) := min{ (a₀ λ^j d mod n) , (−a₀ λ^j d mod n) : j = 0,1,2 }        (integer min)
s_d  := +1 if r(d) < (n+1)//2 else −1
```

`s` is constant on `⟨λ,−1⟩`-orbits by construction, so injecting it **preserves** the μ₃-invariance of
an `I`-confined readout — the plant does not break the symmetry the null carries. For level `e` (exact
`Fraction`), pick the first `⌊e·(n−1)/6⌋` orbits under a seeded deterministic order and set `c_d := s_d`
on them.

**Ladder, frozen:** `e ∈ {1/2, 1/4, 1/10, 1/50, 1/200, 1/1000, 1/5000, 1/20000}`, 30 replicates per
`(e, unit, readout)`. **Detected** = planted cell's `Q` exceeds the NULL-A 99.5% band in ≥ 27/30.
**`e_min(u)` := smallest detected level.**

Analytic expectation stated now, not as a substitute: planted mass `≈ e·n` against a `√p` scale ⇒
`e_min ≈ 4/√p`; at `n ≈ 10⁴`, `e_min ≈ 0.04`; at `n ≈ 10⁵`, `e_min ≈ 0.013`. If the empirical `e_min`
exceeds `3×` this, the pipeline is treated as attenuating and is repaired **before** any null is read.

**`e_min(u)` must be printed adjacent to every null statement, with `(p, n, B, #R, stratum)`. A null
without `e_min` attached is not a result.** For the non-invariant cells the plant is applied without
the μ₃ constraint (matching that cell's symmetry class).

### P-3 — planted isotype effect (tests that `D₄` can detect what H_proj asserts)

Construct a synthetic pair of sequences with identical value counts, identical μ₂ relation, identical
`l²` budget, one μ₃-invariant and one not, where the non-invariant one has a **deliberately** heavier
top-16 by a controlled amount `δ ∈ {50%, 20%, 10%, 5%, 2%, 1%}` of `S`. **`D₄` must detect `δ` down to
a level `δ_min`, reported.** If `D₄` cannot detect `δ = 50%`, the contrast is VOID.

---

## 5. POWER (computed now)

- **Per-unit, magnitude:** `e_min ≈ 4/√p` (P-2), verified empirically; at the discovery frame
  (`n ∈ [10³,10⁴]`) this is `e_min ≈ 0.04–0.13`, at the replication frame (`n ∈ [10⁴,10⁵]`)
  `e_min ≈ 0.013–0.04`. **A null on `D₄` is therefore a bound at the `e_min` injection level and at
  no finer level. It is not "no structure".**
- **Per-unit, contrast:** `S` is a mean of 16 order statistics from `m_eff = (n−1)/6` draws whose
  bulk scale is `Q ~ 1`. Under NULL-A the relative standard error of `S` is `≈ 1/√16 · σ_tail/μ_tail`;
  with `m_eff ∈ [160, 1.7×10⁴]` the top-16 mean sits at `Q ≈ 2·ln(m_eff/16)`-scale for a
  complex-Gaussian ensemble and its relative sd is `≈ 12–15%`. **Detectable per-unit `δ` at
  power 0.8, one unit: `δ ≈ 0.35–0.45` of `S`** — i.e. a *large* per-unit effect only.
- **Pooled:** 18 discovery units + 18 replication units, Stouffer over exact ranks ⇒ sensitivity
  improves by `√18 ≈ 4.24` ⇒ **pooled detectable `δ ≈ 0.08–0.11` of `S` at power 0.8, α = 0.01**.
  `δ_min` from P-3 replaces these estimates once measured; the estimate stands as the pre-committed
  expectation.
- **Arm 2:** not a statistical test. Its "power" is exactness: the eigenvalue multiset is either
  recovered with certified purity `|α_i| = √p` or the arm is VOID. With `≤ 6` units it has **zero**
  power for any distributional claim and none is permitted.

**Family-wise rule.** Family = 3 rows × 2 columns × units, but only **one** contrast (`D₄`, row R4) is
primary. Rows R2 and R6 are pre-declared **replication rows** for the same contrast; they are corrected
as 2 further tests at `α = 0.01/2` and are reported as replication, never as independent discoveries.
Everything else in §2.5/§2.7 is characterization and carries no α.

---

## 6. SCOPE

### 6.1 Frame conditions (all must hold; a unit failing any is excluded **and reported as excluded**)

`E_B : y² = x³ + B`, `B = 7`; `p` prime; `p ≡ 1 mod 3` (**required** — else `β ∉ F_p`, `φ` is not
defined over `F_p` and the whole μ₃ object is absent); `n = #E(F_p)` prime, `n > 3`.

**Stratification, and the collapse the task's stratification request undergoes — stated, not hidden.**
`p ≡ 1 mod 3` is forced by the frame, so a "`p mod 3`" stratification is **vacuous** and is not
performed. The surviving strata, jointly with `p mod 4`, are exactly three:

| stratum | condition | `p mod 12` | `A_new` | `m` (per §A2.1, `[EMPIRICAL]`, used as a *label* only) |
|---|---|---|---|---|
| **S1** | `p ≡ 1 mod 4` | 1 | ordinary | not defined by the `m`-law |
| **S2** | `p ≡ 3 mod 4`, `B` a cubic residue mod `p` | 7 | supersingular | `m = −2` |
| **S3** | `p ≡ 3 mod 4`, `B` a cubic non-residue mod `p` | 7 | supersingular | `m = 1` |

(`p ≡ 11 mod 12` — the `m = 2` cell — is **empty** in this frame, since it forces `p ≡ 2 mod 3`. Stated
so that its absence is not later read as a filter.) The `m` column is a **cheap pre-computed label**
(`p mod 12` + one cubic-residue symbol); it is `[EMPIRICAL]` per §A2.1 and is **never** used as
evidence, only as a stratum name.

### 6.2 Prime sets — IN-SAMPLE vs FRESH, frozen here

**IN-SAMPLE (any prime already appearing in §A2.6's table or in `RESULT_N1_reframed` §2):**
`991, 1051, 1237, 1249, 1303, 1669, 1831, 2089, 2143, 2251, 2281, 2503`.
These are run **first**, reported in a separate table, labelled **IN-SAMPLE**, and **may not appear in
`Z_pooled` or in any confirmatory statement.** They exist in this spec to detect pipeline regressions
against previously recorded behaviour, nothing else.

**DISCOVERY (fresh):** for each stratum S1/S2/S3, the **6 smallest** primes `p > 3000` satisfying §6.1
with `n ∈ [10³, 10⁴]`. **REPLICATION (fresh, disjoint decade):** for each stratum, the **6 smallest**
primes satisfying §6.1 with `n ∈ [10⁴, 10⁵]` — a decade disjoint from discovery.
Both lists are enumerated by a deterministic rule and **printed in the run log before any `V` is
computed**. No prime may be added, dropped, or substituted afterwards; a prime failing an exactness
row is reported as **aborted**, never silently removed (the recorded 8→3 silent-filter failure).

**Out-of-sample confirmation is required:** a `D₄` result named in any conclusion must agree in sign
with discovery in **≥ 16 of 18** replication units. Failing that ⇒ **chance pattern, not named.**

### 6.3 Arm-2 frame (separate, small, and honestly bounded)

Cost is `Σ_k p^k`. Frozen: `#R = 2` readouts (`k ≤ 2`) at `p ≤ 1000`; `#R = 4` readouts (`k ≤ 4`) at
`p ≤ 61`; `#R = 6` **not attempted**. Frequencies: `a = 0` (control) plus the 3 elements of `A_rep`
with the largest `Q` and the 3 with the smallest, per unit. Units: all frame-valid primes in range,
expected `≤ 6`. **This arm makes no claim about any `p` outside these bounds and no distributional
claim at all.**

### 6.4 Generator rule

`G :=` the point produced by: for `x = 1, 2, 3, …`, the first `x` with `x³ + B` a nonzero QR mod `p`,
taking `y :=` the smaller of the two square roots as integers in `[0,p)`. Deterministic, logged.

### 6.5 The scale banner — attached to every number this run produces

> Every number in this run is scoped to `y² = x³ + 7`, `p ≡ 1 mod 3`, `n` prime, `p ≤ 10⁵` (Arm 1) /
> `p ≤ 1000` (Arm 2), this generator rule, these readouts, these statistics. `p = 2²⁵⁶ − 2³² − 977` is
> **~239 binary orders of magnitude** outside this range. **No measurement here has power against a
> structure at `2²⁵⁶`.** No ECDLP, extraction, or security claim is made or implied.

---

## 7. FALSIFICATION (written before the run)

**H_proj is dead if:** `Z_pooled(D₄)` lies inside the NULL-A band (`|Z| < 2.58`, α = 0.01) on the
discovery set, **and** P-1 orders the synthetic rank ladder, **and** P-3 detects `δ ≥ 10%`, **and**
`e_min` is at or below `3×` its analytic expectation. Under those four conditions the conclusion is:
*at fixed ceiling `#R = 4`, μ₃-isotype content does not control the extremal spectral magnitude above
the `δ_min` level; the extremal magnitude of `χ₂(y)` is not a μ₃-projection effect.*

**H_proj is also dead if** `D₄^null` (the pure symmetry-counting contrast) accounts for `D₄^real`
within the band — i.e. whatever isotype-linked difference exists is **forced by the symmetry count**,
already established as information-free by §1.3.

**H_pair is dead if:** Arm 2 recovers, at `a ≠ 0`, a certified-pure eigenvalue multiset with **no**
exact algebraic relation among the `α_i` beyond purity and the Galois action, on **every** unit and
frequency computed, with the `a = 0` control reproducing the independently-known polynomial exactly.

**The whole run is VOID (no verdict in either direction) if:** P-1 fails to order; P-2 fails at
`e = 1/2`; P-3 fails at `δ = 50%`; the §2.4 integer identity fails; the §3.3 known-value control fails;
or any certified comparison in §8 cannot be certified at `B = 512` fractional bits.

**What a null does NOT license (project rule 4).** A null `D₄` is a **magnitude bound at `e_min` /
`δ_min`, in the top-16-of-`(n−1)/6` tail, on rows R2/R4/R6, for the μ₃ isotype decomposition only.**
It is not a statement that the extremal magnitude has no structure, and the words
*tautological / obstructed / benign / generic / at-the-floor / closed / no signal* are barred from the
result document. The structural readouts of §2.5 must be reported alongside it.

---

## 8. EXACTNESS (run-blocking, `btc_puzzle_investigation/CLAUDE.md` OVERRIDE)

**Integer/exact signal path.**
- `χ₂`, `χ₃`, cubic-residue symbols, `β`, `λ`, point arithmetic, `dlog`: Python `int` only.
- Autocorrelation `H_f[Δ] := Σ_d c_d c_{d+Δ}` computed **exactly** (NTT modulo primes with CRT, or
  direct integer convolution). `|V_f(a)|² = Σ_Δ H_f[Δ] e_n(aΔ)` is an exact cyclotomic integer
  determined by the integer vector `H_f`.
- The §2.4 identity is checked with pure integers via `n·H_f[0] = n·#{c_d ≠ 0}`.
- Permutation p-values, ranks, Stouffer inputs: exact integer counts / `Fraction`.

**Float carve-out, named and justified.** Ordering the real numbers `Q_f(a)` requires the complex
embedding. This is done in **fixed-point integer arithmetic** with `B ≥ 128` fractional bits and a
**certified error bound** `|err| ≤ (n + ⌈log₂ n⌉)·2^{−B}`; every order comparison used by the top-16
selection must be **certified** (intervals disjoint). If any pair of intervals overlaps, `B` is doubled
and the comparison retried, up to `B = 512`; failure to certify ⇒ run VOID. Purity checks in Arm 2 use
the same certified-interval discipline. **No key material, no `(n,k,D)` decomposition, and no target
passes through a float; the analytic size is the only quantity so evaluated**, exactly as the OVERRIDE
permits ("a float transform … allowed ONLY as a monotone statistic ranked against a matched permutation
null").

`check_no_float.sh` must pass on every signal-path file **before** any `V` is computed. The banned
operators (`/`, `float(...)`, `**0.5`, `math.*`/`np.*` on curve-derived values, `.astype(float)`) do not
appear in the readout, autocorrelation, null-construction, plant, or p-value code.

---

## 9. PRE-COMMITMENT — outcome table (filled in BEFORE the run)

| # | Outcome | Pre-committed conclusion |
|---|---|---|
| **A1** | P-1 ladder does not order, **or** P-2 fails at `e=1/2`, **or** P-3 fails at `δ=50%`, **or** §2.4 / §3.3 fails | **PIPELINE DEFECT.** No verdict on H_proj or H_pair in either direction. The failing control is reported as the finding. No null may be reported. (This is the §A2.6 outcome cell, honoured.) |
| **A2** | Controls fire; `Z_pooled(D₄)` outside band on discovery **and** sign replicates ≥16/18 | **H_proj SUPPORTED at row R4.** Report `D₄` with `e_min`, `δ_min`, stratum, scope banner. Report the §2.5 isotype-label histogram — the *characterization* is the deliverable, the magnitude is a size. Next probe named: the same contrast at rows R2/R6 and the `(a,b)` joint action of §A2.3. |
| **A3** | Controls fire; `Z_pooled(D₄)` outside band on discovery; replication **< 16/18** | **CHANCE PATTERN — NOT NAMED.** Reported as a discovery-set observation with the failed replication printed. No entry in any findings ledger. |
| **A4** | Controls fire; `Z_pooled(D₄)` inside band; `D₄^null ≈ 0` | **H_proj FALSIFIED at the measured power.** Statement: "at fixed `#R = 4`, μ₃-isotype content does not control the top-16 tail above `δ_min = …`, at `n ≤ 10⁵`, this family." Recorded as a **scoped magnitude bound with power**, not a closure; §2.5 readouts published; open complements listed (other isotypes, non-unitary transforms, higher-degree readouts, `p > 10⁵`). |
| **A5** | Controls fire; `Z_pooled(D₄)` inside band; `D₄^null` large and `D₄^real ≈ D₄^null` | **H_proj FALSIFIED, mechanism named:** the isotype-linked difference is entirely the symmetry count, which §1.3 shows is forced. Report `D₄^null` as the measured size of the forced effect. |
| **B1** | Arm 2 `a=0` control does not reproduce the independently-counted polynomial | **ARM 2 VOID.** No eigenvalue statement of any kind. |
| **B2** | Arm 2 fires; `L(a,T)` even at some `a ≠ 0` | Contradicts `V(a) ≠ 0`; ⇒ a **bug**, not a finding. Run is re-audited; nothing reported until resolved. |
| **B3** | Arm 2 fires; `L(a,T)` not even, but an exact relation among `{α_i}` caps `|Σα_i|` on every computed `(unit, a)` | **H_pair SUPPORTED, symmetry type named.** Report the relation and the argument configuration; this becomes the object-level statement of N1. Explicitly scoped to `p ≤ 61` (dim 4). |
| **B4** | Arm 2 fires; eigenvalues generic (purity + Galois only), no capping relation | **H_pair FALSIFIED at these units.** The `2√p`-scale extremal magnitude is *not* an eigenvalue-relation phenomenon at these `p`; recorded with `N ≤ 6` units and **zero distributional power**, as an existence statement about those units only. |
| **C1** | A frame prime's measured `m` disagrees with its §6.1 stratum label | Prime **aborted and reported as aborted**; the `m`-label is voided for that stratum; the disagreement is itself reported (it bears on §A2.1). |

**Nothing in this table permits the words "closed", "no leakage", "decisive", "generic", "benign", or
"the avenue is dead".** Every cell above produces either a characterization, a scoped bound with a
power number, or a declared defect.

---

## 10. WHAT THIS EXPERIMENT DOES NOT TEST

1. Non-unitary / oblique transformations of the frequency space (§A1.7-2 rules out only unitary ones).
2. Bases other than the `a`-Fourier basis; the joint `(a,b,c)` object of §A2.3/§A1.7 in any form.
3. Higher-degree (non-linear) or multi-point readouts.
4. Any μ₆ refinement beyond the μ₃/μ₂ split registered here; any isotype of any other group.
5. `p > 10⁵` (Arm 1) or `p > 1000` (Arm 2); the secp prime; any `B ∉ {7}` outside `EXPLORATORY`.
6. The sub-Rayleigh deficit (§A2.5) and the per-frequency conservation (§A5.17) — different objects,
   different statistics, not touched.
7. Anything about ECDLP, key recovery, or the security of secp256k1.
