# PRE-REGISTRATION — N1 Eigenvalue Starvation of the `chi2(y)` Twisted Sum (v1)

**Status:** PRE-DATA. Written before any measurement. **No data has been collected for this
question.** The `m`-closed-form (12 primes, 34/34 configurations) and the six-prime saturation
table quoted in §0 are *prior* results and are the motivation, not the evidence, for this drill.
**Date:** 2026-07-20
**Binding on:** any run reporting results for finding **N1** ("`chi2(y)` has 4 eigenvalues available
and delivers the magnitude of 2"), graded `unexplained`, twice attempted, twice not closed.
**Deviations:** any departure from this file must be listed in
`PREREG_N1_eigenvalue_starvation_v1_DEVIATIONS.md`. A deviation is not necessarily wrong — it is
necessarily disclosed.

---

## 0. OBJECT

### 0a. The mathematical object

Curve `E : y^2 = x^3 + B` over `F_p`, `#E(F_p) = n` prime. `C : w^4 = x^3 + B` is the degree-4
cyclic cover; `A_new` is the abelian surface in `Jac(C)` complementary to `E`. At `p = 3 mod 4` the
characteristic polynomial of Frobenius on `A_new` is

```
char(t) = t^4 + m*p*t^2 + p^2 ,        m = b_2 / p  in Z .
```

The object measured is the **twisted character sum family**

```
V(a) = sum_{d = 1}^{n-1} chi2(y_{[d]G}) * e_n(a*d) ,      a = 1 .. n-1 ,
```

together with the **exact integer autocorrelation** that generates it:

```
c(t) = sum_{d} chi2(y_{[d]G}) * chi2(y_{[d+t]G}) ,   t in Z/n ,   c(t) in Z ,
|V(a)|^2 = sum_{t in Z/n} c(t) * e_n(a*t) .
```

This is the object, not a proxy. The question "how many of the four Frobenius eigenvalues of
`A_new` carry weight-1 mass into `V`" is exactly a question about the spectral support of the
integer sequence `c(t)`. `c` is computed exhaustively over the whole group, not sampled.

### 0b. The measured anomaly this drill addresses (prior data, not this run's data)

Saturation `= (measured max over frequencies) / (dim * sqrt(p))`, six primes:

| readout | dim | saturation | range |
|---|---|---|---|
| additive `bx+cy` | 4 | 0.876 | 0.807–0.917 |
| additive `bx` | 3 | 0.909 | 0.809–0.964 |
| `chi2(x)` | 2 | 0.947 | 0.822–0.998 |
| **`chi2(y)`** | **4** | **0.470** | 0.432–0.500 (successive: 0.432, 0.455, 0.477, 0.459, 0.500, 0.499) |

Absolute magnitudes: `0.947 * 2*sqrt(p) ~ 1.89*sqrt(p)`; `0.470 * 4*sqrt(p) ~ 1.88*sqrt(p)`. In the
limit `0.470 -> 1/2` this is exactly `2*sqrt(p)`: **two eigenvalues at full weight-1 mass, two
contributing nothing.**

**Existing constraint the drill inherits.** The `bx+cy` readout has the *same* `dim = 4`, the same
ceiling, the same frequency count and the same estimator, and saturates 0.876 — a 1.86x systematic
gap at identical dimension. A max-over-frequencies upward bias cannot produce a *deficit*, and
cannot produce a deficit in one dim-4 row while the other dim-4 row saturates. This is recorded here
as the reason the anomaly is not an estimator artifact; it is **not** re-derived by this run.

### 0c. Prior killed mechanism — must be beaten, may not be re-proposed

Finding **M4**: `V(a)` is purely **real** at every `p = 1 mod 4` and purely **imaginary** at every
`p = 3 mod 4`. **The parity split does NOT cause the 1/2** — both residue classes sit at ~0.47.
Any mechanism whose content is the real/imaginary split is **already falsified** and may not be
advanced by this run in any form. A candidate mechanism that reduces to M4 under restatement is
counted as falsified, not as a finding.

### 0d. Tautology / forced-quantity check (run-blocking)

Two quantities in this neighbourhood are **algebraically forced** and therefore carry zero
information. Both are computed and printed as *identities to verify the pipeline*, never as
evidence:

1. **Second moment is forced by Parseval.**
   `sum_{a in Z/n} |V(a)|^2 = n * #{d : y_{[d]G} != 0}` exactly, independent of every hypothesis in
   this file. If the run reports this as support for anything, that report is void.
2. **Global negation of the eigenvalue multiset is forced.** Every regime's unitarized eigenvalue
   multiset in §0e is **closed under `alpha -> -alpha`** (verified below, pre-data, by exact
   cyclotomic arithmetic). Therefore "the `chi2` twist negates half the eigenvalues" is, *by
   itself*, a relabeling and predicts nothing. **The hypothesis is only testable in the sharpened
   form of §0f, which names the 2-dimensional subspace, not merely a sign.** This is the single
   most important pre-data constraint in this file.

### 0e. The eigenvalue regimes (pre-data algebra, no measurement)

`m` names all four eigenvalues; `k(m)` = smallest extension degree over which Frobenius is scalar.

| `m` | unitarized eigenvalues | relation | `k(m)` |
|---|---|---|---|
| `-2` | `{1, 1, -1, -1}` | `pi^2 = +p` | 2 |
| `2` | `{+i, +i, -i, -i}` | `pi^2 = -p` | 4 |
| `0` | primitive 8th roots | `pi^4 = -p^2` | 8 |
| `1` | `{+z12, -z12, +z12^5, -z12^5}` (primitive 12th) | `pi^6 = +p^3` | 6 |
| `-1` | primitive 3rd/6th roots | `pi^6 = -p^3` | 6 |

**`m` is predictable per `(p, B)` before any sum is computed**, by the exactly verified closed form
(12 primes, 34/34 configurations, exact cyclotomic arithmetic):

```
S = sum_{x in F_{p^2}} chi4(x^3 + B) = chi3(B) * J(chi3, chi4) + conj ,     m = Re(S)/p ,
J(chi3, chi4) = -p  (p = 1 mod 3)  ,  +p  (p = 2 mod 3) .
```

Consequences used to *select* the regimes in advance:

- `p = 11 mod 12`: `chi3` trivial on `F_p^*`, `S` independent of `B`, **`m = 2` uniformly**.
- `p = 7 mod 12`, `B` a **cubic residue** mod `p`: **`m = -2`**.
- `p = 7 mod 12`, `B` a **cubic non-residue**: **`m = 1`**.

These three cells are **structurally different eigenvalue configurations, selectable before
measurement by computing `p mod 12` and one cubic-residue symbol.** They are the independent arm.

**Pre-data coincidence counts** (computed by exact root-of-unity arithmetic before any data;
`N_coinc(m) = #{(i,j,k,l) in [4]^4 : alpha_i*alpha_j = alpha_k*alpha_l}`):

| `m` | `N_coinc` | distinct pair-products | neg-closed | squares of eigenvalues |
|---|---|---|---|---|
| `-2` | **128** | 2 | yes | `{1}` |
| `2` | **128** | 2 | yes | `{-1}` |
| `0` | **64** | 4 | yes | `{+i,-i}` |
| `1` | **48** | 6 | yes | `{z6, z6^-1}` |
| `-1` | **48** | 6 | yes | `{z3, z3^-1}` |

**Disclosed forced degeneracy (rule 5):** `m = -2` and `m = 2` have **identical** `N_coinc = 128`.
The primary statistic of §1 **cannot** separate them; their difference (`pi^2 = +p` vs `-p`) is
exactly the real/imaginary split that M4 already showed is *not* the cause. This degeneracy is
declared now so that agreement between the `m = -2` and `m = 2` cells on the primary statistic is
counted as **forced**, contributes **zero** to any tally, and may never be reported as replication.

### 0f. The hypothesis, in the only form that is testable

**H (sharpened).** The quadratic twist by `chi2(y)` acts as `-1` on a **specific 2-dimensional
Frobenius-stable subspace** `W_m` of the 4-dimensional `A_new` Frobenius module; the two starved
eigenvalues of N1 are exactly the eigenvalues of `pi` restricted to `W_m`. Because `W_m` must be
Frobenius-stable, its eigenvalue pair is constrained by the regime: `W_m` is spanned by a pair of
eigenvalues closed under the Galois action, i.e. a pair `{alpha, alpha'}` with `alpha*alpha'` fixed.

**H therefore predicts a regime-dependent surviving multiset**, hence a regime-dependent `N_coinc`
of the *surviving 2 eigenvalues*, hence a regime-dependent primary statistic.

**H0 (the weak rival, stated now).** The `1/2` is regime-independent: `chi2(y)` saturates at `1/2`
of `4*sqrt(p)` in every regime with no dependence on `m`. H0 is the hypothesis that survives if the
`m`-cells are pooled — which is why §4 **forbids pooling**.

**A hypothesis that predicts the same `1/2` in every regime is strictly weaker than one that
predicts regime-dependent saturation, and this file scores them differently (§10).**

---

## 1. STATISTIC

Exactly one primary statistic, named now. It is **pooled**, not a max.

### 1a. Primary statistic — exact fourth spectral moment

```
M4 := (1/n) * sum_{a in Z/n} |V(a)|^4  =  sum_{t in Z/n} c(t)^2        (exact integer)
```

The identity `(1/n) sum_a |V(a)|^4 = sum_t c(t)^2` is exact (Parseval applied to the integer
sequence `c`), so `M4` is computed as an **integer sum of squares of integers** — no transform, no
float, no max.

**Reported form (the test quantity):**

```
Q := M4 / p^2                (exact Fraction)
```

**Null model for `Q` (the "full 4 eigenvalues, no starvation" model).** For a weight-1 rank-4
family with eigenvalue multiset `A_m`, the leading term of the fourth moment is
`Q -> N_coinc(m)/ (normalisation)`. The **run does not fit this normalisation.** Instead the
normalisation is fixed by the **rank calibrators** of §3b, which are readouts of *independently
known* dimension measured through the identical pipeline:

```
rho(readout) := Q(readout) / Q(bx+cy)        (exact Fraction)
```

`bx+cy` is the dim-4, 0.876-saturating reference. `rho` is dimensionless, pipeline-normalised, and
is the number every conclusion is stated in.

**Pre-committed predictions (written before data).**

| cell | H (starved to a 2-dim Frobenius-stable subspace) | H0 (regime-independent 1/2) |
|---|---|---|
| `p=11 mod 12` (`m=2`) | `rho` tracks a **2-eigenvalue** multiset, and the surviving pair is `{+i,+i}` or `{+i,-i}` — these give **different** `rho`, and the run must report which | `rho` regime-independent |
| `p=7 mod 12`, `B` cubic residue (`m=-2`) | `rho` tracks a 2-eigenvalue multiset from `{1,1,-1,-1}` | same `rho` as above |
| `p=7 mod 12`, `B` cubic non-residue (`m=1`) | `rho` tracks a 2-eigenvalue multiset from the primitive 12th roots — **`N_coinc` differs (48 vs 128 at full rank)**, so `rho` must differ from the other two cells | same `rho` as above |

**The discriminating comparison, fixed now:** `rho(m=1)` vs `rho(m=2)` and `rho(m=1)` vs
`rho(m=-2)`. The `m=-2` vs `m=2` comparison is **forced-degenerate** (§0e) and excluded from the
discriminating tally.

### 1b. Secondary statistic — legacy saturation (reported, never a verdict)

```
sat := max_{a != 0} |V(a)| / (4 * sqrt(p))
```

retained **only** for comparability with the prior 0.470 figure. It is a max-over-frequencies and
is therefore upward-biased and low-power; **no conclusion in §10 may rest on `sat`.** It is printed
with its exact-comparison certificate (§7).

### 1c. Mandatory structural readout (not a test)

For every cell, the run must emit:

- the exact integer autocorrelation `c(t)` restricted to `t` in the subgroup(s) generated by the
  regime's relevant torsion, and its **support pattern**;
- the multiset of pair-products realised, compared against the §0e table;
- **which 2-dimensional subspace** the surviving mass is consistent with, named as an eigenvalue
  pair, not as a magnitude.

A magnitude alone is not an output (project rule 4).

---

## 2. NULL CONSTRUCTION (matched control)

### 2a. Matched null — group-automorphism relabeling (PRIMARY)

For uniform random `t in 2..n-1`, replace `G` by `[t]G`, i.e. pair `chi2(y_{[t*d]G})` with `e_n(a*d)`.

**Preserves:** the curve, the point set, the exact multiset of `chi2(y)` values, `#{y = 0}`, the
`mu6` orbit structure, the eigenvalue multiset of `A_new` (which depends on `(p,B)` only, not on the
generator), and the full second moment (which is forced anyway, §0d).
**Destroys:** only the alignment between the geometric character and the *particular* additive
character labeling.

This is the correct matched null because `d -> t*d` is an automorphism of the scalar group; it
cannot destroy a symmetry the readout has by definition. (This is the fix for the prior
"6–7 sigma soft shadow", which was a shuffle destroying a symmetry the readout possessed by
definition.)

**Pre-stated caveat:** `V(a)` under this null is `V(t^{-1} a)` — a *permutation of the frequency
axis*. Therefore **`M4` is exactly invariant under null 2a.** This is stated now, before data:
null 2a is a **forced-null control on `M4`**, not a significance null. Its role is to verify the
pipeline (`M4` must be bit-identical across all draws). If `M4` changes under 2a, the pipeline is
broken and the run is void.

### 2b. Matched null for significance — sign-randomisation preserving the marginal

Replace `chi2(y_{[d]G})` by `eps_d * chi2(y_{[d]G})` with `eps_d` iid uniform `{+1,-1}` from a
seeded CSPRNG (zeros preserved as zeros).

**Preserves:** the exact support (`{d : y = 0}`), the exact counts of `+1/-1/0` in distribution, the
second moment exactly.
**Destroys:** all spectral coherence — every eigenvalue structure, giving the `Q` of a rank-0
(pure-noise) sequence.

This null answers "is `Q` distinguishable from spectrally-structureless at all", and calibrates the
scale on which the regime differences of §1a are read.

### 2c. Regime-swap null (the null that isolates `m`)

Compare `Q` across primes **matched on `n`-decade, on `#{y=0}`, and on `p mod 4`**, differing only
in `m`. Preserves size, support, and the M4 real/imaginary parity; destroys only the eigenvalue
configuration. **This is the null that H must beat and H0 must fail.**

### 2d. Calibration requirement

For each prime: 200 draws of 2a (must be bit-identical), 400 draws of 2b. The empirical
distribution of `Q` under 2b is tabulated and its 0.5%/99.5% quantiles fixed as the structureless
band. No parametric distribution is assumed.

---

## 3. PLANT / POWER

### 3a. Magnitude plant (must fire) — exact, no floats

Half-plane sign sequence at a chosen frequency `a0`:

```
s_d^plant := +1 if (a0*d mod n) < (n+1)//2 else -1        (exact integer comparison)
```

Injection at level `e`: for a seeded pseudorandom subset `D_e` of size `floor(e*(n-1))`, set
`s_d = s_d^plant` for `d in D_e`, and `s_d = chi2(y_{[d]G})` otherwise. The planted spectral mass at
`a0` is of order `e*n`, against a ceiling of order `sqrt(p)`.

**Ladder (fixed now):** `e in { 1/2, 1/4, 1/10, 1/50, 1/200, 1/1000, 1/5000, 1/20000 }` (exact
Fractions). 30 replicates per `(e, prime)`. **Detected** = the planted cell's `Q` exceeds the 2b
99.5% band in >= 27/30 replicates.

**Power readout.** `e_min(p)` := smallest ladder `e` detected. **Analytic expectation, stated now,
not a substitute:** detection needs `e*n ~ 4*sqrt(p)`, i.e. `e_min ~ 4/sqrt(p)` (using `n ~ p`); at
`n ~ 10^5` this is `e_min ~ 1.3e-2`. If the empirical `e_min` exceeds 3x this, the pipeline is
treated as attenuating and the run is flagged for repair **before any null is reported**.

`e_min(p)` **must be printed adjacent to every null statement in every output document**, together
with `(p, n, B, m)`. A null without `e_min` attached is, by this file, not a result (project rule 3).

### 3b. Rank calibrators (the structure plant — must return known ranks)

The primary statistic is a **rank** readout, so its firing control must be a rank of known value.
Three readouts on the *same* curves, with independently known dimension, run through the identical
`c(t) -> M4 -> Q -> rho` pipeline:

| calibrator | known dim | required behaviour |
|---|---|---|
| `bx+cy` (additive) | 4 | defines `rho = 1` by construction |
| `bx` (additive) | 3 | `rho` must land strictly between the dim-4 and dim-2 values, ordered correctly |
| `chi2(x)` | 2 | `rho` must land at the dim-2 value, distinct from dim-4 at >= 5 x the 2b band width |

**Hard rule (project rule 2).** If the rank calibrators do **not** separate dim-2 from dim-4 by at
least 5 band-widths, **the `Q` statistic has no rank resolution**, the run yields **"pipeline
defect"**, and **NO null and NO positive may be reported.** Likewise if the magnitude plant fails at
`e = 1/2`. Multiple prior runs on this project were invalidated by controls that never fired.

### 3c. Unforced-hit accounting (project rule 5)

Before any invariance claim over `N` instances, the run must print:

1. the number of **distinct group configurations** actually present (regimes, `k(m)` values,
   `p mod 4` classes, generator classes) — not the number of primes;
2. the list of agreements that are **algebraically forced** and therefore excluded:
   - `m=-2` vs `m=2` on `Q` (forced-degenerate, §0e);
   - the second moment (forced, §0d);
   - `M4` invariance under null 2a (forced, §2a);
   - any agreement between two primes in the same regime with the same `k(m)` and the same
     `p mod 12` — these are **one** configuration, counted once;
3. the resulting **unforced** tally, as `unforced_hits / unforced_opportunities`.

**Only the unforced tally may appear in any conclusion.** A tally like "12/12 primes" is prohibited
where those 12 primes realise 3 distinct configurations; the permitted statement is "3/3
configurations".

---

## 4. FAMILY AND MULTIPLE-COMPARISON RULE

### 4a. Cells, frozen here — regimes are SEPARATE, never pooled

| cell | selection rule (pre-measurement) | predicted `m` | `k(m)` | primes |
|---|---|---|---|---|
| **R1** | `p = 11 mod 12`, any `B` | `2` | 4 | 6 |
| **R2** | `p = 7 mod 12`, `B` a cubic residue mod `p` | `-2` | 2 | 6 |
| **R3** | `p = 7 mod 12`, `B` a cubic non-residue mod `p` | `1` | 6 | 6 |

Per prime, per cell, the readouts are: `chi2(y)` (the object) plus the three rank calibrators of
§3b, plus the plant ladder.

**Pooling across R1/R2/R3 is prohibited.** A pooled number is not a permitted output of this run.
`m` is **verified** per prime against the §0e closed form before the sum is computed; a prime whose
measured `m` disagrees with the prediction **aborts that prime, is reported as aborted (never
silently dropped), and voids the closed form's use in that cell** — that disagreement is itself a
reportable finding (outcome cell **C1**).

### 4b. Family-wise rule

Family = 3 regime cells x 6 primes x 4 readouts = 72 statistics per replication set.
**Holm–Bonferroni at family-wise alpha = 0.01** across the 72, using the empirical 2b null.
Benjamini–Hochberg at FDR 0.05 printed as **SUGGESTIVE only**, never a finding.

The **discriminating** comparisons (§1a) — `rho(R3)` vs `rho(R1)`, `rho(R3)` vs `rho(R2)` — are
**two** pre-specified contrasts, corrected separately at alpha = 0.01 / 2. They are the primary
test. Everything else is characterization.

### 4c. Forced rows that must behave

- **Must-fire:** magnitude plant at `e = 1/2`; rank calibrators separating dim-2 from dim-4.
- **Must-not-vary:** `M4` under null 2a (bit-identical across 200 draws).
- **Must-equal:** second moment = `n * #{y != 0}` exactly.

If a must-not-vary or must-equal row deviates, the run is **void** and reports no verdicts.

---

## 5. OUT-OF-SAMPLE REPLICATION (project rule 6)

**No zero, no pattern, and no regime-difference is named until it replicates out of sample.**

- **Discovery set:** 6 primes per regime with `n` prime, `n in [10^4, 10^5]`, chosen as the smallest
  such primes satisfying the cell's selection rule, deterministic and listed in the run log before
  the sums are computed.
- **Replication set (fixed now):** 6 further primes per regime with `n in [10^5, 10^6]` — a
  **disjoint decade** — and **two generators each** (`G`, `[7]G`), giving 12 runs per regime.
- **Replication criterion (all three):**
  1. the sign and ordering of the regime contrast (`rho(R3)` vs `rho(R1)`, `rho(R3)` vs `rho(R2)`)
     agree with discovery in **>= 11 of 12** runs per contrast;
  2. the named surviving eigenvalue **pair** (§1c) is the same pair in every firing run;
  3. `|rho|` does not drop below the 2b band in any firing run.

Failing (1) => **chance pattern, not named** (two prior chance patterns died at this gate).
Failing (2) or (3) => **ABSTAIN**, listed as an open arm, never as a closure.

**Scaling arm.** An exponent in `p` may be fit **only if >= 6 distinct primes fire within a single
regime, each with `n >= 5000`**, and never from fewer. (A prior drill fit `|delta| ~ p^-0.36` from
three points, two of which had orbits `n = 146` and `n = 3353`.) Primes with `n < 5000` count toward
replication only, never toward a fit.

---

## 6. SCOPE

- Curve family: `y^2 = x^3 + B` over `F_p`, `p` prime, `#E(F_p) = n` **prime** (required; the
  generator then generates the whole group and `e_n` is a character of the full group).
- Generator rule, fixed now: `G` = the point obtained by the smallest `x >= 1` in `F_p` with
  `x^3 + B` a QR, taking the root `y < p/2`; second generator `[7]G`. No search over generators.
- `B` selection, fixed now: for R1, `B = 7`. For R2/R3, `B` = the smallest positive integer with the
  required cubic-residue class mod `p` such that `n` is prime.
- Regimes: R1 (`p=11 mod 12`), R2 (`p=7 mod 12`, `B` cubic residue), R3 (`p=7 mod 12`, `B` cubic
  non-residue). **6 primes per regime, discovery; 6 per regime, replication (disjoint decade), 2
  generators each.** Prime lists frozen and printed before any sum is computed.
- Scalars: **exhaustive**, `d = 1 .. n-1`. Frequencies: **all** `a != 0`.
- Nulls: 200 draws 2a, 400 draws 2b, per prime. Plants: 8 ladder values x 30 replicates x every
  prime.
- `p = 3 mod 4` is required for the `char(t) = t^4 + m*p*t^2 + p^2` form; both R2 (`7 mod 12`) and
  R1 (`11 mod 12`) satisfy `p = 3 mod 4`. This is a **restriction of scope**, disclosed here.

**Every number this run produces inherits this scope and may never be stated without it.**

---

## 7. EXACTNESS (run-blocking precondition, `btc_puzzle_investigation/CLAUDE.md` OVERRIDE)

- Field arithmetic, point arithmetic, `chi2`, `chi3`, `chi4`, the cubic-residue symbol, the
  autocorrelation `c(t)`, `M4 = sum_t c(t)^2`, and all counts: **Python `int` only**.
- `Q = M4/p^2` and `rho`: **`fractions.Fraction`**. All comparisons between `Q` values and all
  threshold decisions: **exact `Fraction` comparison**, never a float comparison.
- The `m` closed form (`S`, `J(chi3,chi4)`): **exact cyclotomic integer arithmetic**, as in the
  34/34 verification.
- The plant's half-plane rule uses the integer comparison `(a0*d mod n) < (n+1)//2`. No `math.*`.
- **`sqrt(p)` never appears in the signal path.** The secondary saturation `sat` (§1b) requires
  comparing an algebraic real `|V(a)|^2 = sum_t c(t) e_n(at)` against a rational threshold: this is
  done by **certified rational interval arithmetic** on the cyclotomic evaluation, refining the
  interval until the decision gap is strictly separated. If separation fails at the working
  precision, the run **reports "undecided" for that frequency** — it may not fall back to a float
  comparison.
- **Float carve-out (analytic size only, no key material in path):** the final *reported decimal
  rendering* of `Q`, `rho`, `sat`, and empirical null quantiles, for human reading only. No branch,
  no threshold, no cell assignment depends on a float. `check_no_float.sh` must pass on every
  signal-path file **before the run starts**; a failure blocks the run and no numbers are produced.

---

## 8. FALSIFICATION (written before the run)

**H is abandoned** — for this scope — if **all** of the following hold with the controls fired
(magnitude plant at `e_min <= 3 * 4/sqrt(p)`; rank calibrators separating dim-2 from dim-4 by
>= 5 band-widths; must-not-vary rows silent):

> `rho(chi2(y))` is statistically indistinguishable across R1, R2 and R3 at the pre-specified
> contrasts (both contrasts fail Holm at alpha = 0.01/2), **and** the same indistinguishability
> replicates out of sample in >= 11/12 runs per regime.

That is: **the starvation is regime-independent, so it is not carried by a Frobenius-stable
2-dimensional subspace `W_m` whose eigenvalue pair varies with `m`.** H as stated in §0f is then
dead, and H0 stands as a *sharper, still-unexplained* description of N1 — which is an outcome cell
(**N2**), not a closure.

**H is also abandoned** if the surviving pair named in §1c is inconsistent across primes *within* a
single regime (criterion 2 of §5) — that inconsistency refutes "a specific subspace".

**What does NOT falsify H:** a small `rho` difference below the measured detection floor. That is
an ABSTAIN (cell **A1**), not a falsification, and must be reported with `e_min`.

---

## 9. STRUCTURE CLAUSE — a bound is never a verdict (project rule 4)

If the regime contrasts do not fire, the run must additionally report **where the effect would have
to live to be invisible here**:

- the **`m=-2` / `m=2` forced degeneracy** (§0e): any mechanism distinguishing `pi^2 = +p` from
  `pi^2 = -p` is invisible to `Q` **by construction** and is untested by this run — it requires a
  statistic sensitive to the real/imaginary split, which M4 has already shown is not the *cause* of
  the 1/2 but has **not** been shown irrelevant to *which* pair survives;
- the **isotypic decomposition** of the surviving mass under the `mu6` action and under `mu_{k(m)}`,
  with a statement of which components the enumerated statistics project onto — mass supported
  entirely on a component orthogonal to `Q` is **not tested**;
- the sign pattern of `c(t)` on the torsion subgroups, reported as characterization with no p-value;
- the **subspace of statistics not covered**: odd moments, the 6th moment (sensitive to triple
  coincidences, which separate `m=1` from `m=-1`), and per-frequency phase structure.

"Signal" and "nothing" are not the only permitted outputs. **Abstention with a named subspace is a
permitted and expected output.** Dissolution of the anomaly is a **positive** outcome and has its
own cell (**D1**).

---

## 10. PRE-COMMITTED OUTCOME TABLE (written before data)

| # | Outcome | Pre-committed conclusion |
|---|---|---|
| **P0** | Magnitude plant does not fire at `e = 1/2` | **PIPELINE DEFECT.** No null, no positive, no bound may be reported. Repair and re-run. The run produces no verdict of any kind. |
| **P1** | Rank calibrators fail to separate dim-2 from dim-4 by >= 5 band-widths | **PIPELINE DEFECT — `Q` has no rank resolution.** Same consequence as P0. This is the control that matters most: without it, every `rho` number in this design is uninterpretable. |
| **P2** | `M4` varies under null 2a, or the second moment != `n*#{y!=0}` | **RUN VOID.** Report the defect; no cell verdicts. |
| **P3** | `check_no_float.sh` fails, or an interval comparison cannot separate at working precision | **RUN BLOCKED** (float) / that frequency reported **"undecided"** (interval). No float fallback. |
| **C1** | A prime's measured `m` disagrees with the §0e closed-form prediction | That prime **aborted and reported as aborted**. The disagreement is a **reportable finding about the closed form** (the `m` law is [EMPIRICAL], 34/34, and does not reach `2^256`), routed to its own pre-registration. It is not folded into this drill's tally. |
| **H1** | Both discriminating contrasts fire (Holm, alpha = 0.01/2), sign+ordering replicate >= 11/12, and the **same eigenvalue pair** is named in every firing run of a regime | **NAMED STRUCTURAL FINDING, scoped.** Report: the surviving 2-dimensional subspace `W_m` per regime **as an eigenvalue pair**, `rho` per regime with `e_min` and `(p, n, B, m)`, the unforced tally in **configurations** (max 3/3 discovery + 3/3 replication), and the `c(t)` support pattern. Conclusion is a scoped structural law for `n <= 10^6`. Extrapolation to `2^256` is **forbidden** by §11. Naming requires the mechanism to be **named** (which pair, which subspace), never "an unnamed symmetry" (project rule 7). |
| **H2** | Contrasts fire at discovery but replicate in < 11/12 | **CHANCE PATTERN. Not named.** Print the discovery statistic; propose no mechanism. |
| **H3** | Contrasts fire and replicate, but the named pair is **inconsistent** across primes within a regime | **ABSTAIN, OPEN ARM.** H's "specific subspace" clause is refuted (§8) while a regime-dependence survives. Pre-committed next step: a new pre-registration aimed at what the surviving pair *does* track (candidate: `k(m)` rather than `m`). Not a closure. |
| **H4** | Exactly one of the two contrasts fires and replicates | **PARTIAL, OPEN ARM.** Report the split rather than an average (a partial rate must be split before it is explained). Name which regime pair separates and which does not; that split is the object handed forward. |
| **N1out** | Controls fired; both contrasts fail Holm; indistinguishability replicates >= 11/12 | **SCOPED BOUNDED NULL + SHARPENED LAW.** Statement, verbatim: *"Across regimes R1 (`m=2`), R2 (`m=-2`), R3 (`m=1`), on 6+6 prime-order curves per regime with `n in [10^4,10^6]`, exhaustive over all `d` and all frequencies, the fourth-moment rank statistic `rho` of the `chi2(y)` twisted sum showed no regime dependence at family-wise alpha = 0.01, with detection floor `e_min = <value>` per prime. The N1 starvation is therefore, within this scope and floor, **regime-independent**: it is not carried by a Frobenius-stable 2-dimensional subspace whose eigenvalue pair varies with `m`."* This **may not** be written as "N1 is explained", "no structure", or "closed". §9 structure clause is mandatory. The anomaly remains graded `unexplained` and the regime-independence is the **new, sharper** constraint on any future mechanism. |
| **N2** | As N1out, and additionally `rho(chi2(y))` sits at the **dim-2 calibrator value** in every regime | **SHARPENED LAW (positive).** The starvation is a genuine rank reduction 4 -> 2 that is regime-independent — i.e. the `chi2` twist kills a 2-dimensional subspace that is *the same for every `m`*, hence defined over the base independent of the CM configuration. Named as a **next object**, with the pre-committed next probe: identify that base-defined subspace via the 6th moment and the `c(t)` support. Not a closure. |
| **A1** | A regime difference is present but smaller than the measured detection floor `e_min` | **ABSTAIN — POWER-LIMITED.** Report the observed difference, `e_min`, and the prime range. Pre-committed next step: **extend the prime ladder upward**, not re-analyze the existing data. |
| **D1** | The anomaly dissolves: `rho(chi2(y))` matches the dim-4 calibrator, i.e. no starvation at the moment level, and the 0.470 is confined to the max-statistic `sat` | **POSITIVE OUTCOME — DISSOLUTION, with a named mechanism required.** The finding becomes: *the 4-eigenvalue mass is present but is not concentrated at any single frequency*, i.e. N1 is a statement about **spectral spreading**, not about starvation. This must be stated with the named mechanism (which moment carries the mass) and re-registered; it may not be reported as "N1 was an artifact" without naming what spreads the mass. Dissolution is a positive result and is reported as prominently as H1. |
| **S1** | BH-suggestive only, replicates >= 11/12 | **SUGGESTIVE, OPEN ARM.** A candidate, not a finding. Requires a new pre-registration with that contrast as its single pre-specified target. |
| **M4-restatement** | Any proposed mechanism reduces, under restatement, to the real/imaginary parity split | **ALREADY FALSIFIED (§0c).** Not reportable as a finding in any form. |

**Nothing outside this table may be reported as a conclusion.** Post-hoc statistics computed on this
data go under a heading literally titled `EXPLORATORY (NOT PRE-REGISTERED)`, and **may not override
a fired outcome cell.** If a cell in this table fires, its pre-committed conclusion is section 1 of
the report.

---

## 11. SCOPE / POWER LIMITATION — INCLUDING THE `2^256` GAP

1. **What this run has power against.** Regime-dependent rank differences in `Q` of size above the
   2b band, at `n in [10^4, 10^6]`, with magnitude floor `e_min ~ 4/sqrt(p)` (empirical `e_min`
   supersedes). The `N_coinc` gap between `m = 1` (48) and `m = 2 / m = -2` (128) is a **factor
   ~2.7 at full rank** — a large, scale-free structural difference, which is why this design is
   built on it rather than on a small bias.
2. **What this run has NO power against.** (a) The `m = -2` vs `m = 2` distinction — forced-degenerate
   under `Q` (§0e). (b) Any effect confined to odd moments or to per-frequency phase. (c) Anything
   suppressed like `p^-1/2`: at `p ~ 2^256` such an effect is of order `2^-128` and requires `~2^256`
   samples. **This run has, by construction, zero power against square-root-suppressed structure at
   cryptographic scale.**
3. **The only permitted bridge to larger `p`.** An exponent fit from **>= 6 primes within a single
   regime, each with `n >= 5000`** (§5), reported with its interval and the explicit statement that
   no measurement above `n ~ 10^6` was made. Fewer points: prohibited, regardless of how clean.
4. **A null here is a null at `n <= 10^6`.** It bounds regime-dependence of the rank statistic in
   the enumerated regimes at the measured primes, and nothing more.
5. The `m` closed form is **[EMPIRICAL]** (12 primes, 34/34 exact configurations). It is used here
   as a **selection rule**, and every use is verified per prime (§4a, cell C1). Its own extension to
   `2^256` requires a closed-form Jacobi-sum argument that is **not** part of this drill.

---

## 12. WHAT THIS EXPERIMENT DOES NOT TEST

1. **`m = 0` and `m = -1` regimes.** Not in scope (their selection rule is not a simple congruence +
   cubic symbol). Nothing here speaks to primitive-8th or primitive-3rd/6th configurations.
2. **`p = 1 mod 4`.** The `t^4 + m*p*t^2 + p^2` form is used at `p = 3 mod 4`; R1 and R2/R3 are both
   `3 mod 4`. The `p = 1 mod 4` half of the M4 parity observation is untested here.
3. **The `m = -2` vs `m = 2` separation** — forced-degenerate under the primary statistic (§0e, §9).
4. **Odd moments, the 6th moment, and per-frequency phase structure** — the statistics that would
   separate `m = 1` from `m = -1` and detect phase-only effects.
5. **Curves with non-prime `n`, twists, or `B` outside the fixed selection rule.**
6. **secp256k1 itself.** No measurement at `p ~ 2^256` (§11).
7. **Any generation-side / PRNG question.** Out of scope by project policy and by construction:
   `d` ranges exhaustively over the full group, not over any key-generation distribution.
8. **Any ECDLP or cryptographic-security claim.** **Neither a null nor a positive nor a dissolution
   in this drill constitutes any statement about ECDLP hardness, key recovery, or the security of
   secp256k1 or any deployed system.** No outcome cell in §10 licenses such a statement, and any
   document quoting this run must carry this sentence.
9. **A verdict of any kind on N1.** N1 is graded `unexplained`; this drill can sharpen it, bound it,
   dissolve it into a named different phenomenon, or abstain. It cannot close it.

---

## 13. RUN CHECKLIST (all must be logged in the output)

- [ ] `check_no_float.sh` PASSED on every signal-path file, before the run (§7)
- [ ] prime lists per regime R1/R2/R3 printed **before** any sum is computed (§4a, §6)
- [ ] `m` verified per prime against the closed form; disagreements reported as aborted (§4a, C1)
- [ ] second moment `= n * #{y != 0}` exactly, every prime (§0d, §4c)
- [ ] `M4` bit-identical across 200 draws of null 2a (§2a, §4c)
- [ ] null 2b band (0.5%/99.5%) from 400 draws, per prime (§2d)
- [ ] **magnitude plant ladder table; `e_min(p)` per prime** (§3a)
- [ ] **rank calibrators: dim-2 vs dim-4 separation in band-widths** (§3b) — if < 5, STOP
- [ ] unforced-hit accounting: distinct configurations counted, forced agreements listed and
      excluded, tally reported as `unforced/opportunities` (§3c)
- [ ] `rho` per regime, exact Fraction + decimal rendering, with `(p, n, B, m, e_min)` on every
      number (§1a, §6)
- [ ] the two discriminating contrasts, Holm at alpha = 0.01/2 (§4b)
- [ ] out-of-sample replication counts per contrast, >= 11/12 rule applied (§5)
- [ ] named surviving eigenvalue **pair** per regime, or explicit ABSTAIN (§1c, §5 crit. 2)
- [ ] legacy `sat` printed with interval-arithmetic certificate; any "undecided" frequencies listed
      (§1b, §7)
- [ ] §9 structure clause emitted if the contrasts do not fire
- [ ] outcome cell from §10 named explicitly; conclusion **copied verbatim** from that cell
- [ ] the §12.8 no-ECDLP-claim sentence reproduced in the output document
