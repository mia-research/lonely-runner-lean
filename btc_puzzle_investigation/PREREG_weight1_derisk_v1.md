# PREREG — Weight-1 de-risk sweep (χ₂(y) sheaf on E: y²=x³+7)

**FROZEN 2026-07-24. This is a specification. It has NOT been run.** No `V(a)`, no eigenvalue,
no `W(p)` exists at freeze time. Only the SELECTION variables (`p`, `n=#E(F_p)`, primality, the
integer Hasse guard) were computed to freeze SCOPE — that is list-construction, not the experiment.

**No leakage, key-recovery, or ECDLP claim is made or attempted. This is the puzzle-free
pure-arithmetic study: the object contains no key. Nothing here transfers to `p = 2²⁵⁶−2³²−977`.**

Instrument on file: `n1_twisted_eigenvalues_v1.sage` (computes this object at `p=13,43`; its control
C2 recovers a planted eigenvalue 4-tuple to `4.4×10⁻¹⁶`). Budget clause: `PREREG_n1_phase_cap_v2.md`
§3.7 (ARM-3), which pre-committed `p ≤ 100`, `O(Σp⁴) ≈ 10⁸` field operations.

**Why this sweep exists.** `RESULT_n1_phase_cap_v3.md` §5 carries a ⚠ PROXY TAG: the whole N1
phase-language line (`|sin θ₁ + sin θ₂| ≤ 1`, the cap `S_y ≤ 2` read as a phase statement) rests on
the premise that **all four twisted Frobenius eigenvalues have modulus EXACTLY √p (weight exactly 1)
for all p**. A companion analytic proof claims this for all p; it is being checked separately. The
premise is empirically `[VERIFIED at p = 13, 43 only — six unforced μ₆ cells]`. This sweep is the
"check Claude can run": extend the DIRECT eigenvalue computation as far as `O(p⁴)` allows, so that a
mis-application of the citation is caught by a computed counterexample **before** the grade moves up.

---

## 1. OBJECT

The object is the multiset of the four Frobenius eigenvalues `{α₁,α₂,α₃,α₄}(a)` acting on `H¹` of the
twisted sheaf `χ₂(y_P)·χ_a(·)` over `E: y²=x³+7 / F_p`, and specifically their **moduli** `|αᵢ|`.
The weight-1 premise is the object-level statement `|αᵢ| = √p` for every `i` and every frequency `a`.

Computed exactly as the instrument does it:
- `E(F_p)`, `p ≡ 1 mod 3`, `n = #E(F_p)` prime, `G` a generator, dlog table `E(F_p) ≅ Z/n`.
- Exact-integer histograms `h_k[d] = Σ_{P∈E(F_{p^k}), Tr_{k/1}P = [d]G} χ₂(y_P)`, `χ₂(y)=y^{(pᵏ−1)/2}∈{±1}`, `k=1..4`.
- `V_k(a) = Σ_d h_k[d]·ζ_n^{ad}` (n-point transform); power sums `p_k(a) = −V_k(a)`.
- Newton's identities on `p_1..p_4` → degree-4 characteristic polynomial → its four roots `αᵢ(a)`.

**Tautology check (required before the run is valid).** Do the feature and the target share
construction such that the pipeline returns weight-1 by fiat? **No.** The eigenvalue moduli are the
roots of a quartic built from the four power sums; nothing constrains those roots to lie on the
circle `|z|=√p`. A non-pure sheaf (a weight-0 or weight-2 piece from a ramification/dimension
miscount) would produce a root off that circle and the pipeline would report it. This non-tautology
is **conditional on the planted control §4b firing** — if the pipeline returned `|α|=√p` regardless
of input, the test would be vacuous. §4b is therefore mandatory, not optional.

**Not a bare magnitude.** Weight-1 is a pass/fail on the moduli, but the object also carries phase
structure `arg αᵢ`, on which the *separate* phase-language claim depends. This sweep records the
sorted phase 4-tuple and conjugation-closure per cell as a **zero-verdict forced readout** (§4d),
scoped explicitly as feeding the `|sin θ₁+sin θ₂|≤1` question — which this sweep does NOT adjudicate.
If the weights all pass but a downstream anomaly lives in the phases, that lives in the recorded
phase 4-tuples, not in `W(p)`.

## 2. STATISTIC (exactly one; exact tolerance; decidable pass/fail)

> `W(p) = max over the (n−1)/6 distinct μ₆ configurations a, and over i=1..4, of  | |αᵢ(a)|/√p − 1 |`.

**Distribution under the null.** None — this is a **deterministic exact computation**, not a sample.
There is no sampling noise; the only stochastic-looking quantity is float round-off, which is bounded
and pushed far below τ by §8. `W(p)` is a single number per prime.

**Decision (frozen):** weight-1 HOLDS at `p` iff `W(p) < τ` with

> **`τ = 1×10⁻⁶`.**

Justification of τ (frozen, not tunable post-hoc):
- τ = 1e-6 is the tolerance **already coded** in the instrument (`C1: max(w) < 1e-6`, `C2: err < 1e-6`),
  so freezing it here introduces no new degree of freedom.
- It sits **≥10 orders above** the measured float floor: C2 recovers an exact-synthetic tuple to
  `4.4×10⁻¹⁶`, and §8 mandates ≥60-digit complex arithmetic for the `ζ_n` transform and the root-find,
  putting the accumulated floor at `~10⁻³⁰` even at the largest prime.
- It sits **≥5 orders below** the smallest weight departure of interest: a weight-0 contaminant
  contributes `||α|/√p−1| = |1/√p − 1| = O(1)`; a weight-2 contaminant `√p − 1 = O(√p)`. Any genuine
  non-purity is `≫ τ` at every prime in scope.
- **Noise-floor guard (frozen):** the run re-runs the exact-synthetic C2 path at each prime's scale
  and reports `W_floor`. If `W_floor > 10⁻⁹` at any prime (i.e. within 3 orders of τ), the instrument
  is declared MARGINAL at that prime and `W(p)` is NOT read as a pass — this keeps τ frozen while
  making the float budget auditable.

## 3. MATCHED CONTROL

A direct-verification sweep has no shuffle null; the failure mode to guard against is *the pipeline
reporting weight-1 by construction / vacuously*. The matched null is therefore the **off-weight
synthetic input** (§4b): it reproduces **every** structure the real path has downstream of the
histogram — the same Newton identities, the same quartic root-find, the same `|·|/√p` modulus map,
the same μ₆ bookkeeping — and destroys **only** the weight-1 property (one or more planted eigenvalues
placed off the circle `|z|=√p`). Preserves: pipeline, degree-4 structure, conjugation-closure.
Destroys: purity. If this matched-null input does not read `W ≫ τ`, the pipeline cannot see
non-purity and every "pass" it emits is uninformative.

## 4. PLANTED / FIRING CONTROLS (must fire, or the sweep is VOID)

**(a) C2 — solver recovery (already on file; re-run, must fire).** Plant a known weight-1 tuple
`√p·{ζ₆, ζ₆², ζ₆⁴, ζ₆⁵}`, synthesize `p_k = Σαᵢᵏ`, push through Newton→root→modulus, require
`max|recovered − planted| < 1e-6` (on file: `4.4×10⁻¹⁶`). Confirms Newton + root solver.

**(b) NEW — off-weight plant (the one that matters here; must fire).** Plant a 4-tuple that is NOT
all weight-1 but IS conjugation-closed (so it isolates the weight check from the conj check):

> `{ √p·ζ₆ , √p·ζ₆⁵ , 1 , p }`  — moduli `{√p, √p, 1, p}`: two weight-1, one weight-0, one weight-2.

Synthesize its power sums `p_k = −Σαᵢᵏ`, feed the SAME Newton→root→modulus pipeline, and require the
pipeline to report

> **`W = √p − 1 ≫ τ`** (e.g. `≈5.56` at p=43, margin `≥10⁶`).

If this does not fire, a pipeline that returns weight-1 by construction would pass §2 vacuously ⇒ the
sweep is VOID (see §9-iii). Note this tuple passes the conjugation-closure check (§4d) while failing
the weight check — demonstrating the weight statistic does independent work.

**(c) Sensitivity calibration (frozen sweep).** Plant `{ √p·e^{iθ}(1+δ), √p·e^{−iθ}(1+δ), √p·ζ, √p·ζ̄ }`
(conjugation-closed, real char poly), sweep `δ ∈ {10⁻⁸,10⁻⁷,…,10⁻²,10⁻¹,1}`, and record `δ_min`, the
smallest `δ` with `W > τ`. Because `W ≈ δ` for a single off-circle pair, `δ_min ≈ τ`. **Pre-commit:**
require `δ_min ≤ 10·τ = 10⁻⁵`; if `δ_min > 10⁻³` the instrument is too blunt and the run reports
MARGINAL-instrument rather than a pass. This answers "how far from √p must one eigenvalue be for the
check to catch it": the frozen answer to beat is `10⁻⁵` (a 0.001% modulus departure).

## 4d. FORCED READOUT CHECKS (zero evidence; all must print, none is a verdict)

- **μ₆ collapse:** `#distinct |V₁(a)|` over `a≠0` **equals** `(n−1)/6` (integer assertion). The
  denominator is `(n−1)/6`, never `n−1`; the group action is `a→λa` (sextic) composed with `a→−a`.
  If this count ≠ `(n−1)/6`, the μ₆ bookkeeping is wrong and the "distinct configurations" count is void.
- **Dimension / #R=4:** the characteristic polynomial must be degree 4 with 4 roots. If the solver
  returns fewer than 4 distinct-modulus roots, or a char poly whose roots are not closed under complex
  conjugation (non-real char poly), REPORT THAT (mis-typed object, §9-iv) — do NOT force a degree-4
  weight reading.
- **Conjugation-closure:** eigenvalue multiset closed under `z↦z̄` at every `a` (instrument's `conj_ok`).
- **k=1 sign convention:** the `p_k=−V_k` sign is FIXED by the k=1 weight reading, not assumed
  (per the instrument header); record that the chosen sign is the one making `|α|≈√p` at `k=1`.
- **Hasse guard (already applied at freeze):** every prime satisfies `(n−p−1)² ≤ 4p`, `isprime(n)`,
  `n ≡ 1 mod 6` — the integer, no-float guard that blocks the `ord(G)`-not-`#E` bug (v1 admitted
  `p=1951→n=5`). Confirmed on the frozen list at §6.
- **Phase 4-tuple (recorded, zero-verdict):** sorted `arg αᵢ/π` per cell — feeds the SEPARATE
  phase-language claim; NOT adjudicated here.

## 5. POWER (computed now, not after)

The computation is deterministic: there is no `n`-dependent detection probability in the usual sense.
Detection probability of a true per-eigenvalue modulus deviation `|δ| > τ + W_floor` is **1 (certain)**
at **every** prime in scope, because `W(p)` reads that deviation directly (`W ≥ |δ|`). The design has
**full power against the failure mode of interest** — a non-pure sheaf:
- weight-0 contaminant: `W = |1/√p − 1| ≥ 0.72` (min over scope at p=13; →1 as p grows) — margin over τ `≥ 7×10⁵`;
- weight-2 contaminant: `W = √p − 1 ≥ 2.6` (min over scope at p=13) — margin over τ `≥ 2.6×10⁶`.
The realized smallest-detectable deviation is `δ_min` from §4c, pre-committed `≤ 10⁻⁵`. A "null"
(all `W(p) < τ`) is therefore informative: it excludes any per-eigenvalue departure `> 10⁻⁵` across
every cell of every prime in scope — not a low-power bound.

## 6. SCOPE — the frozen exhaustive curve list

**This is a small finite population; the sweep is EXHAUSTIVE up to `P_max`, not sampled.** Every
`p ≡ 1 mod 3` with `#E(F_p)` prime and `p ≤ P_max`, computed at freeze time by an exact Legendre
point count `#E = p+1+Σ_x (x³+7 | p)` and the integer Hasse guard `(n−p−1)² ≤ 4p ∧ isprime(n) ∧ n≡1 mod 6`.

**Frozen list (superset, `P_max = 150`), SHA-256 `cb36465c6ac8d778d5068ee07b3567b81138a518aeecd5bf1702853a5d955bec`:**

| p | n=#E(F_p) | a_p=p+1−n | (n−1)/6 cells | p⁴ (k=4 cost) | cum cells | cum Σp⁴ |
|---|---|---|---|---|---|---|
| 13 | 7 | +7 | 1 | 28,561 | 1 | 28,561 |
| 43 | 31 | +13 | 5 | 3,418,801 | 6 | 3,447,362 |
| 61 | 61 | +1 | 10 | 13,845,841 | 16 | 17,293,203 |
| 67 | 79 | −11 | 13 | 20,151,121 | 29 | 37,444,324 |
| 79 | 67 | +13 | 11 | 38,950,081 | 40 | 76,394,405 |
| 97 | 79 | +19 | 13 | 88,529,281 | 53 | 164,923,686 |
| 127 | 127 | +1 | 21 | 260,144,641 | 74 | 425,068,327 |

`p=13,43` are the two already-verified primes (6 cells). The rejects at freeze time: `p≡2 mod 3`
(supersingular, `n=p+1` even, excluded by construction); composite `n`; Hasse-guard failures — none
of the p≡1 mod 3 primes ≤150 with prime `n` failed the Hasse guard.

**`P_max` choice (from a stated compute budget, decidable STOP rule).** Cost is `~p⁴` field ops for
the k=4 enumeration of `E(F_{p⁴})`. The instrument's inner loop is unoptimized (per-point EC
construction + 3 Frobenius modexps in `GF(p⁴)` + dlog lookup), so a field op costs `~10⁻⁵`s in Sage,
not the `~10⁻⁷`s pure-python floor.

- **PRIMARY: `P_max = 100`** — the 6 primes `{13,43,61,67,79,97}`, **53 unforced μ₆ cells**,
  `Σp⁴ ≈ 1.65×10⁸`. This is exactly §3.7's pre-committed budget and is the ~20-minute target
  (`1.65×10⁸ × 10⁻⁵`s ≈ 27 min at the unoptimized rate; ≈15 min if the inner loop is tightened).
  `p=97` alone (`8.85×10⁷`) dominates.
- **STRETCH: `P_max = 150`** — adds `p=127` (`2.6×10⁸`, more than the entire `P_max=100` run),
  `Σp⁴ ≈ 4.25×10⁸`, **74 cells**. Roughly `2.6×` the primary; only attempt if the primary finished
  well under budget.
- **`p ≥ 163` is out of a 20-minute budget** with the current instrument (`163⁴ ≈ 7×10⁸` for a single
  prime `≈2 h`); reaching further requires rewriting the histogram inner loop (vectorized trace,
  no per-point object construction). State this; do not silently truncate.
- **Decidable STOP rule (removes the guessed constant):** run primes in increasing `p`. Measure
  wall-clock `t_prev` at the largest completed prime `p_prev`. Before starting prime `p`, if
  `t_used + t_prev·(p/p_prev)⁴` would exceed **20 min**, STOP and freeze `P_max` at `p_prev`. Report
  the achieved `P_max` and its prime/cell count. This makes the cutoff a function of a *measured*
  constant, not a pre-guessed one.

Every number the run reports inherits this scope: `E: y²=x³+7`, `p ≡ 1 mod 3`, `n` prime,
Hasse-guarded, `p ≤ P_max`, exhaustive.

## 7. FALSIFICATION

Abandon the weight-1 premise (as applied here) iff: **`W(p) ≥ τ` at any `p` in the frozen list,
WITH the off-weight control §4b having fired at that prime's scale** (so we know the instrument can
report ≠ weight-1). Then report the prime `p`, the configuration `a`, and the offending modulus
`|αᵢ(a)|/√p`; the phase-language of the entire N1 line is WITHDRAWN and the citation is being
mis-applied. Conversely, if §4b does NOT fire, no `W(p)` reading falsifies anything — the sweep is
VOID (§9-iii).

## 8. EXACTNESS

- **Signal path is exact integer.** `h_k[d] = Σ χ₂(y_P) ∈ ℤ` (sum of ±1). The histograms — the only
  key-shaped quantity, though there is NO key in this object — are exact `int`. The integer Hasse
  guard and point counts are exact `int`, no `sqrt`, no float.
- **Float carve-out (analytic size only, no key in path).** Float/complex enters ONLY in (a) the
  n-point transform `V_k(a) = Σ_d h_k[d]·ζ_n^{ad}`, (b) Newton→charpoly over ℂ, (c) the quartic
  root-find, (d) `|α|/√p`. This is legitimate per CLAUDE.md: the signal (`h_k`) is exact; the complex
  arithmetic is a monotone size read whose threshold τ sits ≥20 orders above its round-off floor.
- **Precision floor (frozen hardening).** The `ζ_n` transform and the root-find must run at
  **ComplexField ≥ 200 bits (≈60 digits)** — matching the house `C-FFT` 60-digit cross-check — NOT
  the instrument's default 53-bit `CC`. This puts `W_floor ~ 10⁻³⁰`, so no float can decide the
  `τ=10⁻⁶` verdict. The §2 noise-floor guard reports `W_floor` per prime as evidence.
- **No transfer.** Grade cap `[VERIFIED-scope, p ≤ P_max]`, never `[PROVED]`. Nothing reaches
  `p = 2²⁵⁶`; only the separate analytic citation can prove all-p.

## 9. PRE-COMMITMENT (filled in BEFORE the run)

| # | Outcome | Conclusion (frozen) |
|---|---|---|
| **(i)** | `W(p) < τ` at ALL `p` in the frozen list, AND §4b fires at every prime's scale, AND all §4d forced checks pass | Weight-1 **`[VERIFIED-scope, p ≤ P_max, E:y²=x³+7, n prime, Hasse-guarded, exhaustive]`**. The premise's unforced-cell count rises from **6** to **53** (`P_max=100`, 6 primes) or **74** (`P_max=150`, 7 primes). Grade is `[VERIFIED-scope]` — **NOT `[PROVED]`** (only the separate citation proves all p). Update `RESULT_n1_phase_cap_v3.md` §5's proxy tag with the new cell/prime count. The phase-language tag stays on every downstream sentence; the sweep does not touch the `|sin θ₁+sin θ₂|≤1` question. |
| **(ii)** | `W(p) ≥ τ` at ANY `p` (with §4b having fired at that scale) | The premise is **FALSE at that `p`**. Report `p`, the configuration `a`, and `|αᵢ(a)|/√p`. **Withdraw the phase-language of the entire N1 line** (`RESULT_n1_phase_cap_v3.md` §5, §6): only the object-level `S_y ≤ 2` survives; the citation is being mis-applied. Do NOT enlarge scope to rescue it. |
| **(iii)** | §4b (off-weight plant) fails to fire — pipeline does not read `W ≫ τ` on a known non-pure input | **Sweep VOID.** Report an uninformative instrument. The premise tag is UNCHANGED (stays `[VERIFIED at p=13,43, six cells]`). No pass in (i) may be claimed while (iii) holds. |
| **(iv)** | §4d degree/conjugation check fails at some `p` (char poly not degree-4, or roots not conj-closed) | **Mis-typed object.** Report THAT (dim `H¹ ≠ 4`, or a non-real char poly) at the prime; do not force a weight reading. This is a finding about the sheaf's ramification/dimension, not a weight pass or fail. |

---

### Grade cap (restated, load-bearing)
The most this sweep can yield is **`[VERIFIED-scope, p ≤ P_max]`**. It can never yield `[PROVED]`:
a finite exhaustive check over `p ≤ 150` says nothing about `p = 2²⁵⁶` or all-p. A pass raises the
unforced-cell count and hardens the proxy tag; it does not close the N1 frontier and does not
substitute for the separate analytic proof. A single `W(p) ≥ τ` (with §4b fired) refutes the
application of that proof here.
