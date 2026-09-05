# PREREG — Cap Mechanism Discrimination (`|V(a)| ≤ 2√p`)

**Status: PRE-REGISTRATION. Written before any run. Spec only — NOT executed.**
Date: 2026-07-24 · Object: the character sum `V(a) = Σ_{P∈E(F_p)} χ₂(y_P) χ_a(P)`,
`E: y²=x³+7`, `n=#E(F_p)` prime, `a∈(Z/n)*∖{0}`. Instrument:
`/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/n1_twisted_eigenvalues_v1.sage`.

**Purpose.** The bound `|V(a)| ≤ 2√p` is `[VERIFIED — out-of-sample, 120 primes, ~4.7M configs]`,
NOT proved. This spec pre-registers a numerical test of *which* mechanism (M1–M4) confines the
sum, so a proof has a concrete target. A numerical run can only move a mechanism to
`[SUPPORTED]`/`[REFUTED]` as a *signature*; the cap itself stays `[VERIFIED]`, never `[PROVED]`,
from any run here.

---

## 0. Standing corrections to the task's framing (surfaced before committing the design)

These change the scope and the null; they are load-bearing and pre-registered.

**(A) The `O(p⁴)` wall does NOT bind the mechanism question.**
The cap and every mechanism signature depend only on `(e₁,e₂)`, the two free char-poly
coefficients. By the given forced form `P(t)=t⁴−e₁t³+e₂t²+p·e₁·t+p²`, the pieces `e₃=−p·e₁`
and `e₄=p²` are fixed by the functional equation (purity, weight-1, det=p² — all `[PROVED]`).
By Newton's identities, `e₁ = p₁ = −V₁`, `e₂ = (p₁²−p₂)/2 = (V₁²−V₂)/2`. So the discriminating
observables need only `V₁,V₂` — histograms `k=1,2` over `E(F_p), E(F_{p²})`, cost **O(p²)**.
The `O(p⁴)` histogram `V₄` (the thing that did not finish p=61 in 9 min) is needed ONLY to
*re-verify* purity (`e₃=−p·e₁`, `e₄=p²`, `|α_i|=√p`), which is already a theorem. Purity's
empirical re-check is an **instrument self-test**, not a mechanism gate. Consequence: the
mechanism tests reach far larger `p` than the task's `{13,43}` premise assumed.

**(B) The `(n−1)/6` μ₆-cells of one prime are a SINGLE Galois orbit — the independent unit is the
prime, not the cell.** `Gal(Q(ζ_n)/Q)=(Z/n)*` acts transitively on `(Z/n)*`, hence transitively
on the `(n−1)/6` μ₆-cosets. So `{(e₁(c),e₂(c)) : c a cell}` for one prime is the conjugate set of
ONE algebraic number; the cells are NOT independent Bernoulli trials. Per the anomaly-drill rule
"count DISTINCT configurations / don't overcount forced bits," the headline `N` for power is the
**number of primes**, not `Σ (n−1)/6`. Reporting cell-count `N` would inflate power exactly like
`792/792 = 99 forced bits`.

**(C) `p≡3 mod 4` vs the reachable set — a class mismatch to keep on separate ledgers.**
Of the already-computed/near primes, only **p=43** satisfies the stated precondition `p≡3 mod 4`
(with `n=31` prime, `n≡1 mod 6`). **p=13 (n=7)** and **p=61 (n=61)** are `p≡1 mod 4`. If the cap
mechanism differs by `p mod 4` (the χ₂ twist and eigenvalue structure can), pooling `{13,61}` with
`{43}` is a null-mismatch. Pre-commit: **two separate ledgers**, `p≡3 mod 4` and `p≡1 mod 4`; no
pooled number crosses them.

---

## 1. OBJECT

The two free Frobenius-eigenvalue invariants of the twisted weight-1 sheaf at each μ₆-cell:
`(e₁, e₂) ∈ (Z[ζ_n])²`, equivalently the reparametrisation `(σ, π) = (sinθ₁+sinθ₂, sinθ₁·sinθ₂)`
via `e₁=2i√p·σ`, `e₂+2p=−4p·π`. The cap is the object `σ = s₁+s₂`; `|V|/√p = 2|σ|`, cap `⟺ |σ|≤1`.
The **mechanism** is the law relating the two weight-1 pieces `β₁=2i√p s₁`, `β₂=2i√p s₂` (the two
quadratic factors `t²−β_jt−p`). This is NOT a proxy: the pieces are the actual 2-dim summands of
`H¹_c`; `s₁,s₂` are two real DoF and the cap lives in their sum. **Tautology check:** `s₁,s₂` are
the two roots of one quadratic (share `e₁,e₂`), so within one cell they are coupled by
construction; across DIFFERENT primes they are independently constructed. The matched control
(§3) breaks the pairing only across primes — no shared-construction tautology.

**Why the statistic is a 2-vector, not a scalar.** The object has 2 real DoF `(θ₁,θ₂)`. Collapsing
to the scalar `σ²` (the cap magnitude) would destroy the mechanism — exactly the "bound becomes a
verdict" failure. The mechanisms differ in a *relation between two coordinates*; a scalar cannot
carry that.

## 2. STATISTIC (one exact observable per cell; four pre-committed decidable functionals)

**Observable** `T(c) = (e₁(c)², e₂(c)) ∈ (Z[ζ_n]∩ℝ)²` — exact (integer histogram → cyclotomic
transform in `CyclotomicField(n)`, no `CC`). Derived exact reals: `σ²(c) = −e₁²/(4p)`,
`π(c) = −(e₂+2p)/(4p)`. Four functionals, each with a distribution/decision under its null:

- **F1 (M1 — Frobenius-swap / field of definition).** `D_β(c) = e₁² − 4(e₂+2p) ∈ Z[ζ_n]`
  (`= −4p(s₁−s₂)²`). Decide: **is `D_β` a square in `Z[ζ_n]`?** (⟺ `β₁,β₂ ∈ Q(ζ_n)` individually ⟺
  the quadratic `s²−e₁s+(e₂+2p)` splits over `Q(ζ_n)`). Exact; no power/floor issue; decidable at
  a single cell.
  - `D_β` a square at all cells → `β_j` each over `Q(ζ_n)`, **NO Frobenius swap → M1 REFUTED**
    (and confirms the standing fact `β_j∈Z[ζ_n]` at new p).
  - `D_β` non-square at some cell → `β_j` in a quadratic extension, swapped by its Galois → **M1
    SUPPORTED at that (p,cell)**, and this CONTRADICTS the standing fact `β_j∈Z[ζ_n]` (verified only
    at p=13,43) → re-open that fact, report the specific cell.

- **F2 (M2 — dual/conjugate pieces).** Exact: `σ²−4π` (`=0 ⟺ s₁=s₂ ⟺ D_β=0`) and `σ²` (`=0 ⟺ V≡0`).
  - any cell with `σ²>0` → **M2b (`β₂=β̄₁`, `V≡0`) REFUTED** (consistent with `S→2`).
  - any cell with `σ²≠4π` → **M2a (`β₂=−β̄₁`, `s₁=s₂`, cap trivially `≤2`) REFUTED**.
  (These are the "rule them out on the data, not by hand" checks. Both decidable at one cell.)

- **F3 (M3 vs M4 — locus dimension).** Pooled cloud `{(σ²(c),π(c))}` over the reachable primes
  (one Galois orbit per prime). Frozen model: least-squares **degree-3** fit `π = poly₃(σ²)`;
  statistic `R` = RMS vertical residual (in `(σ²,π)` units, `σ²∈[0,4]`, `π∈[−1,1]`). Null = the
  matched independent-piece control (§3) at the SAME orbit count. **Report `R` and the locus, not a
  yes/no** (per "report the locus"). Decision threshold: `R_real < ` [5th percentile of control `R`]
  → "on a curve" (M3); else area-filling (M4a).

- **Cap functional (for the surprise calibration, §5).** `1[σ²(c) ≤ 1]` (exact, `⟺ |e₁|²≤4p`).

## 3. MATCHED CONTROL — "piece-shuffle" (breaks only the cross-piece coupling)

Pool all single-piece values `{s_j}` (2 per cell) across cells, using their EXACT empirical
marginal (support and symmetry as observed — see §0(C): determine sign support `[−1,1]` vs `[0,1]`
from data first). Form synthetic 4-tuples by drawing two pieces INDEPENDENTLY from the pool; run
each through the SAME pipeline `pieces → (e₁,e₂) → factor → (β₁,β₂) → (σ²,π)` used on real data.
- **Preserves:** each weight-1 piece's exact marginal, `|α|=√p`, the `α↦−ᾱ` pairing WITHIN a piece,
  the μ₆/Galois cell structure per prime.
- **Destroys:** the cross-piece coupling `θ₁–θ₂` — precisely the object M1/M3 assert and M4 denies.
- **Not a tautology-shuffle:** the pieces recombined come from DIFFERENT primes (independent
  construction), so the shuffle does not break real signal the way it breaks an artifact (contrast
  the `r=v−w` residue tautology). Feature (`s₁`) and target (`s₂`) are disjoint-construction across
  the shuffle boundary.
- **Matched-null integrity gate:** if the empirical single-piece marginal is signed (`s_j∈[−1,1]`),
  a control forcing `s_j≥0` (θ∈[0,π]) is a NULL-MISMATCH (destroys a sign symmetry the readout has)
  — do NOT use it as the matched null. Determine the sign support first (§9 step 0).

## 4. PLANTED / FIRING CONTROL — independent-θ ensemble (known cap-violation rate)

Draw `θ₁,θ₂` iid, form the paired weight-1 4-tuple `√p{e^{iθ₁},e^{i(π−θ₁)},e^{iθ₂},e^{i(π−θ₂)}}`,
feed through the SAME `newton_to_charpoly → factor → (σ²,π)` path. Computed cap-violation rates
(derivation: `P = 1 − (4/π²)∫₀^{π/2} arcsin(1−sinφ)dφ`, `J=0.64368`; cross-checked by 2-D quadrature
and 2×10⁷ Monte-Carlo):

| ensemble | support of `s=sinθ` | cap event | **P(violate cap)** |
|---|---|---|---|
| A — `θ~U[0,π]` (task's) | `s∈[0,1]` | `s₁+s₂>1` | **0.7391** |
| B — `θ~U[0,2π)` (signed, matched shape) | `s∈[−1,1]` (arcsine) | `|s₁+s₂|>1` | **0.3691** |

**Firing requirement (must both hold or the null is uninformative):**
(i) the pipeline REPORTS `σ²>1` on these synthetic 4-tuples at rate `0.74`/`0.37` (± MC error) —
confirms it can SEE cap violations; (ii) the F3 locus statistic separates a *planted 1-D* M3 cloud
from this independent-θ (M4-by-construction) cloud — calibrated in §5.

## 5. POWER (computed now, per §0(B) with the PRIME as the independent unit)

**F1, F2:** exact and decidable at a single cell — no effect-size/power number applies; one cell
either exhibits the algebraic signature or not.

**Cap-surprise (F-cap vs matched control §3):** independent unit = prime (one algebraic
cap-inequality per prime, holding in all `(n−1)/6` embeddings). Let `q` = matched-control
per-prime cap-violation rate (to be MEASURED via the shuffle, §3; theoretical references `q≈0.37`
(B) / `0.74` (A)). p-value if all `N_prime` valid primes satisfy the cap `= (1−q)^{N_prime}`:

| `N_prime` | valid `p≡3 mod4` set (cells) | `(1−0.37)^N` | `(1−0.74)^N` |
|---|---|---|---|
| 1 | {43}(5) | 0.63 | 0.26 |
| 6 | {43,67,79,127,163,211}(5,13,11,21,23,33) | 0.063 | 3.1e-4 |
| 16 | up to p≈700 | 6.3e-4 | 4.6e-10 |
| 30 | up to p≈1500 | 1.0e-6 | — |

**Verdict: with the current instrument's valid-class reach (p=43 only), `N_prime=1`, p-value 0.26–0.63
— UNPOWERED.** To reach p<1e-3 needs `N_prime≥6` (primes to 211, `O(p²)` mechanism cost) under the
optimistic `q=0.74`, or `N_prime≥16` (primes to ≈700) under the conservative measured `q≈0.37`.

**F3 locus (M3 vs M4a):** frozen model deg-3, threshold = 5th-pct of matched-control `R` at matched
orbit count. Calibration (cap-conditioned control B; models the many-primes-pooled i.i.d. regime):

| pooled orbits `N` | M4 control `R` median | M4 5th-pct (= "on-curve" threshold) | detect exact-(deg≤3) M3 |
|---|---|---|---|
| 5 | 0.078 | 0.0049 | power 1.00 |
| 16 | 0.214 | 0.143 | power 1.00 |
| 50 | 0.234 | 0.197 | power 1.00 |
| 106 | 0.238 | 0.215 | power 1.00 |

- **False-discrimination (a true-M4 orbit-cloud mislabelled M3) = 5% by construction** (the threshold
  IS the 5th percentile). This is the F3 gate's own false-failure rate, stated per the standing rule.
- Power=1.00 holds ONLY for an M3 locus that is *exactly* degree-≤3 in `(σ²,π)`. For a general M3
  locus, detectable iff its deg-3 residual `< threshold(N)`; at `N=5` the threshold is `0.005`
  (only a near-exact locus is caught), at `N=16` it is `0.143` (loose). Un-knowable pre-data, so F3
  is reported as `R_real` + the fitted locus, not a bare verdict.
- **Caveat:** with few primes the per-prime points are Galois conjugates (not i.i.d.); the table's
  i.i.d. model is valid only in the many-primes-pooled regime → F3 needs many primes, reinforcing §6.

## 6. SCOPE

**Forced structure (verified 2026-07-24 for `y²=x³+7`, `p≡3 mod4`, `n` prime, `n≡1 mod6`):**
valid primes = {43, 67, 79, 127, 163, 211, …}; cells `(n−1)/6` = {5, 13, 11, 21, 23, 33, …}.
`p≡1 mod4` companions with `n` prime, `n≡1 mod6` (SEPARATE ledger): {13(1), 61(10), 97(13), 229(43),
241(43), …}.

**Two tiers (the scope decision — neither task-option (a) nor (b), because the `O(p⁴)` wall binds
only the theorem-redundant purity re-check, §0(A)):**

- **Tier-P — purity/instrument self-test, `O(p⁴)` (`V₃,V₄`).** Confirms `e₃=−p·e₁`, `e₄=p²`,
  `|α_i|=√p` (all theorems) → gates instrument correctness only. Current instrument reaches {13,43}.
  The rewrite (below) adds {61,67,79} (`p⁴ ≤ 3.9e7`). If any Tier-P prime FAILS purity → the
  `(e₁,e₂)→(θ₁,θ₂)` interpretation is invalid → STOP.
- **Tier-M — mechanism, `O(p²)` (`V₁,V₂`).** Extract `(e₁,e₂)` at ALL valid primes (both ledgers)
  up to a `p_max` chosen so `N_prime≥16` in the `p≡3 mod4` ledger (p_max≈700; extend to ≈1500 for
  `N_prime≈30`). All of F1/F2/F3 and the cap-surprise run here, CONDITIONAL on Tier-P purity.
  `O(p²)`: `p=1500 → 2.25e6` field ops per `V₂` histogram — feasible.

**Every number the run emits inherits: (its tier, its `p mod 4` ledger, `N_prime`, `q` if a
cap-surprise number). No cross-ledger or cross-tier pooling.**

**Instrument rewrite (required to reach Tier-M `p≳300` and Tier-P `p∈{61,67,79}`; the current
`histogram()` iterates `E(F_{p^k})` via Sage `EllipticCurve` point objects + a per-point Frobenius-
conjugate trace loop, ~10× slower than naïve `O(p^k)`):**
Rewrite `histogram(p,k,...)` (lines ~56–89) with raw `F_{p^k}` coordinate arithmetic, PRESERVING its
exact integer accumulation `h_k[d] = Σ_{Tr(P)=[d]G} χ₂(y_P)`:
1. Represent `F_{p^k}` by a fixed precomputed irreducible polynomial; elements as `numpy` int arrays
   (coefficient vectors over `F_p`). No `EllipticCurve` / field-element objects.
2. Enumerate points by vectorising over all `x∈F_{p^k}`: `rhs = x³+7`; square-test
   `rhs^((p^k−1)/2)==1` (vectorised field power); recover the two `y`.
3. `χ₂(y) = y^((p^k−1)/2) ∈ {+1,−1}` — vectorised.
4. `Tr_{k/1}(P) = P + Frob(P) + … + Frob^{k−1}(P)`; `Frob(x,y)=(x^p,y^p)` = coordinatewise p-power =
   a precomputed `F_p`-linear map on the coefficient vectors (matrix, applied once per power); the
   `k−1` elliptic additions are vectorised across all points (array group law).
5. Index the trace via the existing `dl` dlog table (`curve_data`, line 40) and accumulate
   `h_k[d] += χ₂(y_P)` by `numpy.bincount` — **exact integers**.
6. **Exactness upgrade for the signal path:** replace the `CC` transform `V_k(a)=Σ_d h_k[d]·ζ_n^{ad}`
   (current lines 144–146 use complex doubles) with `CyclotomicField(n)` so `V₁,V₂,e₁,e₂,e₁²,e₂` and
   the F1/F2 tests are EXACT in `Z[ζ_n]`. `CC` eigenvalues/angles remain for display only (carve-out).

## 7. FALSIFICATION (written before the run)

- **Cap itself:** any reachable cell with `σ²>1` (`|e₁|²>4p`) → the `[VERIFIED]` bound has a
  counterexample → report `(p, cell)`, re-open the bound and everything downstream. (This is the
  falsification trigger for the object, not for a mechanism.)
- **M1:** `D_β` non-square in `Z[ζ_n]` at any cell → the standing fact `β_j∈Z[ζ_n]` is false there
  (M1 supported).
- **M2a/M2b:** already falsified the moment one cell shows `σ²≠4π` / `σ²>0` (expected, given `S→2`).
- **M3:** `R_real` NOT below the matched-control threshold at the powered orbit count → M3 (1-D
  locus) unsupported at reachable p; the pairs are area-filling (M4a).
- **Whole-hypothesis abandon:** purity fails at a Tier-P prime → abandon the `(e₁,e₂)→θ` frame
  entirely (the eigenvalues are not weight-1 pure, the cap is a different phenomenon).

## 8. EXACTNESS

Signal path is int / `Z[ζ_n]` end-to-end: integer histograms `h_k[d]`; `V₁,V₂,e₁,e₂` via
`CyclotomicField(n)`; the cap decision `|e₁|²≤4p`, `D_β` square-test (F1), and `σ²−4π`, `σ²`
(F2) are exact comparisons/square-tests in `Z[ζ_n]`. **Float carve-outs (analytic size only, no
key/verdict in the path):** (i) `√p` used to DISPLAY `σ, s_j` (the cap uses `|e₁|²` vs `4p`,
integer); (ii) the F3 deg-3 least-squares residual `R` and its control percentiles (F3 is declared
non-discriminating below the powered orbit count, so no verdict rests on it there); (iii) the
independent-θ / shuffle controls' Monte-Carlo. The `CC` eigenvalue-modulus and angle prints are
display-only.

## 9. PRE-COMMITMENT (outcome → conclusion + grade, fixed now)

**Step 0 (matched-null integrity):** measure the single-piece sign support (§3 gate). If signed,
use control B-shaped matched null; if all `s_j≥0`, control A-shaped. Record which; it sets `q`.

| Outcome | Conclusion | Grade |
|---|---|---|
| Purity holds at all Tier-P primes | instrument/`(e₁,e₂)→θ` frame valid; proceed | forced check — **no mechanism credit** |
| Purity fails at a Tier-P prime | STOP; frame invalid | falsification of frame |
| `D_β` square at all cells | no Frobenius-swap; each piece over `Q(ζ_n)` | **M1 REFUTED** (numerical signature; points proof AWAY from Weil-restriction, TOWARD a base-field relation M3 or coincidence M4) |
| `D_β` non-square at some cell | swap present; standing fact wrong there | **M1 SUPPORTED at (p,cell)** (numerical); re-open `β_j∈Z[ζ_n]` |
| `σ²>0` and `σ²≠4π` somewhere (expected) | dual/conjugate laws excluded | **M2a, M2b REFUTED** (numerical) |
| all valid-class primes satisfy cap AND `(1−q)^{N_prime}<1e-3` | cap is structure, not independent-θ coincidence | **cap [VERIFIED]; matched control fired**; supports {M1,M2,M3} over M4-facet-b |
| all satisfy cap BUT `(1−q)^{N_prime}≥0.05` (e.g. current `N_prime=1`, valid class) | reachable `N_prime` too small to reject coincidence | **ABSTAIN — underpowered** (a finding, per abstention-is-the-finding); need `N_prime≥16` → p_max≈700, Tier-M `O(p²)` rewrite |
| `R_real <` control 5th-pct at powered orbit count | pairs lie on a 1-D locus; report the fitted locus | **M3 SUPPORTED / M4a REFUTED** (numerical signature; false-disc 5%); the locus is the proof target |
| `R_real ≥` threshold at powered orbit count | pairs area-fill the capped region | **M4a SUPPORTED / M3 REFUTED** (numerical); cap has no lower-dim law at reachable p |
| powered orbit count NOT reached (few primes) | M3/M4 not separable | **ABSTAIN on M3 vs M4a** — need pooled `N_prime≳16` primes (p_max≈700), Tier-M rewrite |
| any reachable cell `σ²>1` | cap counterexample | **cap [FALSIFIED at that p]** — re-open the `[VERIFIED]` bound |

**Grade ceiling (fixed):** the cap can only remain `[VERIFIED]` or become `[FALSIFIED]` from this
run — never `[PROVED]`. Any mechanism can only reach `[SUPPORTED]`/`[REFUTED]` **as a numerical
signature that points a proof**; none of these outcomes is itself a proof.

---

## Forced quantities (instrument gates — ZERO discrimination credit)

Per the anomaly-drill rule "count only UNFORCED hits": the following are true by construction/theorem
and must be VERIFIED as instrument-correctness gates but carry NO evidential weight for any Mi.
- μ₆ collapse: `n−1` a-values → exactly `(n−1)/6` cells (needs `n≡1 mod6`, verified §6).
- Factorisation `P(t)=(t²−β₁t−p)(t²−β₂t−p)` with each constant term `−p` (`β₁β₂=e₂+2p`, `β₁+β₂=e₁`).
- `e₃=−p·e₁`, `e₄=p²`; `|α_i|=√p` (Tier-P). A deviation ⇒ histogram bug, not a discovery.
- μ₆-invariance of `V(a)` within a cell (`V(a)=V(ζ₆·a)`). A deviation ⇒ cell definition bug.

## One-line scope-honest summary
With the CURRENT instrument the `p≡3 mod4` valid class reaches only **p=43 (N_prime=1)** → F1/F2 are
fully decidable there, but the cap-surprise and F3 are **UNPOWERED / non-discriminating**. Powering
them needs the `O(p²)` Tier-M rewrite to `p_max≈700` (`N_prime≈16`); the `O(p⁴)` `V₄` barrier is
NOT the binding constraint (it gates only a theorem-redundant purity re-check).
