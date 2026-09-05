# PRE-REGISTRATION — Does the PUBLIC μ3-orbit index j (+ known range) leak the SECRET d mod 3?

**Status: PRE-REGISTERED. Written before any run. No data seen.** Different object from the eps/carry
family (`PREREG_eps_to_d_constraint_v1/v2.md`); reuses that family's fixed OOS curves, exactness rule,
plant discipline, and matched-control philosophy.

Object: `E: y^2=x^3+7`, prime-order subgroup ⟨G⟩ of order `m=n`, GLV endomorphism φ=[λ], λ²+λ+1≡0 (mod m).
`j = χ3`-index of `x([d]G)` (PUBLIC, from the point, no d in path; `chi3_index`/tool 1). Target `d mod 3`.
Congruence (OPEN_d2, verified 30/30 on F43): `d ≡ d0·(−1)^j − ⌊d0 λ^j/n⌋ (mod 3)`, i.e.
`d = d0 λ^j − n⌊d0 λ^j/n⌋` read mod 3. d0 = orbit-min of d under ⟨±λ⟩.

Two parts: **(a)** deterministic structural-degeneracy characterization (crossover bit-length `b*(m)`);
**(b)** a pre-registered leakage statistic for `j → d mod 3`, with the φ-forced coupling quotiented.

---

## PART (a) — STRUCTURAL DEGENERACY (deterministic, NO statistic)

**Object.** For d in a bit-range `[2^{b−1}, 2^b)` with `2^b ≪ m`: is the congruence's decomposition
degenerate, i.e. `d0 = d`, carry `⌊d0 λ^j/n⌋ = 0`, `j=0`, `s=0` — so `d mod 3 = d`, a tautology giving
NO constraint? Characterize `b*(m)` = the crossover where the carry first becomes nonzero (an orbit
sibling `±λ^k d mod m` first drops below d).

**Computation (decidable, exact, per curve).** For every `d ∈ [1,m)`: form the ⟨±λ⟩-orbit
`{±λ^k d mod m : k=0,1,2}` as integers in `[1,m)`; `d0 = min`. Record `[d0==d]` and the carry. Bin by
`⌊log2 d⌋`. `b*(m)` = largest bit b for which ALL d in the bin satisfy `d0=d` (carry 0); first-break =
smallest b with any carry. Int-only. **Frozen result (computed pre-registration, exact enumeration):**

| p | m | ⌊log2 m⌋ | b* (all-degenerate ≤) | first carry bit | fully non-degenerate by |
|---|---|---|---|---|---|
| 547 | 547 | 9 | 3 | 4 | 9 |
| 907 | 967 | 9 | 4 | 5 | 10 |
| 1303 | 1249 | 10 | 4 | 5 | 10 |
| 1669 | 1663 | 10 | 4 | 5 | 10 |
| 2089 | 2143 | 11 | 5 | 6 | 11 |

**Characterization:** `b*(m) ≈ ⌊log2 m⌋ − 6`, with a ~6-bit crossover band up to `⌊log2 m⌋` (the
orbit-min of ~6 near-uniform siblings survives while `d ≲ m/7`). **Scoped structural consequence for
secp256k1** (`m≈2^256`, so `b*≈250`): every feasible BTC-puzzle key (`≤ ~70` bits) sits deep in the
degenerate regime → `d0=d`, carry 0, `j=0`, `s=0` → the congruence returns `d mod 3 = d`, a tautology
with ZERO constraint. This is the deterministic explanation of ARSENAL's "82 keys all give c=0,j=0,s=0"
and it is a PROVED-by-enumeration structural fact on the scoped curves (not a statistic).

**(a) Falsification:** if, below the tabulated `b*`, any enumerated d has `d0≠d` or carry `≠0`, the
degeneracy claim for that curve is false — report the counterexample d.

**(a) Pre-commitment:** report the `b*(m)` table (above) and confirm the below-`b*` regime is uniformly
degenerate on all five curves; state the secp corollary as conditional on the `b*≈⌊log2 m⌋−6` scaling
(EMPIRICAL-scaling, VERIFIED-instance on the five curves, not proved for all m).

---

## PART (b) — LEAKAGE (pre-registered statistic)

### THE FORCED-COUPLING FLAG (resolve before anything counts as a leak)

Under φ: `j → j+1 (mod 3)` and `d → λd`, so `d mod 3 → (λ mod 3)·d mod 3`. **λ mod 3 is
curve-dependent** (computed: 547→1, 907→1, 1303→**0**, 1669→**0**, 2089→**2**) — it is NOT the `−1` of
the F43 example. Within one ⟨±λ⟩-orbit the pair `(j, d mod3)` is therefore FORCED to a deterministic
per-curve pattern `(j0+t, (λ mod3)^t · r)` (mod carry). Any test that includes multiple members of the
same orbit will read this forced pattern as association. **It must be quotiented before it counts as a
leak.** Non-circularity otherwise holds: j is a public point-readout, d mod3 the secret, disjointly
computed (j never uses d mod 3) — this is a legitimate public-feature vs secret-target test, not the
residue-vs-component tautology.

### 1. PRIMARY STATISTIC (quotiented — one representative per orbit)

`G = 2 Σ_cells O ln(O/E)` on the **3×3 contingency** of `(j = χ3-index of [d0]G, d0 mod 3)` computed
over **one representative per ⟨±λ⟩-orbit** (the orbit-min `d0`), enumerated over the fixed range
(default: the full group `[1,m)`, so orbit-reps ≈ `m/6` after ±λ dedup). One representative per orbit
removes ALL within-orbit forced coupling regardless of λ mod 3. Readout: exact permutation p-value
`p = (#{G_control ≥ G_real}+1)/(B+1)`, `B ≥ 5000`. base rate for `d mod 3` = 1/3 (report the exact
marginal). G is float ranked against an integer-count permutation null (no float threshold decides).

**Stratification by log2(d0):** also report G within the below-`b*` (degenerate) stratum and the
crossover/above-`b*` stratum separately — a leak, if any, is predicted by part (a) to live only where
the carry is active. Each stratum inherits its own U and base rate.

### 2. MATCHED CONTROL

Two controls, both required to agree:
- **(C1) Orbit-quotient permutation (primary null):** uniform permutation of the target `d0 mod 3`
  labels across the orbit-representatives, within the log2(d0) stratum (preserves the marginal and the
  range/size structure). Because each orbit contributes once, no within-orbit forced coupling exists to
  manufacture signal; a genuine cross-orbit `j→d mod3` association survives, a forced coincidence
  cannot. This is the control a true leak survives but a symmetry-forced coincidence does not.
- **(C2) Forced-null on the RAW (non-quotiented) range (corroborating):** regenerate synthetic
  `d mod 3` for every key by re-drawing each orbit's anchor residue uniformly and propagating it through
  the ACTUAL per-curve forced map `(λ mod 3)^t` (+ the real carry), then recompute G on the raw range.
  This preserves the exact φ-forced coupling and destroys only unforced association. If `G_raw ≈
  G_forced-null` the raw signal is entirely forced — the leak has COLLAPSED to the φ-relation (the
  flagged case) and does not count.

The verdict is the primary C1 test; C2 demonstrates the raw association is not a forced artifact.

### 3. PLANTED CONTROLS (must fire before any verdict)

- **Positive:** set `j := d0 mod 3` (feature ≡ target) ⇒ `G_real ≫ C1`, `z ≥ 6`. If it does not fire,
  null uninformative — STOP, fix pipeline.
- **Negative:** `j :=` a μ3-orbit-respecting random index independent of d0 ⇒ `G_real ≈ C1`, `z≈0`.
- **Forced-plant (gate for C2):** set `d mod3 :=` pure per-curve forced map of a random anchor with real
  j ⇒ `G_raw ≈ C2` (confirms C2 correctly reads "no unforced leak" and is not manufacturing one).

### 4. POWER (per curve; U = orbit-reps, base rate 1/3)

3×3 table, df=4. Non-centrality `λ_nc = U · V² · 2` (V = Cramér's V); detect at power .8 when
`λ_nc ≳ 12`, i.e. detectable `V ≳ sqrt(6/U)`. U ≈ (m−1)/6 on the full group:

| p | m | U ≈ (m−1)/6 | detectable V (power .8) | detectable per-cell excess over 1/3 |
|---|---|---|---|---|
| 547 | 547 | 91 | 0.26 | ~0.13 |
| 907 | 967 | 161 | 0.19 | ~0.10 |
| 1303 | 1249 | 208 | 0.17 | ~0.09 |
| 1669 | 1663 | 277 | 0.15 | ~0.08 |
| 2089 | 2143 | 357 | 0.13 | ~0.07 |

Stratified sub-tests have smaller U (report each; below-`b*` stratum on small curves may have U too
small for z≥6 — state it, do not read a low-power null as absence). **Real-82 arm is ZERO-power:** all
82 give `j=0` (part a) ⇒ no feature variance ⇒ statistic undefined; consistency spot-check only. The
powered real-analog is the constructed known-generator set with keys spanning ≥ `b*` bits (j varies).

### 5. SCOPE — fixed OOS protocol (reused, no seed-shopping)

- **SCAN:** p=547 (U=91), p=907 (U=161). Development + first pass here only.
- **CONFIRM (frozen):** p=1303 (U=208), p=1669 (U=277), p=2089 (U=357). A scan hit must survive C1 on
  ALL THREE under a fresh confirmatory prereg. Range fixed as full group `[1,m)` (+ the two log2(d0)
  strata); per-curve λ mod 3 fixed as computed above. Every number inherits `(p, m, U, range, stratum)`.

### 6. EXACTNESS

Signal path int-only: orbit/`d0`/carry/`j`/`d mod3` all exact integer mod arithmetic; χ3-index via exact
modular power. No float in the signal path. G and z are float statistics ranked against integer-count
permutation nulls only. `check_no_float.sh` must pass on the run script before it executes.

### 7. FALSIFICATION (part b)

- **Leakage null** iff `G_real` is inside the C1 distribution (`p_perm > 0.05`) on the scan curves at
  U-power giving detectable V ≤ tabulated (min U=91 ⇒ V_detect 0.26). Then `j` does not predict
  `d mod 3` beyond 1/3 on scope. A null is SCOPED (curves, U, range, per-curve λ mod 3), conditional
  phrasing, never "j is independent of d mod 3" in general. Part (a)'s degeneracy already predicts the
  below-`b*` stratum is a tautology, not a leak.
- **Collapse-to-forced** iff C1 null AND `G_raw ≫ C1-shuffle` but `G_raw ≈ C2`: the raw association is
  entirely the φ-forced coupling — explicitly report "collapsed to forced φ-relation, quotiented, no
  leak," not a leak.

### 8. PRE-COMMITMENT (filled BEFORE the run)

| Outcome | Conclusion (pre-committed) |
|---|---|
| Positive plant does NOT fire | Null uninformative. STOP. Fix pipeline. No verdict. |
| `G_real ≫ C1` (z≥6) on orbit-reps, scan | EXPLORATORY leak candidate. Freeze the exact (curve, range, stratum). Fresh confirmatory prereg on {1303,1669,2089}, C1 again. Survives all three → graded EMPIRICAL/VERIFIED-scope; then quantify bits: `log2 3 − H(d mod3 | j)`. Fails any → discarded as scan chance hit. Never a verdict from the scan. |
| `G_real ≈ C1` (p>0.05) on scan, plant fired | SCOPED LEAKAGE NULL: "χ3-index j does not predict d mod 3 beyond 1/3 on curves {547,907}, U-power V_detect≤0.26, plant fired." Conditional phrasing. |
| C1 null but `G_raw ≫ shuffle`, `G_raw ≈ C2` | COLLAPSE-TO-FORCED: raw association is the per-curve φ-relation (λ mod 3), quotiented away → no leak. Report the forced structure, not a leak. |
| Leak concentrates in below-`b*` stratum | Suspect tautology (part a: d0=d there ⇒ d mod3=d); verify j there is not a disguised copy of d mod 3 before any claim. |
| Any statistic/range/stratum/curve changed after scan | Deviation. Disclose; changed result is EXPLORATORY, never the pre-registered verdict. |

**Nothing about the likely outcome is asserted. Part (a) is a deterministic enumeration with a frozen
`b*` table; part (b) quotients the per-curve φ-forced coupling (C1) and cross-checks that the raw signal
is not that forced artifact (C2). The run fills the numbers.**
