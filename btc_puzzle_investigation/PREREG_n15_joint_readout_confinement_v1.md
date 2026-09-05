# PREREG — N15 Joint Multi-Readout Confinement Test (`n15_joint_readout_confinement_v1`)

**Status: FROZEN pre-registration. No data seen. Written before any run.**
Grade of any result this spec can produce: **EMPIRICAL**, scoped to the constructed
known-d secp-pipeline keys of §6 (power arm) + the ~82 real solved puzzle keys (OOS
arm). Nothing here can license a claim at, or a closure of, the 2²⁵⁶ ECDLP.

This spec pre-registers ONE experiment with a designated PRIMARY statistic (§2a),
pre-registered SECONDARY arms (§2b, §2c) under a single family-wise multiplicity
control (§2e), and a well-posedness adjudication that is done **before** the run
(§1) rather than inferred after it.

---

## 0. SCOPE BANNER

**What this measures.** Whether the JOINT public readout tuple
`T(d) = ( e([d]G), s-class([d]G), y-parity([d]G) )`, conditioned on the known
bit-length interval `I = [2^(b-1), 2^b)`, is predictable from **bounded-complexity
(cheap) arithmetic functions of `d`** beyond what its individual readouts are
separately — i.e. a candidate operational keyspace-confinement mechanism on
known-d secp-pipeline keys.

**What this does NOT measure / does NOT license.**
- It is a **stated-power measurement**. A within-null result is a **bounded
  magnitude** carrying its power + scope + untested-channel list, **never**
  "avenue dead / generic / no structure" (dismissal vocabulary is banned here per
  the project closure-grade rule).
- A positive is graded **EMPIRICAL**, pending a second independent
  experiment-designer read (§10) and out-of-sample retest; it is **not** a proof
  and **not** a 2²⁵⁶ statement.
- The raw confinement `H(T|I)` has an **alphabet ceiling of `log₂18 ≈ 4.17` bits**
  (§1, FACT 1) — a constant, independent of `b`. A confinement bounded by this
  ceiling is **not** a sub-brute-force keyspace reduction; it is at most a
  constant-factor filter of the same class as the already-baseline μ₆ automorphism
  speedup (~1.29 bits). The keyspace question lives entirely in the **cheap
  predictability** arm (§1, §2a), not in the raw confinement.

---

## 1. OBJECT

### 1a. STEP 1 — locked definitions (from source; ambiguities named and resolved)

The point is `P = [d]G` on secp256k1 `E: y² = x³ + 7 / F_p`, `p` the secp field
prime, `p ≡ 1 (mod 3)` (j=0 / μ₆ CM curve). `n = #E(F_p)` its order, `x = x(P)`,
`y = y(P)`, both public.

- **`e([d]G)` — the cubic readout (3-valued).** `e ∈ {0,1,2}` defined by
  `x^((p-1)/3) ≡ β^e (mod p)`, `β` a fixed primitive cube root of unity mod `p`.
  Locked from `PREREG_cm_lattice_unfolding_v1.md` §1 ("cubic exponent `e ∈ {0,1,2}`
  (`x^((p−1)/3) ≡ β^e`)"). Firing precedent (`AUDIT_session_conclusions_v1.md` #4):
  `MI(e; d) = 1.585 bits = log₂3` — `e` is uniform on 3 values and fully determined
  by `d` (it is a deterministic function of the public point).

- **`s-class([d]G)` — the lift-norm / carry class (3-valued).** **NAMING-COLLISION
  AMBIGUITY, resolved as a spec decision.** The symbol `s` is overloaded in the
  corpus: `PREREG_cm_lattice_unfolding_v1.md` uses `s = [y > p/2]` for the y-SIGN
  (its `e=0 ∧ s=0` transversal means `e=0 ∧ y<p/2`). The N15 brief instead defines
  "s-class" as the **lift-norm / carry class of the point**, a DIFFERENT object
  (`ANALYSIS_public_gate_glv_carry_circularity_v1.md`: "Eisenstein lift-norm
  inradius"; `NOTE_carry_readout_leak_nulls_v1.md`: the validated carry
  `c(X)=(ω·z(X)−z(βX))/π_p` with the `{¾,⅛,⅛}` Cap-Law).
  **Resolution (frozen):** `s-class := c(X) ∈ {0,1,2}`, the exact-integer Eisenstein
  carry class of `x(P)` produced by the validated tool (`β = ω mod π_p`; exact
  integer Babai reduction of `x` against the gauss-reduced ℤ-basis of the ideal
  `(π_p)`, `N(π_p)=p`; the `{¾,⅛,⅛}` distribution). This is the "lift-norm / carry
  class"; the flap indicator `eps ∈ {0,1,2}` and the norm-bucket of
  `Fraction(enorm,p) ∈ [0,3/4]` induce the same 3-partition and are recorded as
  equivalent presentations. **`s-class` is NOT `cm_lattice`'s `s`.**

- **`y-parity([d]G)` — the sign bit (2-valued).** `y-parity := [ y ≥ p/2 ] ∈ {0,1}`,
  i.e. the compressed-pubkey sign (`y-parity=0 ⇔ y < p/2`). This IS
  `cm_lattice`'s `s`. Computed by the integer comparison `2y ≥ p` (exact; §8).

- **Interval `I`.** `I = [2^(b-1), 2^b)`, the known bit-length band; `b` = the
  `bits`/`N` column of the datasets (§6). Conditioning is per-band.

- **Joint readout.** `T(d) = (e, s-class, y-parity) ∈ {0,1,2}×{0,1,2}×{0,1}`,
  a `3·3·2 = 18`-cell alphabet, conditioned on `I`.

### 1b. Well-posedness adjudication (done before the run; two structural facts, not outcome predictions)

The N15 brief's literal object — "joint confinement / synergy beyond the sum of
marginals," with the §2-suggested statistic `I(d;T|I)` vs `Σ_X I(d;X|I)` — is
**degenerate for the keyspace question**, by two algebraic facts about the object's
alphabet and construction (stated here, before any data, so they cannot be
back-fitted):

- **FACT 1 (alphabet ceiling).** `T` ranges over ≤ 18 cells, so
  `I(d;T|I) = H(T|I) ≤ log₂18 ≈ 4.17 bits`, independent of `b`. A fixed-alphabet
  tuple removes at most a constant number of bits — never a sub-brute-force
  (b-growing) cell. This is a property of the readout's codomain, not a prediction
  of the run.
- **FACT 2 (deterministic sub-additivity).** `e`, `s-class`, `y-parity` are each
  deterministic functions of the point, hence of `d`; so `I(d;X|I)=H(X|I)` and
  `I(d;T|I)=H(T|I)`. Therefore
  `I(d;T|I) − Σ_X I(d;X|I) = H(T|I) − Σ_X H(X|I) = −TC(e,s-class,y-parity | I) ≤ 0`,
  where `TC` is the total correlation (≥ 0 by sub-additivity). The "synergy beyond
  the sum of marginals," read as joint-info-about-`d` minus the marginal sum, is
  `≤ 0` **by an information identity**, not a testable positive.

**Consequence.** The literally-stated statistic measures `−TC ≤ 0`; its only
non-degenerate content is (i) the redundancy `TC(e,s-class,y-parity | I) ≥ 0`
among the three readouts and (ii) the absolute confinement `H(T|I) ≤ log₂18`.
Neither is a keyspace reduction: the ceiling is constant, and exploiting it
requires computing `T(d')` for each candidate `d'`, which costs a full scalar
multiplication `[d']G` = the same as directly checking `[d']G == P` (the `#4`
finding: `T` is not a cheap arithmetic function of `d`).

**What makes it well-posed as a keyspace test (the registered reframing).**
Replace "`T` about `d`" with "`T` about **bounded-complexity (cheap) functions of
`d`**." Let `C(d)` be a frozen vector of cheap arithmetic functions of `d` (§2d).
`T` is **not** a deterministic function of `C(d)` (`C` is O(poly(b)); `T` needs the
scalar mult), so `I(C(d); T | I)` is a genuine, non-degenerate quantity that can be
small or large. A positive is operationally a **keyspace filter** (compute cheap
`C(d')` for candidates, keep only those whose predicted `T` matches the observed
`T(P)`, do the expensive scalar mult only on survivors). This is the PRIMARY object.
The raw `H(T|I)` and `TC` are registered as SECONDARY structural diagnostics,
explicitly **non-keyspace** (§2c).

### 1c. Independence from the DLP (well-posedness Q1, load-bearing)

- **Reading `T(P)` is O(1)** (public point); it is **not** an enumeration. The
  `STRUCTURAL_IMPLICATIONS_2026-07-30_v1.md` "d-carrying ⇒ DLP-locked by
  definition" argument is about the twisted sum `V(a)`, whose **evaluation** is an
  `O(n)` enumeration over the group. It does **not** apply to reading `T`, which is
  a single O(1) readout of one public point. What is DLP-hard is **inverting**
  `T → d`; the registered statistic never inverts.
- On **known-d** sets, `d` is available, so `C(d)` (cheap) and `T([d]G)` (one
  scalar mult per key, already tabulated in the datasets) are **both computable
  without solving any DLP**. Therefore `I(C(d); T | I)`, and the confinement
  `H(d|T,I)`, are **measurable on known-d sets independent of solving any DLP.**
- **Operational reading of "keyspace reduction" (pinned):**
  - A positive on the raw confinement diagnostic (§2c) does **NOT** constitute a
    keyspace reduction: constant ceiling (FACT 1), and exploiting it costs a
    scalar mult per candidate (no cheap filter).
  - A positive on the PRIMARY cheap-predictability arm (§2a) **DOES** constitute a
    keyspace reduction, because it yields a cheap pre-filter that reduces the
    number of scalar mults below brute force. This is the arm the verdict hinges
    on, and the object worthy of the DLP-independence distinction.

### 1d. Marginal expectation

Each individual readout `e`, `s-class`, `y-parity` is a per-point public function of
a bijective image of `d`; its marginal `I(C(d); X | I)` is expected Farey-generic
(the `#4` precedent: `max I(e; 8 cheap fns) = 0.033 bits` at an `n≈349` floor). The
object under test is the **JOINT** cheap predictability and whether adding
`s-class` and `y-parity` to `e` raises it beyond the per-marginal floor.

---

## 2. STATISTIC

### 2a. PRIMARY statistic (exactly one, named now)

`S := Î( C(d) ; T | I=band b )` — the Miller–Madow-corrected plug-in **mutual
information in bits** between the frozen cheap-predictor vector `C(d)` (§2d) and the
frozen joint readout `T = (e, s-class, y-parity)`, computed **within a single
bit-length band `b`** and reported per band; the primary verdict band is the
**power-designated band** of §6 (the largest band whose `MI_min ≤ 10⁻³ bits`,
§5).

**Distribution under the null.** Under the matched null (§3: permute the `C ↔ T`
pairing among the `N` keys **within band `b`**), `C` and `T` are independent with
the observed within-band marginals; `Î` is the plug-in MI of two independent
categoricals whose positive bias depends only on the marginals and `N`. The bias is
**absorbed by ranking against the permutation null** (the null shares the exact
marginals). Reported p-value is exact:
`p_perm = (1 + #{ Ŝ_b ≥ S_obs }) / (1 + B)`, `B = 9999`, integer counts only.
The `log` inside `Î` is a monotone transform used only via its rank against the
matched null (float carve-out, §8).

Chosen as a POOLED, low-df **targeted** statistic (one MI on a fixed alphabet aimed
at the joint cheap-predictability object §1b names as the LIVE keyspace hypothesis),
**not** a max-over-cells.

### 2b. "Beyond the individual readouts" — synergy decomposition (registered SECONDARY, chain-rule terms)

The literal N15 question ("beyond what the individual readouts do separately") is
answered by the incremental (conditional-MI) chain-rule decomposition, each term
with its own exact within-stratum null (the `cm_lattice` ARM-N construction):

- `S_e   = Î(C ; e | I)`                          — marginal cheap leakage of `e`.
- `S_s|e = Î(C ; s-class | e, I)`                 — cheap info `s-class` adds beyond `e`.
- `S_y|es= Î(C ; y-parity | e, s-class, I)`       — cheap info `y-parity` adds beyond `(e,s-class)`.
  Chain rule: `S_e + S_s|e + S_y|es = Î(C;T|I) = S`.

Nulls: `S_s|e` permutes `s-class` **within `(C,e)` strata**; `S_y|es` permutes
`y-parity` **within `(C,e,s-class)` strata** — each preserves the lower-order
dependence exactly and destroys only the incremental coupling (the matched null for
a conditional-MI statistic). `B = 9999`. **"Beyond individual readouts" fires iff
`S_s|e` or `S_y|es` is positive beyond its null** (i.e. a later readout adds
cheap-predictable info the earlier ones did not carry).

### 2c. Structural diagnostics (registered SECONDARY, explicitly NON-keyspace)

- `H_conf = H(d | T, I) = H(d|I) − H(T|I)` per band — the raw confinement (FACT 1
  ceiling `H(T|I) ≤ log₂18`). Reported with its ceiling; a diagnostic of the
  redundancy structure, **not** a keyspace claim.
- `TC = Σ_X H(X|I) − H(e,s-class,y-parity | I) ≥ 0` per band — the total
  correlation (mutual redundancy of the three readouts within `I`). Matched null:
  permute `e`, `s-class`, `y-parity` **independently** within band `b` (destroys
  cross-readout coupling, preserves each marginal). A positive `TC` characterizes
  the readouts as mutually redundant; it says the joint cell is *larger* than the
  independence prediction and is explicitly **not** a synergy about `d`.

### 2d. Frozen cheap-predictor vector `C(d)` (bounded-complexity, anti-tautology-critical)

`C(d)` is restricted to genuinely CHEAP (O(poly(b)), no scalar-mult) functions of
`d`, extending the `#4` set:
`C(d) = ( d mod 3, d mod 6, d mod 7, d mod 9, d mod 12,
          jacobi(d, n), cube-res(d, n), hi₃(d,b), lo₃(d) )`
where `jacobi(d,n)` = integer Jacobi symbol, `cube-res(d,n) = d^((n-1)/3) mod n`
mapped to `{0,1,2}` (n prime), `hi₃(d,b)` = the top 3 bits of `d` within band `b`
(the interval-position feature), `lo₃(d)` = the bottom 3 bits. **`C` must never
include `d` itself, all bits of `d`, or `[d]G`/`x`/`y`** (that would be
tautological — see §2R). The list is FROZEN here; no post-hoc addition.

### 2e. Multiplicity control

One permutation loop recomputes ALL registered statistics per shuffle: primary `S`
(§2a) + 3 chain-rule terms (§2b) + `TC` (§2c), across the reported bands.
Family-wise p-value = permutation rank of the **maximum** standardized statistic
across the registered family (min-p / max-T), exact integer counts,
**family-wise α = 0.001**. The primary `S` additionally carries its own single-test
`p_perm` reported un-corrected for transparency; the LEAK verdict requires the
family-wise-corrected threshold.

---

## 2R. ANTI-TAUTOLOGY (well-posedness Q2, resolved)

- **Feature = `C(d)`** (bounded-complexity functions of `d`). **Target = `T`**
  (readout of the POINT `[d]G`). **Shared intermediate = `d` only.** The map
  `d → T` goes through the scalar multiplication (the DLP-hard direction); `C` is a
  direct cheap function of `d`. `T` is **not** built from `C`, and `C` is **not**
  built from `T`; there is no sub-construction of one inside the other. The only
  bridge is `d → [d]G → T`. A positive `I(C;T|I)` therefore means a
  bounded-complexity function of `d` predicts a readout that otherwise requires the
  scalar mult — a genuine leak, not a tautology.
- **NOT the `r = v − w` residue-vs-component artifact.** `T` is not a residual of
  `C` (nor vice versa); nothing here subtracts a component from the whole. The
  shuffle null (§3) breaks the tested coupling *and* would break a genuine leak
  identically, so — unlike the `r=v−w` case where the shuffle hides the artifact —
  here the shuffle is a valid matched null (it destroys exactly the DLP-bridge
  coupling under test, nothing forced).
- **NOT a linear-relation check.** `Î` is a categorical MI, not a linear
  correlation, and no algebraic identity is imposed between `C` and `T`.
- **Interval conditioning introduces no tautological path.** Conditioning on band
  `b` and including `hi₃(d,b)`/`lo₃(d)` as cheap predictors is legitimate: these are
  O(1) bit reads of `d`, and `T([d]G)` is not a trivial function of a few bits of
  `d` (it needs the scalar mult). The runtime construction audit (§8) asserts that
  `x`, `y`, and `[d]G` never enter the `C` code path and that `d`'s full value never
  enters the `T` code path.

---

## 3. MATCHED CONTROL

**Primary null (arm §2a).** Within band `b`, shuffle the `C(d) ↔ T` pairing among
the `N` keys.
- **Preserves:** the within-band marginal of `C` (each cheap-function distribution),
  the within-band marginal of `T` (the joint `18`-cell readout distribution incl.
  its `{¾,⅛,⅛}`/cubic/parity structure), and the band conditioning.
- **Destroys:** only the `C ↔ T` correspondence — the DLP-bridge coupling under
  test. A marginal-only effect (e.g. a skewed `T` distribution within the band)
  cannot masquerade as coupling, because it is held fixed on both sides.

**Conditional nulls (arm §2b).** As stated in §2b — within-stratum permutation of
the incremental readout, preserving all lower-order dependence exactly.

**Diagnostic null (arm §2c, `TC`).** Independent within-band permutation of `e`,
`s-class`, `y-parity` — destroys cross-readout coupling, preserves each marginal.

**Why no μ₆-transversal here (contrast with `cm_lattice`).** `cm_lattice` measured a
μ₆-covariant feature against a μ₆-covariant target, so it needed the transversal to
avoid a forced-lockstep artifact. Here the target `T` is a per-point readout and the
feature `C` is a function of `d`; the μ₆ orbit action moves *both* `C` (via
`d → ±λ^j d`) and `T` (via `e→e+1, s-class→·, y-parity→1−·`), but the within-band
`C↔T` shuffle preserves each marginal and destroys only their coupling, so no forced
lockstep is manufactured. **Registered null-validity witness:** additionally report
`S` on the μ₆-orbit-collapsed set (one representative per orbit); the two must agree
within the permutation band, else the null is flagged mis-specified and the run is
inadmissible (redo).

Every "k/k" tally reports **distinct-key** counts (no orbit double-counting).

---

## 4. PLANTED / FIRING CONTROL

**Positive plant (must fire — power calibration).** Augment `C` with a synthetic
cheap symbol `c*(d)` that equals a chosen coordinate of `T` (say `e`) with
probability `ε` (drawn from a fixed seed keyed to the key index) and is uniform on
`{0,1,2}` otherwise. Sweep `ε ∈ {0, 1/64, 1/32, 1/16, 1/8, 1/4, 1/2, 1}`. The
pipeline MUST recover the injected dependence; report `ε_min` = smallest `ε` with
family-wise `p_perm < 0.001` at the run's `N`. A second plant injects a **joint**
dependence (`c*` matches `(e,s-class)` jointly) to exercise the chain-rule terms.
**Non-degeneracy guard:** the plant must fire monotonically across the `ε` ladder
(higher `ε` ⇒ lower `p_perm`); a non-monotone plant response flags a broken
estimator.
**VOID rule:** **if `ε = 1` (full plant) does NOT fire, the statistic/pipeline is
broken, every arm is VOID, and NO null is banked — full stop.** `c*` is drawn from
`T` (a target quantity) ONLY inside the plant harness, never in the real `C` path.

**Hard null (must NOT fire — calibration).** `C` of key `i` paired to `T` of a
random key `j` (same band). Over 100 independent re-pairings, empirical family-wise
false-positive rate at α = 0.001 must be `≤ 2α`; if it exceeds `2α`, the permutation
null is miscalibrated and the run is VOID.

---

## 5. POWER

Detection is a permutation MI test with `df = (|C-alphabet| − 1)(|T-alphabet| − 1)`.
Plug-in MI floor `≈ df / (2 N ln2)`; detectable MI at family-wise α=0.001,
power 0.8: `MI_min(bits) ≈ λ_nc(df, α, power) / (2 N ln2)`.

**Anchoring to the prior (`#4`).** `max I(e; 8 cheap fns) = 0.033 bits` at `n≈349`
— consistent with a floor `≈ df/(2·349·ln2)` for `df≈22` (`d mod 12` × `e`),
confirming the prior was **finite-size-floor-limited**, not a measured absence.
Because keys are **constructed on demand** (§6), `N` is chosen per band to drive the
floor down:
- `N = 10⁶` ⇒ floor `≈ df/(2·10⁶·ln2)`; for the joint (`|C|` up to a few thousand
  across the frozen vector reduced to its realized support, `|T|=18`) the primary is
  run on the **realized-support** contingency table, keeping `df` moderate; target
  `MI_min ≤ 10⁻³ bits` (≈ 30× below the `0.033` prior floor).
- `N = 10⁷–10⁸` (constructed) ⇒ `MI_min ≈ 10⁻⁴–10⁻⁵ bits`.

**Weil/character-sum floor.** For the multiplicative-character components of `C`
(`jacobi`, `cube-res`), the correlation with a per-point CM readout of `[d]G` is a
character sum over the curve, bounded by Weil at `O(p^{-1/2})` amplitude ⇒ an MI
floor `~ 1/n` bits, negligible (`~2^{-256}` at secp scale) relative to the finite-N
sampling floor. `MI_min = max(sampling floor, Weil floor) =` sampling floor for all
realistic `N`. **What counts as sub-brute-force vs at-the-floor:** an at-the-floor
result is `|S| < MI_min` (bounded null). A sub-brute-force result requires the cheap
joint predictability to yield a filter whose passed fraction of `I` is bounded away
from 1 by an amount that **grows with `b`** — reported as the induced filter
selectivity, not merely as an MI magnitude. A constant-selectivity positive is a
constant-factor filter (reported as such), not sub-brute-force.

**Under-power rule.** Any band with `MI_min > 10⁻² bits` at its run `N` is recorded
"insufficient power," not as a bound.

---

## 6. SCOPE / PARAMETERS

**Arm 1 — constructed known-d keys (POWER-BEARING).** Generated on demand via the
secp construction pipeline (`build_fullrange_dataset_v1.py`: `scalar_mul` + exact
`derive`), **not** capped at the existing 100k/36k CSVs. Per band, construct as many
known-d keys as needed to reach `MI_min ≤ 10⁻³ bits` (§5). Columns consumed:
`d` (decimal, exact), `X`, `Y` (hex → `int(·,16)`, exact parse), `N`/`bits` (band),
`sextant` (available). `e`, `s-class`, `y-parity` recomputed exactly from `x`, `y`
(§8). **Bands:** `b ∈ {32, 48, 64, 96, 128, 160, 192, 256}` (sampled), plus:
- **Arm 1b — full enumeration (EXACT, higher-power sub-arm).** For low bands
  `b ∈ {8, 12, 16, 20, 24}`, enumerate the **entire** keyspace of the band
  (`2^(b-1)` keys), giving the exact joint distribution of `(C, T)` and the exact
  confinement `H(d|T,I)` — no sampling floor for the confinement, and the primary
  `S` computed on the exact within-band table.

**Arm 2 — real solved puzzle keys (OOS, fixed, low-power).**
`btc_puzzle_master_exact.csv` (~82 SOLVED rows: `priv_dec` = `d`, `X_hex`, `Y_hex`,
`bits`). Kept for the project "test on both sets" rule and as the OOS check on any
constructed-arm positive — **not** a power arm (`N≈82`, `MI_min` large; per-band
`N` is single digits). Any real-arm null is explicitly power-limited.

**Power vs secp full 256-bit keys (stated honestly).**
- The PRIMARY cheap-predictability arm (§2a) **has real power at 256 bits**: we
  construct millions of known-d 256-bit keys and compute `C(d)` (cheap) and
  `T([d]G)` (one scalar mult each). So the keyspace-relevant statistic reaches the
  actual secp band.
- The CONFINEMENT-ENUMERATION sub-arm (Arm 1b) does **not** reach 256 bits (cannot
  enumerate `2^255`); it is exact only for `b ≤ 24`. The confinement diagnostic at
  256 bits is therefore sampled, not exact, and is subject to FACT 1's constant
  ceiling regardless.

**Selection rule (no cherry-picking).** Fixed band list above; fixed seed `= 7`
(matching `build_fullrange_dataset_v1.py`); `B = 9999` permutations; frozen `C`
vector (§2d). Every reported number carries its `arm`, `b`, `N`, and statistic name.

**In-bounds.** `d` drawn uniformly within each band (no generator bias); any
`C→T` structure is a property of the curve's CM/GLV arithmetic (number-theoretic
key structure, in-bounds). The PRNG/generation mechanism is not studied.

---

## 7. FALSIFICATION (pre-committed decision table; no dismissal vocabulary in any null branch)

Preconditions for ANY verdict (else inadmissible → redo): `ε=1` plant fires
monotonically; hard-null FP `≤ 2α`; μ₆ null-validity witness agrees; band `MI_min
≤ 10⁻² bits`.

- **RETAINED (joint cheap-leakage).** Family-wise `p_perm < 0.001` on the primary
  `S` (§2a) on the constructed power arm AND corroborated OOS on the real-82 arm
  (or, if the real arm is power-starved, the constructed positive replicates across
  ≥2 independent constructed seeds). Grade **EMPIRICAL**. Un-gates the operational
  cheap pre-filter; report the induced filter selectivity vs `b` (§5) and which
  chain-rule term(s) (§2b) carry it. NOT a proof, NOT a 2²⁵⁶ statement.
- **SCOPED NULL (bounded magnitude).** Family-wise `p_perm ≥ 0.001` across all
  powered bands, with ALL controls fired. Conclusion: the joint cheap
  predictability of `T` is bounded, `|S| < MI_min`, **with power (`MI_min`, `N`) +
  scope (arms, bands) + untested-channel list** (other cheap-predictor families,
  other readouts / larger alphabets, the confinement-enumeration reaching only
  `b ≤ 24`, the DLP-inversion direction). A bounded magnitude — **not** "avenue
  dead / generic / no structure."
- **VOID.** `ε=1` plant did not fire (instrument dead) ⇒ no null banked; fix
  pipeline, no verdict. Likewise hard-null FP `> 2α` (null miscalibrated) or μ₆
  witness disagreement (null mis-specified) ⇒ inadmissible, redo.
- **CONSTRUCTED FIRES, REAL DOES NOT.** Report as a scope-limited positive on the
  constructed arm; the real-82 non-replication is flagged **power-limited**
  (`N≈82`, per-band single-digit) — this is not evidence of absence. Grade
  **EMPIRICAL (constructed-only)**; owed: a larger real OOS if/when more keys solve.
- **REAL FIRES, CONSTRUCTED DOES NOT.** Anomalous (the real set passes through the
  same secp pipeline). Treat as a pipeline/instrument discrepancy to investigate
  (construction path, band matching, `C`/`T` recompute), **not** as a verdict.
- **Diagnostics (§2c).** `H_conf`/`TC` results are reported with the FACT-1 ceiling
  attached and are **never** read as a keyspace verdict in any branch.

---

## 8. EXACTNESS (no-float compliance)

**Signal path is int/Fraction only.**
- `e` = `pow(x, (p-1)//3, p)` mapped to `{0,1,2}` (integer modpow; `//` on the
  public exponent is exact-integer, not a ratio in the data path).
- `s-class` = the exact-integer Eisenstein carry class via
  `eisenstein_lift_sextant_exact_v1` / the validated carry tool (all `int`; Babai
  reduction via integer `rdiv`/`gauss_reduce`; norm as `int`, any ratio as
  `Fraction`).
- `y-parity` = `1 if 2*y >= p else 0` (integer cross-product; no `/`).
- `C(d)`: `d % m` (integer), `jacobi(d,n)` (integer symbol), `cube-res` =
  `pow(d, (n-1)//3, n)` mapped to `{0,1,2}`, `hi₃`/`lo₃` via bit shifts.
- `X`, `Y` parsed by `int(·,16)` (exact); `d` by `int(·)` (exact). No
  `float()`, `/`, `**0.5`, `round(ratio)`, `math.*`/`np.*` on any key-, point-,
  feature-, or target-derived value.

**Construction audit (runtime assertions, frozen):**
1. `x`, `y`, `X`, `Y`, `[d]G` are never referenced inside the `C` code path
   (source scan of the feature functions at import).
2. The full value of `d` is never referenced inside the `T` code path (only the
   public point coordinates are).
3. `C` contains no element functionally equal to `d`, all bits of `d`, or a point
   coordinate (frozen-list assertion).

**Float carve-out (named, justified).** The ONLY float is `math.log` inside the MI
estimator `Î`, tagged `# noqa: float`. It is a monotone transform used ONLY via its
rank against the matched permutation null (§2a–c); the null shares the exact
marginals, so plug-in bias cancels in the rank. No key/point/feature/target value
passes through a float; no float threshold is applied to data.

**Gate:** `bash check_no_float.sh <runner + any new signal-path file>` must exit 0
before any statistic is computed.

---

## 9. PRE-COMMITMENT — outcome table (filled BEFORE the run)

| Arm / statistic | Outcome (trigger) | Pre-committed conclusion | Grade |
|---|---|---|---|
| **Primary `S` (§2a)** | FW `p_perm < 0.001`, constructed, replicated (seed/OOS), all controls fired | **Joint cheap-leakage RETAINED** at scope: `C(d)` predicts `T([d]G)` beyond marginals ⇒ candidate operational keyspace filter; report selectivity vs `b` + carrying chain-rule term. | **EMPIRICAL** |
| **Primary `S`** | FW `p_perm ≥ 0.001` across all powered bands, all controls fired | **SCOPED NULL:** joint cheap predictability bounded `|S| < MI_min` with power + scope + untested-channel list. Bounded magnitude, NOT a closure. | scoped null (EMPIRICAL bound) |
| **Chain-rule `S_s|e`, `S_y|es` (§2b)** | positive beyond within-stratum null | later readouts add cheap-predictable info beyond `e` ⇒ "beyond individual readouts" component fires; report which. | EMPIRICAL |
| **Chain-rule** | within null | adding `s-class`/`y-parity` gives `< MI_min` cheap info beyond `e` at scope. | scoped null |
| **Confinement/TC (§2c)** | any value | structural characterization of readout redundancy (`H(T|I)` vs `log₂18`; `TC`); explicitly **NOT** a keyspace verdict. | diagnostic |
| **Real-82 arm (§6)** | agrees with constructed | OOS corroboration (if powered) / power-limited note (if not). | as parent arm |
| **any arm** | `ε=1` plant did NOT fire | **VOID** — instrument dead, no null banked. | VOID |
| **any arm** | hard-null FP `> 2α` OR μ₆ witness disagrees | **INADMISSIBLE** — null miscalibrated/mis-specified; redo. | — |
| **constructed fires / real does not** | as §7 | scope-limited positive; real non-replication flagged power-limited (not absence). | EMPIRICAL (constructed-only) |
| **real fires / constructed does not** | as §7 | pipeline/instrument discrepancy to investigate; not a verdict. | — |

---

## 10. OWED GATES

- **Second independent experiment-designer read is OWED** before any positive
  (RETAINED / chain-rule fire) promotes past EMPIRICAL — this spec's frame layers
  (object/disjointness §1–2R, matched-control adequacy §3, scope §6, falsification
  §7, pre-commitment §9) require context-isolated review; a self-audit discharges
  only the mechanical layers.
- **`compile-diff` is OWED** if any result here is folded into a
  `POSITIVE_FINDINGS_MASTER_*` / consolidated / handover document.
- **`check_no_float.sh` (§8)** must exit 0 on the runner before the run; record it
  as a mechanical gate satisfied, with the artifact.

---

### Frozen feature / target / null registry (for the audit)

- `e = [x^((p-1)/3) ≡ β^e] ∈ {0,1,2}`; `x = x([d]G)`. Public, exact int.
- `s-class = c(X) ∈ {0,1,2}` (Eisenstein carry, `{¾,⅛,⅛}` law, ideal `(π_p)`,
  `N=p`). Public, exact int. (NOT `cm_lattice`'s `s`.)
- `y-parity = [2y ≥ p] ∈ {0,1}`; `y = y([d]G)`. Public, exact int. (= `cm_lattice`'s `s`.)
- `T = (e, s-class, y-parity)`, 18-cell; `I = [2^(b-1),2^b)`.
- `C(d) = (d mod 3,6,7,9,12; jacobi(d,n); cube-res(d,n); hi₃(d,b); lo₃(d))`,
  bounded-complexity, frozen, excludes `d`/its full bits/point coords.
- Primary: `S = Î(C;T | band b)` bits; matched null = within-band `C↔T` shuffle;
  `B=9999`; FW α=0.001.
- Chain-rule: `Î(C;e|I)`, `Î(C;s-class|e,I)`, `Î(C;y-parity|e,s-class,I)`;
  within-stratum nulls.
- Diagnostics: `H(d|T,I)` (ceiling `log₂18`), `TC` (independent within-band perm null).
- Plants: positive `ε`-sweep (fire at `ε=1`, monotone) + joint plant; hard null
  (FP `≤ 2α`); μ₆ null-validity witness.
- Exactness: int/Fraction; float carve-out = `math.log` in `Î` (`# noqa: float`);
  `check_no_float.sh` exit 0.
- Arms: constructed on-demand (power, `MI_min ≤ 10⁻³`; full-enum `b ≤ 24`);
  real-82 (OOS, low power). Bands `b ∈ {8..24 enum, 32..256 sampled}`. Seed 7.

---

**Provenance.** Pre-registered via the `experiment-designer` gate (context-isolated;
raw material + criteria only, no session narrative, no expected answer), 2026-08-25.
Definitions locked from `AUDIT_session_conclusions_v1.md` #4,
`PREREG_cm_lattice_unfolding_v1.md`, `NOTE_carry_readout_leak_nulls_v1.md`,
`ANALYSIS_public_gate_glv_carry_circularity_v1.md`; DLP-independence checked against
`STRUCTURAL_IMPLICATIONS_2026-07-30_v1.md`; construction pipeline
`build_fullrange_dataset_v1.py`. FACT 1 / FACT 2 (§1b) independently re-derived in
the main session before persistence. This is SPEC ONLY — no runner has executed.
