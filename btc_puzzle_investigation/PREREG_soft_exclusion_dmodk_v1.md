# PRE-REGISTRATION — SOFT exclusion: do public point-invariants under/over-represent d mod k?

**Status: PRE-REGISTERED. Written before any run. No data seen.** Same machinery as
`PREREG_eps_to_d_constraint_v2.md` (omnibus G on a collapsed joint feature vs target, μ6-orbit matched
control, Holm, plants, fixed OOS, exact int + G float carve-out). Two changes: TARGET = `d mod k`
(secret residue), FEATURES = the public point-invariant vector. **Fence premise (binding):** the
target's hardness is ASSUMED, not proven; no route is a wall; the only admissible conclusions are a
scoped POSITIVE (bits removed, bound to method+power+curves) or a SCOPED NULL bound to
method+power+curves — NEVER "impossible/secure".

Follows the HARD-exclusion scoped null (`RESULT_exclusion_hard_empty_cells_v1.md`: no empty cells at
populated granularity). Occupancy is uneven ⇒ the live question is SOFT (statistical under/over-
representation), a distribution test, not a support test.

Object: `E: y²=x³+7`, prime-order ⟨G⟩ of order `n=m`, GLV φ=[λ], λ²+λ+1≡0 (mod n). `P=[d]G`, coords
`(x_d,y_d)`. This is a legitimate public-feature → secret-residue LEAKAGE test: features are public
functions of `(x,y)` (disjoint construction, no d in path); `d mod k` is the secret.

---

## 1. OBJECT — features (verified public/d-free) and targets

Public invariant vector `V(P)`, evaluated at one representative per μ6-orbit (§2):

| feature | values | φ-action | d-free? |
|---|---|---|---|
| χ3-index | {0,1,2} | φ: →+1 (covariant) | yes (x-only) |
| eps | {0,1,2} | φ-INVARIANT | yes (x-only) |
| s-band | {0,1,2,3} | φ-INVARIANT (norm-preserving) | yes (x-only) |
| sextant | {0..5} | φ: →+2 (covariant) | yes (x-only) |
| χ2(y)=Legendre(y,p) | {±1} | φ-INVARIANT (φ fixes y) | d-free BUT parity-suspect |

**Targets:** `r = d mod k`, `k ∈ {2,3,4,6,7}`. Reported per k; Holm over the k-family.

**χ2(y) PARITY-SUSPECT flag (carried from v2, made precise here):** all scope curves have `p≡3 mod 4`
⇒ `χ2(−1)=−1` ⇒ χ2(y) is ODD in d (`χ2(y_{n−d})=−χ2(y_d)`). Since `−1 ∈ μ6`, χ2(y) is coupled to the
`d ↔ n−d` sign, hence to `d mod k` for EVEN k (k∈{2,4,6}) by the ±-symmetry. This coupling is FORCED,
not a leak. The μ6-orbit quotient (§2, with a sign-canonical rep) plus the matched control (§3) must
absorb it; any χ2(y)-driven signal on even k is tagged PARITY-SUSPECT and is not a leak unless it
survives the ±-preserving control.

## 2. STATISTIC — μ6-orbit quotient, omnibus G (exactly one primary)

**Quotient FIRST (removes GLV redundancy AND the forced within-orbit coupling).** The forced coupling
is curve-dependent (computed): under φ, `d mod k → (λ^t·d mod n) mod k` — NOT a clean `×(λ mod k)`
except in the carry-free low range (the mod-n wraparound is the carry). Per-curve `λ`:

| p | n | λ | λ%2 | λ%3 | λ%4 | λ%6 | λ%7 |
|---|---|---|---|---|---|---|---|
| 547 | 547 | 40 | 0 | 1 | 0 | 4 | 5 |
| 907 | 967 | 142 | 0 | 1 | 2 | 4 | 2 |
| 1303 | 1249 | 1155 | 1 | 0 | 3 | 3 | 0 |
| 1831 | 1753 | 1570 | 0 | 1 | 2 | 4 | 2 |
| 2143 | 2089 | 826 | 0 | 1 | 2 | 4 | 0 |

Because the forced map is not clean-multiplicative over the full group, the quotient is done by the
EXACT scalar orbit, not by an assumed rule: enumerate ⟨±λ⟩-orbits `{±λ^t d mod n}`, take the orbit-min
`d0` (sign-canonical: `d0 < n/2` where the pair permits) as the representative. `V_rep = V([d0]G)`,
`r = d0 mod k`. One rep per orbit ⇒ no within-orbit forced coupling enters the statistic.

**PRIMARY statistic:** omnibus `G = 2 Σ_cells O ln(O/E)` between the collapsed joint feature
`J = (χ3, eps, χ2y)` (3·3·2 = 18 cells) and target `r = d mod k`, on the orbit-reps. **One permutation
p-value per k** (`p_k = (#{G_ctrl ≥ G_real}+1)/(B+1)`, B≥5000); **Holm over k∈{2,3,4,6,7}** (family = 5).
G is a float transform ranked against an integer-count permutation null (no float threshold decides).

**SECONDARY (declared map list, Holm over frozen count 25):** each single feature
{χ3, eps, s-band, sextant→{0,1,2} by mod 3, χ2y} × each k∈{2,3,4,6,7} = 25 tests; individual G vs the
same control. Includes the **raw hint to test, NOT a claim:** the reported `χ3=2` row skew (32/37 or
/43 on one curve) is the (feature=χ3, target=d mod k) cell — its verdict comes from the frozen
χ3-map + omnibus, never from that cell alone.

## 3. MATCHED CONTROL (μ6-orbit; absorbs the forced coupling)

Permute the target `r = d0 mod k` labels across the orbit-representatives (preserves the exact `d mod k`
marginal and the `V_rep` marginal; destroys only the cross-orbit feature↔residue association). Because
reps are one-per-μ6-orbit, the within-orbit φ-forced coupling (χ3↔residue, sextant↔residue, and the
χ2y↔even-k parity) is already quotiented — a forced coincidence cannot appear; a genuine unforced
leak survives (`G_real ≫ G_ctrl`).

**Adequacy check via the full-set repairing null (used by the forced-coupling plant, §4):** on the
NON-quotiented point set, re-pair each orbit's ordered V-vector with a random orbit's ordered
target-vector (both computed exactly from the scalar orbit). This preserves each orbit's internal
forced pattern and both marginals, destroying only cross-orbit association; a pure-forced-coupling
input yields `G_real ≈ G_ctrl` here, confirming the design does not read forced coupling as a leak.

## 4. PLANTS (must resolve before any verdict)

- **Positive (planted residue leak):** bias the target so that reps with a chosen `V_rep` value
  over-represent one residue beyond the marginal (a genuine unforced leak of known size). PRIMARY must
  detect it (`G_real ≫ ctrl`, survives Holm), `z ≥ 6`. If it does not fire, null uninformative — STOP.
- **Forced-coupling plant (must be ABSORBED, not read as leak):** feed data whose ONLY structure is
  the exact per-curve φ-forced coupling with random orbit-anchor residues and NO unforced leak. The
  PRIMARY (quotiented) must report NULL (`G_real ≈ ctrl`). If it fires, the quotient failed to absorb
  the forced coupling — STOP, fix the quotient. (Demonstrate the un-quotiented naive test DOES falsely
  fire here, to show the quotient is load-bearing.)
- **Negative:** a μ6-respecting random feature independent of the target ⇒ `G ≈ ctrl`, no Holm survivor.

## 5. POWER — per curve (U = orbit-reps ≈ (n−1)/6) and per k

Omnibus df = (18−1)(k−1) after empty-cell drop = 17(k−1). Non-centrality `λ_nc = U·V²·(min−1)`; detect
at power .8 when `λ_nc ≳ df + 2√(2df)`; detectable Cramér's V ≈ `sqrt((df+2√(2df))/(U·(min−1)))`.

| p | n | U≈(n−1)/6 | df(k=3) | V_detect k=3 | df(k=7) | V_detect k=7 |
|---|---|---|---|---|---|---|
| 547 | 547 | 91 | 34 | 0.51 | 102 | 0.79 |
| 907 | 967 | 161 | 34 | 0.38 | 102 | 0.59 |
| 1303 | 1249 | 208 | 34 | 0.34 | 102 | 0.52 |
| 1831 | 1753 | 292 | 34 | 0.28 | 102 | 0.44 |
| 2143 | 2089 | 348 | 34 | 0.26 | 102 | 0.40 |

The smallest curves at large k are UNDER-POWERED (V_detect > 0.5) — state this per cell; never read an
under-powered null as an exclusion-of-absence. The secondary single-feature maps (fewer df) are better
powered; report both. **Real-82 arm is ZERO-power** (all 82 are orbit-min with `j=0`, degenerate per
`PREREG_j_range_to_dmod3_v1.md` part a) ⇒ no feature variance; consistency spot-check only. Powered
real-analog = constructed known-generator set with keys spanning ≥ `b*` bits.

## 6. EXCLUSION READOUT (bits removed, control-calibrated)

Per k: `bits_removed_net = H_ctrl(d mod k | V) − H_real(d mod k | V)` (base-2), where `H_real` is the
empirical conditional entropy on the orbit-reps and `H_ctrl` is the matched-control mean (this de-biases
the always-downward finite-sample conditioning bias). Report `bits_removed_net` with the control
distribution (mean ± sd) and the permutation p; also report the raw `H(d mod k) − H(d mod k | V)` and
the base `H(d mod k)` (≈ log2 k, not exactly, since d mod k counts differ by ≤1). A soft exclusion =
`bits_removed_net` exceeding the control distribution at the Holm-corrected level.

## 7. SCOPE (frozen OOS; p≡7 mod 12 = secp class, for the c₂ grading)

- **SCAN:** p=547 (n=547), p=907 (n=967). Development + first pass only.
- **CONFIRM (frozen):** p=1303 (n=1249), p=1831 (n=1753), p=2143 (n=2089). A scan hit must survive its
  primary (per-k omnibus, Holm) on ALL THREE under a fresh confirmatory prereg. No feature/collapse/
  target/curve/k changes after the scan. Every number inherits `(p, n, U, k, feature-collapse)`.

## 8. EXACTNESS

Integer signal path: χ3-index (exact modular power), eps/s-band/sextant (integer lift arithmetic),
χ2(y) (exact Legendre), `d mod k`, orbit enumeration — all exact int. No float in the signal path.
G, entropy, z are float statistics ranked ONLY against integer-count permutation nulls; no float
threshold decides a verdict. `check_no_float.sh` must pass on the run script before it executes.

## 9. PRE-COMMITMENT (filled BEFORE the run)

| outcome | conclusion |
|---|---|
| Positive plant does NOT fire | null uninformative. STOP. Fix pipeline. |
| Forced-coupling plant FIRES on the quotiented primary | quotient failed to absorb forced coupling. STOP, fix quotient. No verdict. |
| Some k: `G_real ≫ ctrl` (Holm-significant), survives OOS all 3 | SOFT EXCLUSION on scope: report `bits_removed_net` per k with (p,n,U). Characterize which feature/residue subclass carries it (χ3? sextant? — and rule out PARITY-SUSPECT χ2y on even k via the ±-preserving control). EXPLORATORY until confirm; grade EMPIRICAL/VERIFIED-scope after OOS. A POSITIVE (bits removed), scoped — never "d mod k is secure". |
| All k: `G_real ≈ ctrl` (Holm-null), plants clean, adequate power (V_detect ≤ ~0.3) | SCOPED NULL: "public invariant vector J does not under/over-represent d mod k beyond the μ6 matched control on curves {547,907,1303,1831,2143}, U-power V_detect≤{value}, plants fired." Conditional phrasing; bits_removed_net reported with its CI (consistent with 0). NEVER "impossible/secure". |
| χ3=2 hint significant only via χ2y on even k, dies under ±-preserving control | PARITY artifact, not a leak — report as absorbed forced coupling. |
| Under-powered cell (V_detect > 0.5, e.g. small curve × k=7) | state UNDER-POWERED; no null-of-absence read from it. |
| any statistic/collapse/target/curve/k changed post-scan | deviation — disclose; changed result is EXPLORATORY, never the pre-registered verdict. |

**PARALLEL FENCE-LINE (registered OPEN, not tested here, not closed):** is any public invariant of
`[d]G` computable from `d` in less than one scalar-multiplication? GLV φ proves ≥1 orbit-covariant is
cheap FROM P; the question FROM d is open. Noted; not a claim; not closed.

**Nothing about the likely outcome is asserted. The forced μ6-coupling is quotiented (§2) and its
absorption is a firing plant (§4); the omnibus + Holm bound the k-family multiplicity; bits-removed is
control-calibrated (§6). The run fills the numbers.**
