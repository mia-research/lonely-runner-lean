# PRE-REGISTRATION v2 — FROZEN FAMILY: do public x-covariants supply the d-side carry (and cut d2)?

**Status: PRE-REGISTERED. Written before any run. No data seen.** Supersedes the single-map v1
(`PREREG_eps_to_d_constraint_v1.md`) with a multiplicity-controlled test over the WHOLE declared map
family. Same object, same disjoint-construction rule, same no-float rule, same matched control, same
plants. The point: the family and its multiplicity budget are frozen HERE, so a surviving hit is not
post-hoc map-fishing.

Object: `E: y^2=x^3+7` (j=0, Aut=μ6, GLV φ, A=0), prime-order subgroup ⟨G⟩ of order m, `p≡1 mod 3`
(so μ3/β exist). Feature source: `int1_frame_operator_v1.py::build`, `xy_interference_U_v1.py::sg`,
`lift_sextant_rhombus_law_proof_v2.py::sextant`/`enorm`. Target source: ARSENAL tool 7 / OPEN_d2.

Decidability of Part (2) PAYOFF is UNCHANGED from v1 §"DECIDABILITY VERDICT": it is a corollary of the
identity, measured as `log2(|B|/|B'|)` bits via the carry/interval formula with no candidate group-mul.
Null identity ⇒ payoff exactly 0. Not restated here; v1 governs it.

---

## 1. OBJECT — public feature covariants (each verified d-FREE) and targets

All features are exact functions with NO scalar d in the path (verified by reading each source):

| feature | type | source (x-only unless noted) | d-free? |
|---|---|---|---|
| `eps(x)` | {0,1,2} | `build(p).eps` | yes — no d in path |
| `sg(x)` signed flap | {−1,0,+1} | `sign(u±v−1/2)`, `(u,v)=coeffs(eis(x))` | yes |
| s-band3 | {0,1,2} | `enorm(eis(x))/p` via int cross-products | yes |
| `sextant(eis(x))` | {0..5} | `sextant(u,v)` | yes |
| `chi2(y)=Legendre(y,p)` | {±1} | **y-coordinate** (public, disjoint from d) | d-free BUT see caveat |

- **s-band3 (exact, no float):** with `E=enorm(eis(x))`, band = 0 if `16E<3p`, 1 if `16E<6p`, else 2
  (thresholds 3/16, 3/8 of `s=E/p`). All comparisons integer cross-products.
- **`chi2(y)` caveat (recorded now, not post hoc):** y is public and disjoint from the carry's
  *construction*, but `chi2(y)` is **ODD in d** (`y([m−d]G)=−y([d]G)`, and `xy_interference` line
  170–174 confirms `sg` even × `s_y` odd decorrelate). Therefore `chi2(y)` may be **tautological**
  against the **parity/sign targets** `c mod 2` and `sign(c)` (both odd-ish in d). Its results against
  those two targets are tagged PARITY-SUSPECT and cannot be read as an eps-family find; the matched
  control (§3, within-j permutation preserves the d↔m−d pairing structure) is the arbiter.
- **`j = χ3`-index is the STRATIFIER, not a feature.** Control permutes the target WITHIN j-bin (§3);
  raw j is excluded as a feature because the target's carry is itself j-dependent (`ε=[d1λ^j+d2λ^j≥m]`)
  — using j as feature AND stratifier would be circular. So j appears only as the stratum label.

**Targets (d-side, disjoint construction, built from scalars only):**
- Two-key carry `carry = [d1 λ^j + d2 λ^j ≥ m]` (binary; the tool-7 payoff object; d1 fixed).
- Single-key `c(d)` derived: `c mod 3` (ternary), `c mod 2` (binary), `[c≠0]` (binary),
  `[sign(c)>0]` (binary).

## 2. STATISTIC — two components, both frozen now

### (I) PRIMARY — OMNIBUS association test (no multiplicity)

The decisive claim: **if the joint feature tuple is independent of the target beyond the matched
control, then NO frozen map in the family can predict the target — a family-wide null in ONE test with
zero multiplicity budget spent.**

- Frozen collapsed joint feature `J(x) = (eps, sign(sg), sband3) ∈ 3×3×3` (27 cells; collapse fixed
  now to keep expected cell counts ≥ ~U/27 workable; sextant and chi2y enter only via component II so
  the omnibus stays low-df and powered).
- Statistic: `G = Σ_{j-strata} 2 Σ_cells O ln(O/E)` — the log-likelihood-ratio (G) statistic between
  `J` and the target, computed per j-stratum and **summed over strata** (this is the pooled/targeted
  form; not a max-over-cells).
- **ONE permutation p-value per target family:** `p_omni = (#{G_control ≥ G_real}+1)/(B+1)`, `B≥5000`,
  control = §3 within-j permutation. Two omnibus tests total: one for `carry`, one for `c mod 3`.
- G is a float transform ranked against a matched permutation null ⇒ allowed (no float threshold
  decides; the count is integer).

### (II) SECONDARY — DECLARED FINITE MAP LIST, Holm–Bonferroni over the frozen count

Explicit (map, target) test list — the family size is **frozen at 31**:

Binary features `F_b` (7): `[eps==2]`, `[eps==1]`, `[s<3/16]` (i.e. sband3==0), `[s>=3/8]`
(sband3==2), `[sg>0]`, `[chi2y==1]`, `[sextant∈{0,2,4}]`.
Ternary features `F_t` (3): `sextant mod 3`, `sg+1`, `sband3`.

- `carry` (binary) × `F_b` = 7 tests.
- `c mod 2` (binary) × `F_b` = 7. `[c≠0]` × `F_b` = 7. `sign(c)` (binary) × `F_b` = 7.
- `c mod 3` (ternary) × `F_t` = 3.
- **Total = 7+7+7+7+3 = 31. Holm–Bonferroni family size N_Holm = 31.**

Per test: G-statistic (2×2 / 2×3 / 3×3) summed over j-strata, permutation p-value vs §3 control.
Holm over the 31 raw permutation p-values; family-wise α = 0.05. A test "survives" iff it clears its
Holm step. The two `chi2(y)`×{`c mod 2`,`sign(c)`} entries are inside the 31 but carry the
PARITY-SUSPECT tag; a survivor there is not an eps-family find without the control distinguishing it.

## 3. MATCHED CONTROL (identical to v1)

Within-j-bin permutation of the TARGET: re-pair each feature tuple with a `carry`/`c` computed from a
`d2'` drawn uniformly from the SAME j-stratum (and same s-branch class) as the true `d2`. Preserves
μ3/μ6 forcing, j-distribution, s-branch structure, and the target marginal; destroys only the
point-to-carry link. A true UNFORCED association survives (`G_real≫G_control`); a μ3-forced coincidence
is preserved in both (`G_real≈G_control`) — no false positive. `B≥5000`.

## 4. PLANTED CONTROLS (unchanged from v1 — must fire before any verdict)

- **Positive:** feature := target ⇒ omnibus `p_omni` significant, and the matching map achieves M=U;
  require plant `z≥6`. If it does not fire, null uninformative — STOP, fix pipeline.
- **Negative:** μ3-symmetry-respecting random feature ⇒ `G≈G_control`, no Holm survivor, `p_omni≈U(0,1)`.
- **Gate plant:** force target `ε=0` whenever `sband3==0`; the `[s<3/16]`→carry map must fire.

## 5. POWER (per curve, U and largest-cell q reported now)

- **Omnibus:** non-centrality `λ = U·w²`, df = (cells_J−1)(cells_T−1) after empty-cell drop
  (≤ 26·1=26 for carry, ≤ 26·2=52 for c mod 3). Detect effect size `w` at power .8 when `λ ≳ df+2√(2df)`.
  For carry (df≈26): need `w ≳ sqrt((26+15)/U)`. Reported per curve below.
- **Per-map (component II):** binary/binary → z ≈ `sqrt(U(1−q)/q)` for a full identity (q=largest
  target cell prob under control). Full identity detectable (z≥6) for U≳55 at q≈0.6. A partial map
  covering unforced fraction f detectable when `f·U(1−q) ≳ 3√(U q(1−q))`; the exact f-threshold is
  reported per curve at run time.
- **Per-curve U (frozen, exact):**

| role | p | m | U=⌊m/3⌋ | full-map z (q=0.6) | omnibus min-w (carry) |
|---|---|---|---|---|---|
| scan | 547 | 547 | 182 | 11.0 | 0.47 |
| scan | 907 | 967 | 322 | 14.7 | 0.36 |
| confirm | 1303 | 1249 | 416 | 16.6 | 0.31 |
| confirm | 1669 | 1663 | 554 | 19.2 | 0.27 |
| confirm | 2089 | 2143 | 714 | 21.8 | 0.24 |

- **Real-82 arm is ZERO-power for the carry identity** (ARSENAL: all 82 give c=0,j=0,s=0 ⇒ no variance).
  Reported as consistency spot-check only; the powered real-analog is the constructed known-generator
  set with non-orbit-min d2 (c varies). Same as v1 §5; not restated in full.

## 6. SCOPE — FIXED OOS PROTOCOL (declared before looking, no seed-shopping)

- **SCAN / design curves:** `p=547` (m=547, U=182), `p=907` (m=967, U=322). All feature/map/omnibus
  development and the first pass happen ONLY here.
- **CONFIRM curves (frozen now):** `p=1303` (m=1249, U=416); `p=1669` (m=1663, U=554); `p=2089`
  (m=2143, U=714). The last two are fixed by the deterministic rule "the two smallest primes p>1303
  with p≡1 mod 12 and #E(F_p) prime" — exact (p,m) computed and frozen above, removing all discretion.
- A scan hit is confirmed ONLY if it survives Holm on **all three** confirm curves under a fresh
  confirmatory prereg (§9). No parameter, map, collapse, target, d1, or curve may change after the scan.
- d1: three fixed values per curve (report each separately; never pooled without scope). Both sets:
  small enumerable curves (decidable core) + constructed known-generator set (powered analog) + real 82
  (spot-check only). Every number inherits `(p, m, d1, U)`.

## 7. EXACTNESS (unchanged)

Signal path int/Fraction throughout: eps, sg (Fraction `coeffs`), enorm, sextant, c, carry, floor — all
exact. `s<3/16` etc. as integer cross-products (`16E<3p`, `8E<3p`, `16E<6p`). No FFT, no float in the
signal path. G and z are float statistics ranked against integer-count permutation nulls only.
`check_no_float.sh` must pass on the run script before it executes.

## 8. FALSIFICATION

- **Family-wide null** iff BOTH omnibus tests are non-significant (`p_omni>0.05`) on the scan curves AND
  all 31 maps fail Holm on the scan — at U-power giving full-map z≥6 (satisfied: min U=182). Then there
  is nothing to confirm; the whole declared family is null on scope.
- A family-wide null does NOT license "no structure" beyond the declared family/curves. It is a SCOPED
  null: bound to {this feature family, these maps, these curves, this U-power, plant fired}, conditional
  phrasing. A per-map bound is a magnitude, never "featureless."
- Any single Holm survivor OR omnibus rejection on the scan is NOT a verdict — it is EXPLORATORY and
  triggers §9.

## 9. PRE-COMMITMENT (filled BEFORE the run)

| Outcome | Conclusion (pre-committed) |
|---|---|
| Positive plant does NOT fire | Null uninformative. STOP. Fix pipeline. No verdict. |
| Both omnibus non-sig AND all 31 maps Holm-null on scan (U-power z≥6) | FAMILY-WIDE SCOPED NULL: "no map in the frozen family predicts {carry, c-derived targets} beyond control on curves {547,907}, U-power z≥11, plant fired." Conditional phrasing. Part (2) payoff = 0 bits by corollary. No confirm run needed. |
| Omnibus rejects OR ≥1 map survives Holm on scan | EXPLORATORY. Freeze the exact surviving (map,target,j-stratum,d1). Open a FRESH confirmatory prereg (single pre-committed statistic = that survivor) on confirm curves {1303,1669,2089}, Holm again. Survives all three → graded EMPIRICAL/VERIFIED-scope, then run Part-(2) payoff bits. Fails any → discarded as a scan chance hit (logged, not a verdict). |
| Survivor is a `chi2(y)`×{`c mod2`,`sign(c)`} cell only | PARITY-SUSPECT: before EXPLORATORY promotion, verify the control (which preserves d↔m−d pairing) still shows `G_real≫G_control`; if the association collapses under the parity-preserving control it is the odd-in-d tautology, discard. |
| Any statistic/map/collapse/target/curve/d1 changed after the scan | Deviation. Disclose; the changed result is EXPLORATORY, never the pre-registered verdict. |

**Nothing about the likely outcome is asserted. The frozen omnibus makes the whole 31-map family a
single decidable test; the map list + Holm bound the multiplicity a scan will otherwise leak; the OOS
curves are fixed by an exact rule. The run fills the numbers.**
