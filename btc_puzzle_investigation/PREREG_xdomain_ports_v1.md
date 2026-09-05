# PRE-REGISTRATION — cross-domain ports (RH-line / LRC-line methodology → secp256k1 curve line)

**Status: SPEC ONLY. FROZEN. No arm has been run. No statistic in this document has been evaluated
on curve data.** Written context-isolated by `experiment-designer`, 2026-07-24.

**Binding on:** any run reporting a result for any of the four proposed ports. A run that changes a
primary statistic, the frozen curve list, the null, the plant, or the outcome mapping MUST file
`PREREG_xdomain_ports_v1_DEVIATIONS.md` naming each change. A deviation is not necessarily wrong; it
is necessarily disclosed.

**Inputs treated as given and not re-tested here:** `xdomain_derivation_checks_v1.py` output (DC1–DC4);
`ANOMALY_DRILL_01_CT_SPLIT_v1.md`; `RESULT_N1_reframed_2sqrtp_cap_v1.md` §1 (the `[−1]` derivation —
note §2/§3 of that file are WITHDRAWN and are **not** used here); `NEXT_DIRECTIONS_v1.md` §3.1/§3.2/§4;
`chi2y_saturation_v1.log`; `_anomaly_drill_ct_split_v2.py` (source read for the state map);
`lift_sextant_rhombus_law_proof_v2.py` (`rdiv`, `reduced_basis`, `sextant`).

**No ECDLP claim is made or reachable by any arm below.** Every arm produces a structural
characterization of curve arithmetic. None reads a scalar bit.

---

## 0. DISPOSITION OF THE FOUR PROPOSALS AGAINST DC1–DC4

| # | proposal as stated | settled by | disposition |
|---|---|---|---|
| 1 | project `H¹` eigenspaces off "coherent μ₃-residue modes"; check whether the residual forces 50% dilution | **DC1** | **RETIRED as stated.** `β` maps `H¹(a) → H¹(aλ)`; it is an isomorphism between *different* twisted cohomologies and has no action on fixed-`a` cohomology, so there is no μ₃-invariant subspace of `H¹(a)` to project off. Same structural defect as `[−1]` (on file) and `ζ₄` (on file, unreviewed). **Replaced by ARM 1.** |
| 2 | event-complete boundary-set enumeration of `C_T` instead of one orbit | **DC4** (premise confirmed: `λ₂=λ₃=1/3` is exact, so a measured split is model deviation, not numerics) | **LIVE, instrument redesigned.** The proposed `n²` enumeration has two forced structures the proposal does not account for (§2.0). **ARM 2 runs the corrected instrument.** |
| 3 | φ(n) grid law → `[k]P` in the Eisenstein fundamental domain / flaps | **DC3** + **DC5 (new, §3.0)** | **RETIRED at secp.** DC3: `n` prime ⇒ `φ(n)=n−1` ⇒ the coprimality *selection* is vacuous. DC5 (derived here, before data): at prime modulus the full-orbit character sum **cannot** vanish exactly unless the readout is constant, so "all non-trivial modes vanish" is structurally impossible, not merely unobserved. **Replaced by ARM 3, which runs only at composite order and has no transfer path to secp — stated up front.** |
| 4 | log-coordinate / φ(n)-averaging operator on the amicable 2-cycle | **DC2** | **RETIRED as stated.** `t_p + t_n = 2` is an identity in the definition of amicability: zero information, and it is the only "boundary condition" the proposal supplies. **Replaced by ARM 4**, the parity-legal channel named in `NEXT_DIRECTIONS_v1.md` §3.2. |

**What survives of each retired proposal — the strictly-remaining question, stated once:**

- **From #1:** *why does a quadratic-character readout on this curve cap at `2√p` regardless of its
  `dim H¹`?* This is an eigenvalue question, and every prior attempt measured `max_a|V(a)|`, a
  magnitude — a proxy. ARM 1 computes the object.
- **From #2:** *is there any inter-coordinate coupling in `C_T` at all, and if so in which subspace of
  the degenerate block?* Prior bound `<2%` at one generator, one orbit, one prime.
- **From #3:** *the φ-selection has content only at composite modulus.* Nothing about `secp` follows
  from any outcome. ARM 3 is characterization of the flap readout at composite order, full stop.
- **From #4:** *the earlier `eis_p(X_d)` vs `eis_n(d)` null was forced to zero by parity* (even vs odd)
  and measured nothing. ARM 4 rebuilds it with an odd-in-`d` curve-side lift.

**A retirement above is a retirement of a proposed MECHANISM. It is not a closure of any frontier.**
§X.6, N1, the flap programme and the amicable correspondence all remain open regardless of every
outcome below.

---

## 1. ARM 1 — the four *twisted* Frobenius eigenvalues of the `χ₂(y)` sheaf (weight profile)

### 1.1 OBJECT
The Frobenius eigenvalue multiset `{α₁(a),…,α₄(a)}` acting on `H¹_c(E ⊗ F̄_p, L_{χ₂(y)} ⊗ L_{χ_a})`,
for `E : y² = x³ + 7 /F_p` with `#E(F_p) = n` prime. This is the Kohel–Shparlinski object itself, not a
correlate of it. The quantity every prior N1 run reported, `max_a |V(a)|`, is `|Σ_i α_i(a)|` — one
linear functional of this multiset.

Tautology check: there is no feature/target pair here. The arm is a deterministic algebraic
computation with an exact instrument check (§1.4). Nothing is correlated against anything.

### 1.2 STATISTIC (exactly one primary)
For frequency `a` and `k = 1,2,3,4`:
```
V_k(a) := Σ_{P ∈ E(F_{p^k}), P ≠ O}  χ₂^{(k)}(y_P) · ζ_n^{ a · dlog_G(Tr_{k/1} P) }        ∈ Z[ζ_n]
```
where `χ₂^{(k)}` is the quadratic character of `F_{p^k}`, `Tr_{k/1}P = Σ_{i=0}^{k−1} φ^i(P) ∈ E(F_p)`
(`φ` = `p`-power Frobenius), and `dlog_G` is the discrete log in `E(F_p) = ⟨G⟩ ≅ Z/n`.
`V_k(a)` is stored as an exact integer coefficient vector of length `n` modulo the all-ones vector
(`Φ_n = 1 + t + ⋯ + t^{n−1}`, `n` prime).

Convention (asserted, then checked by §1.4): `H⁰_c = H²_c = 0` for the non-trivial twisted sheaf, so
the power sums are `p_k := Σ_i α_i(a)^k = − V_k(a)`. Newton's identities on `p₁…p₄` give
`e₁,e₂,e₃,e₄ ∈ Q(ζ_n)` exactly (`fractions.Fraction` coefficients; the only divisions are by `2,3,4`).

> **PRIMARY:  `W₄(a) := e₄(a) · ē₄(a)`, where `ē` is complex conjugation `ζ_n ↦ ζ_n^{−1}`.**
> `W₄(a) = ∏_i |α_i(a)|²`. It is asserted to be a **rational integer** (assert; halt if not).

Deligne gives weights `≤ 1` for `H¹_c` of an affine curve; the weight-graded pieces have `|α_i| ∈ {1, √p}`
(a weight-0 piece is exactly the source of the `+1` in the Kohel–Shparlinski `4√p + 1`). Hence the
pre-listed outcome cells are:

| `W₄(a)` | reading |
|---|---|
| `p⁴` | all four eigenvalues weight `1` (i.e. `|α|=√p`) — the `4√p` ceiling is real and the `2√p` cap is an **alignment** obstruction |
| `p³` | three weight-1, one weight-0 |
| `p²` | **two weight-1, two weight-0** — "eigenvalue starvation": the effective ceiling is `2√p + 2` and N1 is a *weight* fact |
| `p¹`, `p⁰` | ≤ 1 weight-1 eigenvalue |
| `0` | rank drop: `dim H¹_c < 4` at this `a` |
| anything else | the `dim = 4` premise or the Lefschetz convention is wrong — halt, do not interpret |

**Not forced.** Deligne bounds the weights but does not fix the profile; `W₄ = p⁴` and `W₄ = p²` are
both consistent with every theorem currently cited on this record.

**Characterization companions (reported, never a verdict):** `e₁ē₁`, `e₂ē₂`, `e₃ē₃`; the weight
profile per `a`; and — the "effect in a subspace we are not projecting onto" arm — the *ramification*
count recomputed numerically (`dim H¹_c = 2g−2+#R = 4` asserted from `#R = 4`: three 2-torsion zeros of
`y` plus the order-3 pole at `O`). If the measured profile is inconsistent with `dim = 4`, the finding
is the dimension, not the cap.

### 1.3 SCOPE — frozen list, computed at spec-writing time, no later filtering
`E : y² = x³ + 7`, all primes `p` with `#E(F_p) = n` prime and `p ≤ 97` (prime order forces
`p ≡ 1 mod 3`, since `p ≡ 2 mod 3` gives `#E = p+1`, even):

| tier | `(p, n)` | unforced cells `(n−1)/6` |
|---|---|---|
| **DISCOVERY** | `(13,7)`, `(43,31)`, `(61,61)` | `1 + 5 + 10 = 16` |
| **HOLDOUT** (out-of-sample retest; run only after DISCOVERY is written up) | `(67,79)`, `(79,67)`, `(97,79)` | `13 + 11 + 13 = 37` |

**Cell counting (forced-duplication ledger, derived before data).** `V_k(aλ) = V_k(a)` (DC1, `λ³≡1 mod n`,
extended to `k>1` because `β` commutes with `φ` and with `Tr`), and `V_k(−a) = χ₂^{(k)}(−1)·V_k(a)`, which
leaves `W₄` invariant. So `⟨λ, −1⟩` of order 6 acts on `(Z/n)∖{0}` and **the number of distinct
configurations is `(n−1)/6`, not `n−1`.** `6 | n−1` for all six curves (checked: 6,30,60,66,78,78).
Any tally reported as `366/366` would be **313 forced bits**; the honest denominators are **16** and **37**.
`a = 0` is excluded by name (forced: `V_k(0)` is a point count).

### 1.4 PLANTED CONTROL — must fire, or the arm is void
1. **Inverter plant.** Choose a known multiset `A = {α_i}` with a stated weight profile (e.g.
   `{√p·ζ₁₂, −√p·ζ₁₂, 1, −1}` realised inside `Z[ζ_{12n}]`), synthesise `p_k = Σα_i^k`, feed the
   Newton inverter, and require **exact** recovery of `e₁…e₄` and of `W₄`. Firing criterion: exact
   equality for **3/3** planted profiles, one per outcome cell `p⁴ / p³ / p²`.
2. **Dimension plant.** At `p = 13` compute `V_k` for `k = 1…6` and require that the degree-4 char
   polynomial recovered from `k ≤ 4` **predicts `p₅` and `p₆` exactly**. Firing criterion: exact match.
   At `p = 43` do the same with `k ≤ 5`. At `p ≥ 61` this check is **not run** (cost `p⁵`) — disclosed
   as a scope limit, and the `dim = 4` premise is then carried by `p ∈ {13,43}` plus the `#R` count.
   **If the `k=5,6` prediction fails at `p=13`, the whole arm halts** and the finding is that the
   convention or the dimension is wrong.

There is no statistical null here because there is no statistic with a sampling distribution: the
computation is deterministic and exact. That is stated, not hidden.

### 1.5 POWER
Deterministic and exact ⇒ detection probability **1** for any weight profile, at every one of the
**16** DISCOVERY / **37** HOLDOUT cells. The limitation is not power, it is **`p` range**: `p ≤ 97`.
Falsifying a claim of the form "the profile is `X` for all `p`" requires one counterexample; the arm
cannot address `p ≈ 2²⁵⁶` and does not claim to.

### 1.6 EXACTNESS
Integers and `Fraction` throughout. `F_{p^k}` implemented as `Z[t]/(f)` with `f` a frozen irreducible
of degree `k` over `F_p`, all coefficients `int`. `Z[ζ_n]` as integer vectors modulo the all-ones
vector. Conjugation is index negation. **No float anywhere in ARM 1**, including reporting: `W₄` is
compared to `p^j` by integer equality, never by tolerance. `|α_i|` are *not* computed.

### 1.7 PRE-COMMITMENT (written before the run)
| DISCOVERY outcome | conclusion, fixed now |
|---|---|
| `W₄ = p²` at **16/16** | **N1 is a weight fact, not an alignment fact.** The effective ceiling for `χ₂(y)` is `2√p + O(1)`, the "½" is the ratio of the true ceiling to the nominal `4√p`, and the RH-style "projection off a coherent subspace" framing is the wrong shape for it: there is no subspace to project off, there are simply two fewer weight-1 eigenvalues. Promote to HOLDOUT. Grade if HOLDOUT also 37/37: `[MEASURED-EXACT, 53/53 unforced cells, p ≤ 97]`. **Not** a theorem; the `p`-uniform statement stays OPEN. |
| `W₄ = p⁴` at **16/16** | **N1 is an alignment obstruction.** Four weight-1 eigenvalues exist and something prevents them aligning past `2√p`. *This is the outcome under which the RH-line port acquires content*, since an alignment obstruction is exactly what a coherent-subspace argument would explain — but the μ₃ route to it is dead (DC1) and a new symmetry acting **within** fixed-`a` cohomology must be named before any further port is attempted. Grade: `[MEASURED-EXACT, …]` + a named open question. |
| mixed across `a` within a curve | **The profile is `a`-dependent.** Report the exact partition of the `(n−1)/6` cells by profile and the invariant that separates them (candidate strata pre-listed: `χ₃(a)`, `χ₂(a)`, order of `a` mod small primes). This is a *sharper law*, and it is the most informative outcome. |
| mixed across curves, constant within | Report the `p`-invariant separating them (pre-listed: `p mod 4`, `p mod 9`, `m = b₂/p` of `A_new`). |
| `W₄ ∉ {p⁴,p³,p²,p,1,0}` at any cell | **HALT.** Premise failure. File the deviation; do not interpret any other cell. |

**FALSIFICATION.** The hypothesis "the `2√p` cap on `χ₂(y)` is an eigenvalue-weight phenomenon" is
falsified by `W₄ = p⁴` at any single unforced cell. The hypothesis "the cap is an alignment
phenomenon" is falsified by `W₄ = p²` at any single unforced cell. Exactly one of them will be
falsified per cell; that is the design.

---

## 2. ARM 2 — `C_T` inter-coordinate coupling on the AP-complete population

### 2.0 TWO FORCED STRUCTURES IN THE PROPOSED INSTRUMENT (derived here, before any data)

The proposal is: enumerate all `n` step sizes `g` and all `n` positions `d`, transition
`s([d]G,[d+g]G) → s([d+g]G,[d+2g]G)`, `n²` transitions, floor `√30/n`. Two facts about the state map
as implemented (`_anomaly_drill_ct_split_v2.py`) change what this instrument measures.

**F1 — `state` depends only on the SUM of its two arguments.**
```python
def state(z1, z2):
    sx, sy = z1[0] + z2[0], z1[1] + z2[1]
    return (rdiv(sx * R2[1] - sy * R2[0], DET), rdiv(-sx * R1[1] + sy * R1[0], DET))
```
Hence `state(z1,z2) = state(z2,z1)` identically.

**F2 — the lift array is EVEN in `d`.** `Z[d] := eis(x([d]G))` and `x([−d]G) = x([d]G)`, so
`Z[−d] = Z[d]`. Only `(n−1)/2 + 1` distinct values exist.

**Consequences (all forced; each is an instrument check whose confirmation carries ZERO information as
evidence, and whose failure means the code does not implement the stated map):**

- **(C1) The count matrix is exactly symmetric.** The map `(d,g) ↦ (d+2g, −g)` is a fixed-point-free
  involution on `{(d,g) : g ≠ 0}` and, by F1, exchanges `s₁ ↔ s₂`. Therefore
  `N[i][j] = N[j][i]` **exactly**, for every curve. The AP-complete estimator is a **reversible**
  chain: `λ₂, λ₃` are real by construction, and **every statistic on the antisymmetric part of `C_T`
  is identically zero — zero information. Named and excluded from ARM 2.**
- **(C2) Each transition is counted exactly twice.** `(d,g) ↦ (−d,−g)` preserves both `s₁` and `s₂`
  by F2, so **all counts are even** and the number of *distinct* enumerated events is
  `(n(n−1) − #degenerate)/2 ≈ n²/2`, not `n²`.
- **(C3) The AP-complete operator is NOT the `g=1` operator with more samples.** It is the pooled
  operator over all 3-term arithmetic progressions in `Z/n`, and pooling `g` with `−g` is what
  symmetrises it. The `g=1` drill measured a *directed* operator. **The proposal's phrase "the
  COMPLETE population of the operator" is inaccurate; it is the complete population of a
  different, reversible operator.** Both are legitimate objects; the run must not report a bound on
  one as a bound on the other.
- **(C0) C1 and C2 were verified at spec-writing time on a synthetic even array with a
  sum-symmetric state map** (`n = 101`: count matrix exactly symmetric, all 9800 counts even). This is
  an instrument check on the *derivation*, on synthetic indices only; no curve data was read.
- **(C4) The floor `√30/n` is an assumption the design violates.** The `n²` triples are built from
  `≤ (n+1)/2` distinct lattice values; each `Z[d]` participates in `Θ(n)` triples. The Hájek
  projection of such a U-statistic has variance `Θ(1/n)`, not `Θ(1/n²)`, unless it is annihilated by
  centring against the estimated marginals. **The floor is therefore between `≈ √30/n` and
  `≈ √(30/n)` and must be MEASURED, not assumed.** At `n = 2143` the bracket is
  **`0.26%` … `11.8%` — a factor of 45.** The claimed "6–30× power gain" is a hypothesis this arm tests.

### 2.1 OBJECT
The deviation `D := Ĉ_T − Ĉ₁ ⊗ Ĉ₂` restricted to the **near-degenerate 2-dimensional block** of
`Ĉ₁ ⊗ Ĉ₂` — i.e. the first-order generator of the `λ₂/λ₃` splitting that DC4 shows is exactly zero
under the model.

**Shared-construction disclosure.** `D` is a residual of the data against a model fitted from the
*same* counts (the marginals `Ĉ₁, Ĉ₂` are computed from `N`). This is the same shape as the
`r = v − w` hazard and it is why an asymptotic `χ²` reference with naive `df` is **excluded**: the
fitting bias is reproduced exactly by the surrogate ensemble (which re-estimates its own marginals the
same way), and the surrogate ensemble is the only null used for the primary.

### 2.2 STATISTIC (exactly one primary)
Let `Π` be the projector onto `span{ 1 ⊗ v₂ , u₂ ⊗ 1 }` (right) with matching left projector, where
`u₂, v₂` are the second right-eigenvectors of `Ĉ₁, Ĉ₂`. Write `B` for the resulting `2×2` block of
`D` in the biorthogonal basis, `B_{xy} = ⟨f_x, D e_y⟩ / ⟨f_x, e_x⟩`.

> **PRIMARY:  `T₂ := ‖B‖_F² = B_aa² + B_ab² + B_ba² + B_bb²`**

Four real dimensions, aimed exactly at the degeneracy: `T₂` is the first-order generator of `|λ₂−λ₃|`.
It is **not** a max over 81 cells (`max|C_T − C₁⊗C₂|`, the v1 estimator, is upward-biased and
low-power — excluded by name) and **not** `|λ₂−λ₃|` itself (a non-negative gap, upward-biased —
excluded by name, reported only as a companion).

**Null:** the matched surrogate ensemble of §2.3, `B = 200` draws, integer-rank p-value
`p = (1 + #{b : T₂^{(b)} ≥ T₂^{obs}}) / (B+1)`. No asymptotic reference is used for the decision.

**SECONDARY (mandated "effect outside the projected subspace"):**
`T_out := ‖D‖_F² − ‖Π D Π‖_F²`, ranked against the same `B` draws. A coupling living outside the
degenerate block is visible here and is *named*, not lost.

**CHARACTERIZATION (signed, reported always, never a verdict):** `B_aa − B_bb` (split along the
near-degenerate diagonal); `B_ab, B_ba`; `‖D_even‖_F, ‖D_odd‖_F` in the swap channel
`S : (c₁,c₂) ↦ (c₂,c₁)`; per-`g` operators `Ĉ_T^{(g)}` and their dispersion (the directed information
that C1 destroys in the pooled object).

### 2.3 MATCHED CONTROL
**Primary null (N-B, the null of the stated hypothesis).** Build a synthetic array `Z'` of length `n`
whose two lattice coordinates are drawn **independently** with exactly the measured per-coordinate
marginals of `Z`, and with `Z'[−d] = Z'[d]` imposed (F2). Then run the **identical** AP-complete
`n²` enumeration on `Z'`.
- **Preserves:** array length `n`; the evenness `Z[−d]=Z[d]`; both per-coordinate marginals exactly;
  the AP overlap/dependence structure; the marginal re-estimation step; C1 and C2 (assert both hold
  in every surrogate draw — if a surrogate draw is not symmetric, the null is mis-built).
- **Destroys:** only the joint coupling between the two lattice coordinates — the hypothesis under test.

**Secondary null (N-A).** Permute the distinct values of the `Z` array (respecting `Z[−d]=Z[d]`) and
re-enumerate. Preserves the exact multiset of lattice points and destroys the arithmetic association
with `d`. Reported alongside; it answers a different question (arithmetic vs. any point multiset) and
its answer must be labelled as such.

### 2.4 PLANTED CONTROL — must fire, or the arm is void
Into the N-B surrogate, inject a coupling at level `ε`: with probability `ε` (applied to the antipodal
pair `{d,−d}` jointly, preserving F2), set the second lattice coordinate of `Z'[d]` to a fixed
deterministic function of the first. Sweep `ε ∈ {0.001, 0.002, 0.005, 0.01, 0.02, 0.05}`.
**Firing criterion:** there exists `ε* ≤ 0.05` at which `T₂` rejects at `α = 0.01` in **≥ 18/20**
planted draws. If no `ε ≤ 0.05` fires, the instrument has no power in the interesting range and
**ARM 2 reports "no informative bound", not a bound.**

### 2.5 POWER — computed as an ordering-enforced pre-step
**The entire calibration (§2.3 null ensemble + §2.4 plant sweep + the resulting `ε*`) is run and its
output file hashed BEFORE `T₂` is computed on real curve data.** Two scripts, two outputs; the
real-data script asserts the hash of the calibration output at start.

Pre-run bracket (this is what the arm measures, and the claim it adjudicates):

| scenario | floor at `n = 2143` | floor at `n = 5953` | verdict on the proposal's "6–30× gain" |
|---|---|---|---|
| independent triples, `√30/n` | `0.26 %` | `0.092 %` | CONFIRMED |
| Hájek-dominated, `√(30/n)` | `11.8 %` | `7.1 %` | REFUTED (the enlargement buys `<2×` over the `g=1` orbit) |

**Scaling measurement (pre-registered, and pre-registered against the DRILL-01 failure mode):** fit
`floor ~ n^{−α}` by OLS on `log(floor)` vs `log n` using **all 37** curves of §2.6, `B = 20` surrogate
draws each. **No curve may be dropped for any reason**; any curve that fails to compute is listed by
name with its error and the fit is reported both with and without it. `α` is reported with its CI and
is a **descriptive secondary only — it is never used to extrapolate a bound to an unmeasured `n`.**
(DRILL-01 fitted `p^{−0.36}` from 3 points, 2 of them junk; that failure is the reason for this clause.)

### 2.6 SCOPE — frozen list, computed at spec-writing time
`E : y² = x³ + 7`, `p ≡ 1 mod 3`, `#E(F_p) = n` prime, `1000 ≤ n ≤ 6000`. **All 37 such `p`:**
```
991 1051 1237 1249 1303 1669 1831 2089 2143 2251 2281 2503 2647 2677 2731 3271 3343 3511 3571
3673 3691 3739 3853 3931 4159 4243 4447 4513 4549 4597 4831 5107 5197 5281 5791 5923 6091
```
- **PRIMARY (`B = 200` surrogates):** the 9 curves with `n ≤ 2143` —
  `p ∈ {991, 1051, 1237, 1249, 1303, 1669, 1831, 2089, 2143}`.
- **HOLDOUT (run only after PRIMARY is written up):** the 6 largest `n` —
  `p ∈ {5107, 5197, 5281, 5791, 5923, 6091}`.
- **SCALING (`B = 20`):** all 37.
- Degenerate index exclusions, stated now: `g = 0`; and any triple with `d ≡ 0`, `d+g ≡ 0`, or
  `d+2g ≡ 0 (mod n)` (the point at infinity has no lift). The **count of excluded triples must be
  printed** (`≈ 3n` of `n²`). A silent exclusion is the DRILL-01 failure and voids the run.
- **Every number this arm produces carries:** `E: y²=x³+7`, this `p`, full group (prime order, so the
  orbit is the whole group and the generator drops out of the scope — this is the one scope
  reduction the enlargement genuinely buys), AP-complete population, `T₂` estimator, N-B null.

### 2.7 EXACTNESS
`N` is an exact integer matrix (`numpy` `int64` with an asserted `|value| < 2⁶²` guard on every
intermediate of `rdiv`); `Ĉ_T, Ĉ₁, Ĉ₂, D` are exact `Fraction`s. **Float carve-out, named:** the
eigenvectors `u₂, v₂` defining `Π`, and the eigenvalue companions. Justification: (i) `Π` is built from
the **measured marginals only** — which are the null's own nuisance parameters, preserved by
construction — and is **frozen** in the calibration phase; (ii) the identical frozen `Π` is applied to
the real data and to every surrogate draw, so the p-value is an integer rank unaffected by the
projector's precision to first order; (iii) no float is ever compared to a threshold applied to data.
The exact integer `N` is written to disk and hashed for every curve.

### 2.8 PRE-COMMITMENT
| outcome | conclusion, fixed now |
|---|---|
| plant does **not** fire at any `ε ≤ 0.05` | **ARM 2 is void.** Report "uninformative instrument", not a bound. Do not report `T₂` on real data. |
| `T₂` rank-p `≤ 0.01` on `≥ 5/9` PRIMARY curves | **A coupling exists in the degenerate block.** Report its *location*: sign of `B_aa − B_bb`, the swap-even/odd split, and the eigenvector. Retest on HOLDOUT before naming it. If HOLDOUT does not reproduce, the discovery is **not named** (two chance patterns have already died this way on this record). |
| `T₂` rank-p `> 0.01` on `≥ 5/9`, plant fired at `ε*` | **Bound, with power and scope:** "any inter-coordinate coupling in the AP-complete `C_T` is below `ε*` at `n ≤ 2143`, for `E:y²=x³+7`, these 9 primes, the full group, the `T₂` estimator and the N-B null." **This is a magnitude. It is not `no structure`, not `generic`, not `safe`, and it does not close §X.6.** The structure question stays where DRILL-01 left it: which subspace. |
| `T₂` null but `T_out` fires | **The coupling is outside the degenerate block.** Report the subspace. This is the outcome the primary is *not* aimed at, and it is why `T_out` is in the spec. |
| `α ≈ 0.5` in the scaling fit | The proposal's "6–30× power gain" is **REFUTED**; record that AP-completeness removes generator scope but does **not** buy `n²` samples. |
| `α ≈ 1.0` | **CONFIRMED**; the `√30/n` floor is real and `n ~ 10⁴` reaches `0.05%`. |
| per-`g` dispersion large | `Ĉ_T^{(g)}` is `g`-dependent ⇒ pooling was the wrong object; the finding is the `g`-dependence and the pooled bound must be withdrawn. |

**FALSIFICATION.** "`C_T` is an exact tensor square of the AP-complete population" is falsified by
`T₂` rejecting at `α = 0.01` on the PRIMARY set **and** reproducing on HOLDOUT. "The AP enlargement
gains `6–30×`" is falsified by `α < 0.75` in the scaling fit.

---

## 3. ARM 3 — exact-vanishing census of the flap readout at composite order

### 3.0 DC5 (derived here, before data): the φ(n) port is structurally void at prime modulus
Let `m` be the group order, `h : Z/m → μ_6 ∪ {0,1}` any readout, and `W(a) = Σ_d h(d) ζ_m^{ad}`.
For `m` **prime**, `Z[ζ_m]` is free over `Z` (resp. over `Z[ζ_6]`) on `1, ζ, …, ζ^{m−2}`, so
`Σ_j b_j ζ_m^j = 0` **iff all `b_j` are equal**. Since `b_j = h(a^{−1}j)` is a relabelling of `h`,
`W(a) = 0` for some `a ≠ 0` **iff `h` is constant**. Therefore:

> **At prime `n`, "all non-trivial Fourier modes vanish" is impossible for any non-constant readout.**
> DC3 already made the coprimality *selection* vacuous; DC5 makes the *conclusion* unattainable.
> The LRC φ(n) grid law has **no non-vacuous transfer to secp256k1**, and no outcome of ARM 3
> can create one. This is stated up front and is not revisited after the run.

The law has content only where `φ(m) < m−1`, i.e. `m` composite. ARM 3 runs there, as
characterization of the flap readout — **not** as a step toward secp.

### 3.1 OBJECT
The exact vanishing locus of the discrete Fourier transform of the flap indicator along a cyclic
subgroup of composite order, and its relation to the primitive residues.

### 3.2 STATISTIC (exactly one primary)
`E : y² = x³ + 7 / F_p`, `p ≡ 1 mod 3` (required for the Eisenstein lattice to exist), `G` a point of
maximal order `m = exponent(E(F_p))`, `m` composite. Flap indicator, as implemented on this record:
```
ε(X) = 1  ⟺  2·|cent(X) − cent(ρ·X mod p)| > p ,      ρ = β + 1 a primitive 6th root mod p
h(d)  = ε( x([d]G) ) ∈ {0,1}
W(a)  = Σ_{d=0}^{m−1} h(d) · ζ_m^{a d}   ∈ Z[ζ_m]   (integer coefficient vector, length m)
```
> **PRIMARY:  `Z_unf := #{ a : gcd(a,m) = 1, a ≢ −a, W(a) = 0 exactly }`,**
> counted over one representative per `{a, −a}` pair.

Exact zero test: integer polynomial remainder of `Σ_k c_k x^k` modulo `Φ_m(x)` over `Z`, asserted to
be the zero polynomial. No tolerance, no float.

**Forced ledger, derived before data (these cells carry ZERO information and are excluded from
`Z_unf` by name):**
- `a = 0` (forced non-zero: `W(0) = Σh > 0`).
- `gcd(a,m) = g > 1`: `W(a)` collapses to a transform on `Z/(m/g)` of the folded counts, and vanishes
  for structural subgroup reasons. **These are the "non-primitive" residues; zeros there are FORCED
  and are the analogue of the LRC law's excluded times.** They are counted and reported *separately*
  as `Z_forced`, never pooled into `Z_unf`.
- `h` is **even**: `x([−d]G) = x([d]G)` ⇒ `h(−d) = h(d)` ⇒ `W(−a) = W(a)`. So `a` and `−a` are **one**
  configuration. Denominator is `φ(m)/2`, not `φ(m)`.

**Magnitude companion (mandated, so a suppression is not lost when there is no exact zero):**
`R_min := min_{a unforced} |W(a)|² / m`, ranked against the null ensemble. Float carve-out: `|W|²`
from the exact integer coefficient vector, analytic size only; the *exact-zero* decision never touches
it.

### 3.3 SCOPE — frozen list, computed at spec-writing time
All `p` with `p ≡ 1 mod 3`, `100 ≤ p ≤ 420`, `m = #E(F_p)` composite with `100 ≤ m ≤ 400` — **21 curves**:
```
p    103 109 139 151 157 181 193 199 223 229 241 271 277 283 307 313 331 337 367 373 379
m    111 129 147 133 172 208 219 189 252 259 259 243 273 309 327 292 364 372 372 336 343
```
Total unforced cells `Σ φ(m)/2 = 1464`. **DISCOVERY** = the 14 curves with `p ≤ 283`;
**HOLDOUT** = the 7 with `p ≥ 307`. Frozen now.
If `exponent(E) ≠ #E` for a curve (non-cyclic), use `m = exponent(E)`, recheck the `100 ≤ m ≤ 400`
window, and **list by name any curve that leaves the window, with the reason** — no silent drop.

### 3.4 MATCHED CONTROL
**Null:** permute `h` **within the constraint that defines the readout**: `h` is even in `d`, so the
null permutes the `(m−1)/2` antipodal classes (and, independently, may re-assign the class at `d=0`).
- **Preserves:** the exact value multiset of `h`; the evenness `h(−d) = h(d)` and hence the forced
  relation `W(−a) = W(a)`; the group `Z/m` and all its subgroup structure; `Z_forced` behaviour.
- **Destroys:** only the association between the flap label and the discrete log.
**A plain shuffle of `h` over `d` is EXCLUDED by name**: it breaks the evenness the readout has by
definition, i.e. it destroys a symmetry the statistic inherits — the exact μ₆-blind-shuffle defect
already caught on this record. A run using a plain shuffle here is void.
`B = 200` null draws per curve ⇒ `4200` surrogate curves, resolution `2.4×10⁻⁴` on the null zero rate.

### 3.5 PLANTED CONTROL — must fire, or the arm is void
Construct `h_plant` with a **known** exact zero at a **primitive** frequency: pick `a₀` with
`gcd(a₀,m)=1`, and build `h_plant` by adding, to a random even base labelling, an even perturbation
lying in the kernel of the `a₀`-transform (e.g. for `q | m`, a `±1` pattern supported on a coset of the
index-`q` subgroup, symmetrised in `d ↦ −d`). **Firing criterion:** the census returns `Z_unf ≥ 1` and
identifies `a₀`, in **3/3** planted curves. If the census cannot find a zero that was put there, the
arm is void.

### 3.6 POWER
Exact arithmetic ⇒ **any** exact zero is detected with probability 1. The meaningful power number is
the false-positive side: the null zero rate is resolved to `2.4×10⁻⁴` (§3.4). For the magnitude
companion `R_min`, a suppression is detectable at `α = 0.01` when the real `R_min` falls below the
`1/(B+1) = 0.5%` quantile of the null ensemble — i.e. the arm resolves a suppression only if it is
the most extreme of 201 draws; no finer claim is available at `B = 200`.

### 3.7 EXACTNESS
`int` only in the signal path: `cent`, `ρ·X mod p`, the `ε` comparison (an integer inequality),
`c_k` counts, the `Φ_m` remainder. Float appears only in `R_min`'s reported magnitude. **No float
threshold is ever applied to data.**

### 3.8 PRE-COMMITMENT
| outcome | conclusion, fixed now |
|---|---|
| plant does not fire | **ARM 3 void.** Report an uninformative instrument. |
| `Z_unf = 0` across all 1464 unforced cells, plant fired | **The φ-grid law does not transfer as an exact vanishing law**, at composite order `100 ≤ m ≤ 400`, for the flap indicator on `y²=x³+7`. Grade `[MEASURED-EXACT, 21 curves, m ≤ 400, flap indicator only]`. **This is a scoped negative about ONE readout at ONE size range. It is not a closure of the flap programme and says nothing about other readouts or about secp (where DC5 already makes the question void).** |
| `Z_unf > 0` on DISCOVERY | **A conservation candidate.** Do not name it. Report: which `a`, the Lam–Leung length of the vanishing sum, which subgroup structure carries it, and whether the same `a`-invariant appears on the HOLDOUT 7 curves. **Name it only after out-of-sample reproduction.** Grade if reproduced: `[MEASURED-EXACT + OOS]`; if not: `[chance pattern, dropped]` — recorded, not hidden. |
| `Z_unf = 0` but `R_min` in the bottom `0.5%` on `≥ 10/14` DISCOVERY curves | **A suppression, not a vanishing.** Report as a magnitude with its `B = 200` resolution, and name the next probe (larger `B`, or the norm-based exact suppression measure). |
| `Z_forced` does not match the subgroup prediction | **HALT** — the forced ledger is wrong, and every unforced count inherits the error. |

**FALSIFICATION.** "The φ(n) grid law transfers to the curve as exact modal vanishing" is falsified by
`Z_unf = 0` at 1464/1464 unforced cells with a fired plant. It is *already* falsified at secp by DC5,
independently of this run.

---

## 4. ARM 4 — the parity-legal amicable channel `eis_n(cent y([d]G))` vs `eis_n(d)`

### 4.1 OBJECT
The joint law of two lattice reductions of the **same** ideal `(π_n) = (π_p − 1) ⊂ Z[ω]`: one applied
to a curve-side coordinate, one applied to the scalar. The amicable relation `#E(F_p)=n`,
`#Ẽ(F_n)=p` is a verified fact of secp on this record; the two quotients `Z[ω]/(π_p) ≅ F_p` and
`Z[ω]/(π_n) ≅ Z/n` differ by the `−1`, and that slippage is the object.

**Why the prior null was uninformative (not repeated here):** `eis_p(X_d)` is **even** in `d`
(`x(−P) = x(P)`) and `eis_n(d)` is **odd** in `d`; the linear channel between an even and an odd
function is `0` **by parity, before any data**. DC2 supplies no replacement premise (`t_p+t_n=2` is a
definition). ARM 4 uses an **odd-in-`d`** curve-side lift, which is the only version of the test that
can carry information.

**Tautology check.** Feature `s_u(d) = sextant(eis_n(cent(y([d]G))))` is a function of the point;
target `s_w(d) = sextant(eis_n(d))` is a function of the scalar. Neither is a sub-construction of the
other; they share only the lattice `L_n` and the reduction map. **No `r = v − w` hazard.** They are
linked only through the group law, i.e. through the ECDLP map.

### 4.2 STATISTIC (exactly one primary)
Sample `S = {±d_1, …, ±d_{K₀}}`, `d_i` drawn uniformly from `[1,n)` with a frozen seed
(`K₀ = 2×10⁵`, `K = |S| = 4×10⁵`). For `j,k ∈ Z/6`:
```
U_{j,k} = Σ_{d ∈ S} ζ₆^{ j·s_u(d) + k·s_w(d) }   ∈ Z[ζ₆]        (|U|² ∈ Z, exact)
```
**Forced ledger, derived before data.** `cent(−Y mod p) = −cent(Y)` and `eis_n(−X) = −eis_n(X)` (up to
the `rdiv` tie case, §4.6) give `s_u(−d) = s_u(d)+3` and `s_w(−d) = s_w(d)+3` in `Z/6`. Since `S` is
parity-closed, `U_{j,k} = (−1)^{j+k} U_{j,k}`, so:
> **`U_{j,k} = 0` EXACTLY whenever `j+k` is odd — 18 of the 36 isotypes. Forced. Zero information.**
> Unforced: 18, minus the trivial `(0,0)` = **17 real degrees of freedom**.

A μ₆-**equivariant** coupling (the joint depending only on `s_u − s_w`) lives exactly on the diagonal
isotypes `(j,−j)`, `j = 1..5`: real dimension **5** (conjugate pairs `{(1,5),(5,1)}`, `{(2,4),(4,2)}`,
self-conjugate `(3,3)`). Aim there. *(Ledger arithmetic — 18 forced / 17 real df / 5 diagonal — and the
`rdiv` tie characterisation were both verified combinatorially at spec-writing time; no curve data read.)*
> **PRIMARY:  `T₄ := Σ_{j=1}^{5} |U_{j,−j}|²`**  (exact integer; `df = 5`).

**SECONDARY (mandated "outside the projected subspace"):** `T_off := Σ_{j+k even, (j,k)≠(0,0), k≠−j} |U_{j,k}|²`
(`df = 12`), ranked against the same null. A non-equivariant coupling shows here.
**CHARACTERIZATION:** the full `6×6` integer contingency table; the per-isotype `|U_{j,−j}|`; and which
`j` carries the mass (`j=3` is the pure sign/parity channel, `j=1,5` the primitive-6th-root channel —
this is the only place in the battery where a genuine "primitive-residue" reading survives, and it is
`m = 6`, not `m = n`).

### 4.3 SCOPE
**secp256k1 itself**: `p = 2²⁵⁶ − 2³² − 977`, `n` the real group order, `G` the standard generator,
`π_p` by Cornacchia on `4p = a² + 3b²`, `L_n = gauss_reduce((A_p−1, B_p), (−B_p, (A_p−1)−B_p))` (the
construction already on file). `K = 4×10⁵` sampled scalars, frozen seed. **This is the only arm in the
battery that runs at full `2²⁵⁶` scale.** Every number carries: secp256k1, `y`-coordinate readout,
`L_n` reduction, sextant quantisation, `K = 4×10⁵`, pair-permutation null.

### 4.4 MATCHED CONTROL
**Null (pair-permutation).** Represent `S` as `K₀` antipodal pairs. Draw a permutation `σ` of
`{1..K₀}` and signs `ε_i ∈ {±1}`; define `π(±d_i) = ±ε_i d_{σ(i)}`. Pair `(s_u(d), s_w(π(d)))`.
- **Preserves:** both exact value multisets; the parity covariance `π(−d) = −π(d)` and hence **all 18
  forced zeros** (assert this on every draw — a null that breaks the forced zeros is mis-built and
  voids the arm); `K`; the sample `S`.
- **Destroys:** only the pairing between curve-side and scalar-side labels.
`B = 999` draws; integer-rank p-value.

**Secondary null (multiplicative rotation).** `w'_d := s_w(c·d mod n)` for random `c`. Preserves more
arithmetic structure (it is an automorphism of `Z/n`). **Excluded `c` by name:** `c ∈ {±1}` (identity)
and `c ∈ ⟨λ⟩·{±1}` (the order-6 GLV subgroup — forced-related by DC1). Reported as a stricter null;
disagreement between the two nulls is itself a reportable characterization.

### 4.5 PLANTED CONTROL — must fire, or the arm is void
With probability `ε`, replace `s_u(d_i)` by `s_w(d_i)` for the whole antipodal pair (parity-consistent:
`s_u(−d) = s_u(d)+3` is re-imposed). Sweep `ε ∈ {0.001, 0.002, 0.005, 0.01, 0.02}`.
**Firing criterion:** `T₄` rejects at `α = 0.01` in **≥ 18/20** planted draws at some `ε ≤ 0.02`.

### 4.6 POWER (computed now, not after)
`T₄` has `df = 5`. Under a local alternative with per-isotype correlations `ρ_j`, the non-centrality is
`λ = K · Σ_{j=1}^{5} |ρ_j|²`. For `α = 0.01` (`χ²₅` critical `15.09`) and `80%` power, `λ* ≈ 18`
(normal approximation to the non-central `χ²`; the run replaces this with the empirical plant curve).
Hence at `K = 4×10⁵`:
```
Σ_j |ρ_j|²  ≥  4.5×10⁻⁵      ⇔      per-isotype |ρ|  ≥  3.0×10⁻³   (5 equal isotypes)
copy-fraction plant:  ε*  ≈  |ρ| / (5/6)  ≈  3.6×10⁻³   (≈ 0.36 %)
```
`T_off` (`df = 12`, critical `26.2`, `λ* ≈ 22`): per-isotype `|ρ| ≥ 2.1×10⁻³`.
**Pre-registered extension:** if `K` is raised to `4×10⁶`, the same formulas give
`|ρ| ≥ 9.5×10⁻⁴`, `ε* ≈ 0.11%`. Any `K` other than `4×10⁵` must be declared in the deviations file.

### 4.7 EXACTNESS
`int` only: the scalar multiplication, `cent`, the `L_n` reduction (`rdiv` on integers), `sextant`
(integer comparisons), the counts, and `|U_{j,k}|²` (an integer, computed in `Z[ω]` coordinates —
`|a+bω|² = a²−ab+b²`). **No float in the signal path.** `numpy int64` permitted with an asserted
`< 2⁶²` guard.
**Named forced-asymmetry ledger:** `rdiv` rounds ties toward `+∞`, so `rdiv(−ν,δ) = −rdiv(ν,δ)` fails
exactly when `2·(ν mod δ) = δ`. The **count of tie-broken indices must be printed** for both `s_u` and
`s_w`; if any forced zero `U_{j,k}` (`j+k` odd) is non-zero, it must equal the tie count's signature,
and if it does not, **HALT** — the parity premise is wrong and the `df = 5` ledger is wrong with it.

### 4.8 PRE-COMMITMENT
| outcome | conclusion, fixed now |
|---|---|
| plant does not fire at any `ε ≤ 0.02`, or a null draw breaks a forced zero | **ARM 4 void.** Report an uninformative instrument, not a bound. |
| `T₄` rank-p `≤ 0.01`, both nulls | **A μ₆-equivariant coupling exists between the two quotients of `Z[ω]` at secp scale.** Report which `j` carries it and its size `|ρ_j|`. This is a *structural* statement about the amicable pair; at `|ρ| ~ 10⁻³` it is **not** a key-recovery claim and must not be described as one. Next probe named in the same document. |
| `T₄` rank-p `> 0.01`, plant fired at `ε*` | **Bound with power and scope:** "any μ₆-equivariant coupling between `eis_n(cent y([d]G))` and `eis_n(d)` is below `|ρ| = 3.0×10⁻³` at `K = 4×10⁵` on secp256k1, sextant quantisation, pair-permutation null." **A magnitude. Not `no leakage`, not `generic`, not a closure of §XI.3/§X.3.** The obvious next moves (finer quantisation than 6 cells; the `xy` readout instead of `y`; larger `K`) are named in the result document. |
| `T₄` null but `T_off` fires | **The coupling is non-equivariant.** Report the isotype. This is exactly why `T_off` is in the spec. |
| the two nulls disagree | Report both. The pair-permutation null and the rotation null differ by the arithmetic of `Z/n`; a disagreement localises the effect in that arithmetic and is a *finding*, not a nuisance. |

**FALSIFICATION.** "The amicable slippage carries a μ₆-equivariant channel detectable at sextant
resolution" is falsified by `T₄` null at `K = 4×10⁵` **with the plant fired at `ε* ≤ 0.4%`** —
falsified *at that resolution and that quantisation*, which is the whole of what the sentence claims.

---

## 5. CROSS-ARM RULES (binding on all four)

1. **Ordering.** For ARMs 2 and 4, the null ensemble and the plant sweep are computed, written to
   disk and hashed **before** the primary statistic touches real curve data; the real-data script
   asserts the hash. For ARMs 1 and 3, the plant must be recovered before the census is run.
2. **Frozen scope lists.** The curve lists in §1.3, §2.6 and §3.3 were computed at spec-writing time
   and are frozen. **No curve may be added or removed.** A curve that fails to compute is reported by
   name with its error; the result is reported both with and without it.
3. **Forced hits count zero.** Each arm carries an explicit forced ledger
   (§1.3, §2.0, §3.2, §4.2). Denominators are unforced-cell counts:
   **ARM 1 = 16 / 37**, **ARM 3 = 1464**, **ARM 4 = 17 real df of 36 isotypes (5 in the primary)**.
   A tally stated against a larger denominator is a deviation.
4. **Controls must fire.** A non-firing plant voids its arm and the arm reports "uninformative
   instrument", never a bound. A null that breaks a symmetry the readout has by definition voids its
   arm (plain shuffles are excluded by name in ARMs 3 and 4).
5. **No magnitude becomes a verdict.** The words `safe`, `generic`, `nothing here`, `closed`, `no
   structure`, `benign`, `at the floor`, `tautological` are **banned from every result document
   produced under this spec** as characterisations of an outcome. Every bound is written as
   `< X at n = N, scope S, estimator E, null U, plant fired at ε*`.
6. **Abstention is legitimate.** An arm may end in "instrument uninformative" or "not testable at this
   scale". **That is not a closure of the underlying frontier**, and the frontier's status line is
   unchanged by it.
7. **Out-of-sample before naming.** Any positive on DISCOVERY is retested on the pre-frozen HOLDOUT
   before it is named. A discovery that fails HOLDOUT is recorded as a dropped chance pattern.
8. **Deviations file is mandatory** if any element of this spec changes, including `B`, `K`, `α`, the
   curve lists, the estimator, or the outcome mapping.

## 6. GRADES AVAILABLE TO EACH ARM

| arm | best available grade | what it may never be graded |
|---|---|---|
| 1 | `[MEASURED-EXACT, 53/53 unforced cells, p ≤ 97]` (+`[DERIVED]` for the `dim H¹` check) | `[PROVED]` — the arm proves nothing `p`-uniformly; and no statement about `p ≈ 2²⁵⁶` |
| 2 | `[MEASURED, bound with power+scope, control fired]` or `[MEASURED, coupling located in subspace X, OOS-reproduced]` | `[PROVED]`; and no `p`-scale extrapolation from the `α` fit |
| 3 | `[MEASURED-EXACT, 1464 unforced cells, m ≤ 400, flap indicator]` | any transfer to secp — **DC5 forbids it, whatever the outcome** |
| 4 | `[MEASURED, secp256k1 full scale, bound or coupling with power+scope]` | `[leakage]`, `[key recovery]`, or any ECDLP consequence |

**Nothing in this battery, at any outcome, constitutes an ECDLP result.**
