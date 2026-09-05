# PRE-REGISTRATION — Cheap DLP-free invariants of Q_d = S([d]G) ∈ A_new(F_p): partial-d information beyond the orbit label

**Status:** FROZEN pre-registration. Written BEFORE any Q_d datum at any prime is computed.
**Frozen date:** 2026-08-22
**Author:** kellytmunroe@gmail.com (via experiment-designer, context-isolated spec)
**Supersedes / relates to:** frontier N14 in `POSITIVE_FINDINGS_MASTER_v12.md`
("Partial-d info in the isotypic trace ℓ(d) beyond the orbit label"), which was
graded `[PROVISIONAL]` at p=43 / 15 points and blocked from scaling ("Singular
wedges above"). This spec pre-registers the DIRECT-INVARIANT (dlog-free) form.

**Grade contract:** every number produced under this spec inherits its SCOPE (the
prime it came from) and may never be stated without it. No grade promotion is
authorized by this run while any owed slot in the SELF-AUDIT remains open.

---

## 0. Decision-integrity preamble (why ordering is the mechanism)

Everything that could be chosen after seeing data is frozen in THIS file and
nowhere else: the single verdict statistic `T`, the decoder (frozen MAP on a
train split), the null (exact permutation, `K`, `α`), the invariant menu `F`, the
modulus set `M(n)` (a deterministic function of the public curve order `n`), the
prime ladder, the sample sizes `N_p`, and the three controls with their required
firing/null behaviour. A positive cannot be manufactured by picking a lucky
`(f,m)` post hoc (menu frozen; significance additionally requires SURVIVING the
matched control AND replicating on ≥2 primes AND being out-of-sample). A null
cannot be laundered into a find by adding an invariant or modulus after the fact
(both sets frozen). Neither verdict is reachable by reframing.

---

## 1. OBJECT

- Curve `E : y² = x³ + B` over `F_p`, `p ≡ 7 (mod 12)` (i.e. `p ≡ 3 mod 4` and
  `p ≡ 1 mod 3`), `j(E)=0`. `n = #E(F_p)` PRIME; `G` a fixed generator.
- `d ∈ (Z/n)*` the discrete log of a public point `[d]G`.
- Cover `C : w⁴ = x³ + B`, genus 3; `Jac(C) ~ E × A_new`, `dim A_new = 2`,
  `A_new` has CM by `Q(ζ₁₂)` and is supersingular at these `p` (embedding degree 3).
- Map `S : E(F_p) → A_new(F_p)`: take ONE (non-Galois-closed) 4th-root preimage of
  the C-point over the E-point, project to the `A_new` isotypic component.
  `Hom(E, A_new) = 0`, so `S` is NON-homomorphic. Established covariance:
  writing `ℓ(d) = dlog_{A_new}(S([d]G))`, `ℓ(λd) = k·ℓ(d)` with `k = p²`,
  `k² + k + 1 ≡ 0 (mod ord)`, `λ` = the GLV cube-root-of-unity multiplier on `Z/n`.
  Call this the ORBIT LABEL: it partitions `(Z/n)*` into λ-orbits `{d, λd, λ²d}`,
  worth `log₂ 3 ≈ 1.585` bits, and it is a KNOWN structural fact — not what we test.
- **Object under test:** whether a CHEAPLY COMPUTABLE (no `A_new` dlog) invariant
  `f` of the POINT `Q_d := S([d]G)` carries information about `d` BEYOND the orbit
  label — specifically partial / mod-small / distributional information.

**Tautology check (disjoint construction).** The feature is a function of the
POINT `Q_d`'s coordinates; the target is a function of the SCALAR `d` (its residue
`d mod m`). They meet ONLY through the pipeline `d → [d]G → S → Q_d → f` whose
leakage is exactly the hypothesis. `f` is never computed from `d mod m`. This is
NOT the forbidden `r = v−w` vs `w` tautology (feature built from target); it is a
legitimate leakage test with disjoint feature/target construction.

---

## 2. STATISTIC (exactly one verdict statistic)

**`T(p, f, m)` = out-of-sample MAP-recovery count of `d mod m` from `f(Q_d)`.**
An integer. This is the SOLE statistic that can trigger either verdict.

Protocol at each ladder prime `p`:
1. Fix `E` (smallest `B>0` with `n=#E(F_p)` prime, `j=0`), `G`, `n`.
2. **Orbit-quotient the sample.** Draw `N_p` DISTINCT λ-orbits; from each take the
   canonical representative `d* = min{d, λd mod n, λ²d mod n}`. Use one rep per
   orbit so the KNOWN 3-fold covariance is NOT triple-counted as three independent
   leaks. (This is the operational meaning of "quotient out the orbit label.")
3. Compute `Q_{d*} = S([d*]G)` in the chosen realization (§ REALIZATION), then
   `f(Q_{d*})` for each `f` in the frozen menu `F` (§ below). No `A_new` dlog.
4. Split the `N_p` reps into TRAIN / TEST by a fixed permutation seeded by `p`
   (seed frozen = `p`), equal halves.
5. On TRAIN build the MAP decoder `g_{f,m}(a) = argmax_b #{train reps : f=a, d* mod m = b}`
   (ties broken by smallest `b`). Frozen after training.
6. On TEST: `T = #{test reps : g_{f,m}(f(Q_{d*})) = d* mod m}`.
7. **Null distribution of `T`:** EXACT PERMUTATION. Permute the TEST-set
   `d* mod m` labels `K = 9999` times; recompute `T` with the FROZEN decoder;
   `E = #{permutations : T_perm ≥ T_obs}`. p-value `= (1+E)/(1+K)` as an integer
   ratio. **The verdict is decided by the integer `E`, never a float threshold.**

Under H0 (`f` carries nothing about `d mod m` beyond what the sample marginal
gives), `T` is distributed as the permutation null centred at the `1/m` floor;
the permutation uses the OBSERVED marginal of `d* mod m`, so any marginal skew
from canonical-rep selection is absorbed exactly. Under H1, `T` exceeds the null.

**Invariant menu `F` (frozen, all DLP-free — read coordinates, never a full-group dlog):**
- `f1`: Legendre symbol of the trace-to-`F_p` (first `F_p`-coordinate) of
  `ζ_d = e(Q_d, R)`, `R` a fixed auxiliary point, `e` the degree-3 pairing.
- `f2`: Legendre symbol of the `F_{p³}`-norm `N(ζ_d) ∈ F_p*`.
- `f3`: (first `F_p`-coordinate of `ζ_d`) `mod ℓ₀`, `ℓ₀` = smallest prime `| #A_new(F_p)`.
- `f4`: subfield-membership class of `ζ_d` (is `ζ_d^{(p³−1)/(p−1)} = 1`? — a
  proper-subfield indicator), a small finite alphabet.
- `f5`: small-torsion projection label: `[cof]·Q_d ∈ A_new[ℓ₀]` read as an index in
  `{0..ℓ₀−1}` against a fixed `A_new[ℓ₀]` basis. `cof = #A_new(F_p)/ℓ₀`; the internal
  `ℓ₀`-torsion dlog is `O(ℓ₀)`, cheap and allowed — this is NOT the full-group dlog.
- `f6`: parity and sextant of the `C`-lift `w`-coordinate (`w mod 2`; sextant of `w`).

Each `f` returns an element of a small finite alphabet `A_f` (`|A_f| ≤ 12`).

**Modulus set `M(n)` (frozen function of the PUBLIC order `n`, computed before any Q_d):**
`M(n) = { m ∈ {2,5,7,11,13} : (λ mod m) ∉ {0,1} }  ∪  {smallest 2 primes >3 dividing n−1}`.
The `(λ mod m)∉{0,1}` guard keeps the λ-orbit acting non-trivially on `Z/m`, so the
orbit label alone cannot determine `d mod m`; any recovery is genuinely beyond-orbit.
`n` is a curve parameter, not data, so deriving `M(n)` is not post-hoc.

**Secondary diagnostic (NON-verdict):** a marginal-bias readout of the empirical
distribution of `f(Q_d)` vs the uniform-point expectation. This is REPORTED for
interpretation only and CANNOT by itself trigger either verdict. Rationale: a
marginal bias in `f` independent of `d` is a property of `S`'s image, not
`d`-leakage; letting it drive a verdict would be a post-hoc reframe. Explicitly
fenced off here so it cannot be promoted after the numbers land.

---

## 3. CONTROLS (all three specified; each must behave as stated or the run is UNINFORMATIVE)

### (i) MATCHED control — `S_closed` (same p, differs only in the tested bit)
Same `p, E, G, d*`-sample, same `C`, same `A_new`; replace the non-Galois-closed
4th-root preimage `S` by the GALOIS-AVERAGED preimage `S_closed`: sum the four
preimages `{w, −w, iw, −iw}` (`i=√−1 ∈ F_{p²}`) as a divisor on `C`, then project
to `A_new`. Because this factors through a homomorphism `E → A_new = 0`
(`Hom(E,A_new)=0`), the `A_new`-projection is forced trivial, so `Q^closed_d` is
`d`-independent (identity / fixed 4-torsion coset). **Required behaviour:** running
the identical statistic on `Q^closed_d` must return recovery WITHIN the null band
(no `(f,m)` with `E=0`) at every powered prime. It isolates the tested property
(the NON-closure) from any pipeline artifact. If `S_closed` FIRES, the apparent
signal is a pipeline artifact → that prime is UNINFORMATIVE.
*(Secondary matched comparison, reported not gating: a `j=0` curve at `p' ≡ 11 mod 12`
where `E` is supersingular and the `A_new` split degenerates.)*

### (ii) FIRING PLANT — `f_plant` (positive control calibrating power)
Synthetic invariant built from `d`: `f_plant(Q_d) := (d mod m)` with each label
independently corrupted (replaced by a frozen-PRNG uniform label) with probability
`(1−π)`. Corruption is exact-integer: draw integer `u ∈ [0, D)` from a keyed PRNG,
corrupt iff `u < ⌊(1−π)·D⌋` (threshold precomputed as an integer; `π` is a design
constant, not data). Sweep `π ∈ {1, 1/2, 1/4, 1/8, 1/16, 0}`. The pipeline
(train MAP on corrupted TRAIN, evaluate on TEST) MUST detect `f_plant` (`E=0`,
p<1e-4) for all `π` above the power floor, and MUST NOT detect at `π=0`. The
smallest `π` reliably detected = the achieved detection floor (the analogue of the
prior POSCTRL that fired 0/15 while the real detector sat inconsistent 15/15).
**If the plant does not fire at achievable `N`, the null is uninformative — full stop.**

### (iii) COLLAPSE NULL — full-pipeline shuffle (calibrates false-positive rate)
Permute the `Q_d ↔ d` association across the sample BEFORE computing the target,
then run the ENTIRE train/test/decoder/permutation pipeline. Required: recovery at
floor (no significant `E`) for all `f, m`. If the collapse null shows spurious
significance the whole pipeline is miscalibrated → fix before trusting any positive.
(This checks the end-to-end pipeline, a superset of the internal permutation null.)

---

## 4. POWER

**Ladder** (`p ≡ 7 mod 12`, prime-order `j=0` curve confirmed per `p` by search over `B`):
`p ∈ {43, 79, 127, 163, 199, 211, 283, 331, 439, 499}` for VALIDATION, extended to
`p ∈ {~3011, ~6007, ~10007-class}` for POWERED tests. Target ≥ 6 primes total,
reaching as high as the realization runs (see SELF-AUDIT owed slot).

**Sample cap.** Orbit-dedup caps usable reps at `N_p ≤ (n−1)/3`. Hence:
- Small primes `p ∈ [43, 499]`: `N_p ≈ 14…166`. **UNDERPOWERED for m>2** — these
  rows are VALIDATION ONLY (reproduce N14 at p=43; cross-check realizations;
  confirm plant/collapse/matched behaviour). They CANNOT beat the anti-pattern.
- Powered rows require `n ≳ 3000` so `N_p ≳ 1000`, `N_test ≳ 500`.

**Detection floor** (permutation p<0.01; recovery excess `δ` over the `1/m` floor
detectable when `δ ≳ 2.58·√((1/m)(1−1/m)/N_test)`):

| m | floor 1/m | N_test=500 → δ_min | N_test=2000 → δ_min | ≈ bits floor (N_test=500) |
|---|-----------|--------------------|---------------------|---------------------------|
| 2 | 0.500     | 0.058              | 0.029               | ~0.010 bit                |
| 5 | 0.200     | 0.046              | 0.023               | ~0.0076 bit               |
| 7 | 0.143     | 0.040              | 0.020               | ~0.0066 bit               |
| 11| 0.091     | 0.033              | 0.017               | ~0.0055 bit               |

A full partial-leak (recovery → 1) or a "which-of-3" orbit-resolution (an extra
`log₂3` bits) is detected at `N_test` as small as ~50. The design therefore spans
from near-total leak down to ~0.007 bit at `N_test=500`.

**Anti-pattern beaten (explicit).** Prior scope was `N=15` at `p=43`: at `m=5`,
`N_test≈7`, `δ_min ≈ 0.38` — blind to anything short of a near-total leak. This
design at `N_test=500` sees `δ ≈ 0.046` (a ~50× tighter effect-size floor). The
"15 points" floor is the anti-pattern this spec is built to beat; the POWERED
verdict is defined only on rows with `N_test ≥ 500`.

---

## 5. SCOPE (banner — governs every number this run emits)

This is a SMALL/MID-`p` STRUCTURAL test of whether the covariant `S` carries
`d`-information beyond the orbit label AS AN ARITHMETIC FACT, over the invariant
menu `F` and moduli `M(n)`, on the stated prime ladder. It makes NO claim at
`p ≈ 2²⁵⁶`. The scale banner governs: for secp `ord_n(p) = (n−1)/6 ≈ 254 bits`,
and the pairing/MOV second hop is PROVED dead as an attack (constraint #1); this
spec reads cheap invariants directly and never proposes an MOV/pairing recovery of
`d`. A structural find here is a LEVER CANDIDATE, not an attack, and would require
a separate dlog-free exploitation argument that this spec does not supply.

---

## 6. FALSIFICATION / DECISION RULE (pre-committed both ways; neither reachable by reframing)

**Preconditions for ANY verdict** (else = UNINFORMATIVE at that scope; owed better
realization / larger `N`; NOT a closure and NOT a find):
- FIRING PLANT fired at `π ≥ π_floor` on ≥2 powered primes (power confirmed), AND
- COLLAPSE NULL at floor on all powered primes (FP rate calibrated), AND
- MATCHED `S_closed` at floor on all powered primes (artifact excluded).

**Outcome A — LEVER LIVES.** On ≥2 distinct POWERED primes (`N_test ≥ 500`),
∃ `f∈F`, `m∈M(n)` with out-of-sample recovery giving `E=0` at `K=9999`
(`p < 1e-4`) AND the matched `S_closed` control at that `(p,f,m)` is null
(`E/K > 0.01`) AND collapse null at floor.
→ CONCLUSION: "Cheap DLP-free invariant `f` of `Q_d` carries partial
`d`-information (`d mod m`) beyond the orbit label, at scope [ladder reached].
Lever lives." Report the specific `(f, m, recovery rate, bits)` — each WITH its
prime (SCOPE) and its `N_test` detection floor (POWER). NEXT PROBE (named now):
does recovery compose across `m` via CRT toward a search-space reduction; which
`f` and what symmetry-type / coordinate the leak lives in; push the realization
higher.

**Outcome B — NO INFORMATION (bounded closure at the counter-prior's bar).**
Preconditions met AND across ALL powered primes, ALL `f∈F`, ALL `m∈M(n)`, every
out-of-sample recovery sits within the null band (no `E=0` that also survives the
matched control).
→ CLOSURE, graded at the PROVED bar per the counter-prior:
  - OBJECT = { cheap DLP-free point invariants in menu `F` of `Q_d=S([d]G) ∈ A_new(F_p)` };
  - CLASS closed = { out-of-sample MAP recovery of `d mod m`, `m∈M(n)` — i.e.
    first-order partial / mod-small / distributional `d`-information readable
    WITHOUT the `A_new` dlog };
  - POWER = detection floor `Δ_min` achieved = [smallest `δ`/bits from §4] at
    `N_test = [value]`, per prime;
  - SCOPE = prime ladder `{p reached}`, `p≡7 mod 12`, prime-order `j=0` curves.
  - EXPLICITLY NOT CLOSED (a bound is a size, not "no structure"): higher-order or
    JOINT invariants; invariants outside `F`; moduli outside `M(n)`; cross-`d`
    joint distinguishers; anything at `p≈2²⁵⁶`. If the `d`-information lives in a
    subspace/joint statistic this design does not project onto, Outcome B returns
    "no information" while the structure persists there — so the null is bounded to
    `F` and first-order, and higher-order/joint invariants are the pre-committed
    NEXT PROBE even under Outcome B.

**Anti-reframe.** Outcome B cannot be upgraded to A by adding an `f`/`m` post hoc
(both frozen). Outcome A cannot be manufactured by a lucky `(f,m)`: significance
requires surviving the matched `S_closed` control AND replicating on ≥2 primes AND
being out-of-sample under a frozen decoder.

---

## 7. EXACTNESS / FLOAT RULE

All signal-path arithmetic is exact: `F_p, F_{p²}, F_{p³}` as integer tuples mod
`p`; Legendre via integer `pow(a,(p−1)//2,p)`; lift via Tonelli (integer); counts,
MAP decoder, and permutation exceedance counts all integer; p-values reported as
the integer ratio `(1+E)/(1+K)`. **No float decides any verdict.** Any effect size
printed as a float is DISPLAY-ONLY and is ranked against the integer permutation
null (the CLAUDE.md analytic-size carve-out: no key in the path). `check_no_float.sh`
MUST pass on the run script before execution.

---

## REALIZATION (named concretely; the p=43-hang confronted head-on)

**R1 — PRIMARY (small/mid p): supersingular MOV embedding into `F_{p³}*`, hand-rolled.**
`A_new` is supersingular with embedding degree 3 (established). Realize
`A_new(F_p)` via a FIXED pairing `e(·, R) : A_new(F_p) ↪ F_{p³}*`. Compute
`S([d]G)` by: (a) 4th-root-lift `[d]G` to `C` (Tonelli for `w²=±y`); (b) project
the `C`-divisor to the `A_new` isotypic component; (c) embed to `F_{p³}*` and read
cheap invariants as `F_p`-coordinate functions. Arithmetic is `F_p`/`F_{p³}`
integer tuples ONLY — it does NOT invoke Sage's function-field Jacobian, so it does
NOT hit the p=43 hang. The `A_new` / `F_{p³}` dlog is NEVER computed (that is the
forbidden MOV attack step and it is dead at scale anyway, constraint #1); we read
coordinates, not logs.

**R3 — CROSS-VALIDATION ONLY (p=43): Sage function-field `Jac(C)`.** Known to hang
above p=43; used solely to confirm R1 reproduces the N14 `ℓ(d)` object at p=43. It
is NOT the scaling engine.

**R2 — FALLBACK (owed): explicit genus-2 hyperelliptic model of `A_new` + Mumford.**
No such explicit model is on disk; if found it gives Mumford-`u`-polynomial
coordinates as the cheap invariants. Marked owed.

**The run uses R1**, validated against R3 at p=43. Largest `p` with a real compute
budget: reported by the run; the powered ladder targets `p ≳ 3000`. Whether R1
runs at `p ≳ 3000` is the primary OWED slot below.

---

## SELF-AUDIT — sections of THIS spec I could not fully cover (absence from this list is NOT clearance)

1. **REALIZABILITY ABOVE p=43 — OWED (largest gap; mechanical + frame).** R1 is
   demonstrated only at p=43 (reproducing N14). Its scaling to `p ≳ 3000` — required
   for EVERY powered row and thus for either verdict A/B — is NOT yet shown; step (b)
   (isotypic projection) must be reimplemented off Sage's function-field Jacobian and
   shown to run. Until then the POWERED decision rule is INERT and the spec can execute
   only its UNDERPOWERED validation rows. Owed; attempted date to be recorded on run.
2. **FAITHFULNESS OF THE `F_{p³}` INVARIANT READ — OWED (mechanical).** The claim that
   the pairing embedding is injective on the relevant `A_new(F_p)` subgroup (so distinct
   `Q_d` give distinct `ζ_d`, i.e. `f` retains resolution) is asserted from embedding
   degree 3; must be smoke-checked at p=43. If it collapses resolution, `f1–f4` lose power.
3. **MATCHED-CONTROL ADEQUACY — PARTLY OWED (frame; self-audit CANNOT discharge).**
   `S_closed`'s triviality rests on `Hom(E,A_new)=0` forcing the Galois-closed
   `A_new`-projection to 0. This is a PREDICTION the run verifies, not a proven input;
   if `S_closed` is not identically trivial, the matched null band must be re-derived.
   Per CLAUDE.md §2a this frame item needs isolation, which a self-audit does not provide.
4. **`M(n)` NON-EMPTINESS PER PRIME — OWED (mechanical).** The `(λ mod m)∉{0,1}` guard
   plus `n`-dependence could empty `M(n)` for some ladder prime; verify `M(n)≠∅` before
   counting a prime as powered.
5. **SCALE-BANNER GAP — DISCLOSED, NOT COVERED (scope/frame).** A "lever lives" at
   `p~10⁴` says nothing at `p=2²⁵⁶`; the dlog second hop is dead at scale. A find here is
   a lever candidate needing a separate dlog-free exploitation argument this spec omits.
6. **INVARIANT-MENU COMPLETENESS / SUBSPACE GUARD — DISCLOSED, NOT COVERED (frame).**
   `F` is finite and first-order. If `d`-information lives in a joint/higher-order
   invariant or a coordinate outside `F`, Outcome B returns "no information" while the
   structure persists in an unprojected subspace. The Outcome-B null is therefore bounded
   to `F` and first-order, and higher-order/joint invariants are the named next probe.

**Layer tags per CLAUDE.md §2a:** slots 1,2,4 are MECHANICAL (a run/smoke-check can
discharge them, with the artifact). Slots 1(frame part),3,5,6 are FRAME — isolation is
the mechanism and a self-audit cannot clear them; they are disclosed as owed/open.
