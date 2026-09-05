# PRE-REGISTRATION — Flap (Eisenstein/Dedekind μ₆ class): GROUP-LAW transition dependence

**Status: SPEC ONLY. FROZEN before any transition/chain data is seen. Decidable artifact.**
**Date 2026-07-21. Designed by the context-isolated `experiment-designer` agent; reviewed and persisted.**
Implementation target: `flap_grouplaw_transition_v1.py`. Origin: user draft "ε Carry-Trajectory
(Flap-Spill)"; re-scoped to the curve-side group-law object (item ②), corrections folded in.

---

## 0. OBJECT

- **Curve.** secp256k1 `E:y²=x³+7` over `p=2²⁵⁶−2³²−977`; order `N_ord` (`N_ord<p`, `3|N_ord`); `G`.
  CM by `ℤ[ω]`; GLV `φ(x,y)=(βx,y)`, `β³≡1 mod p`. `p≡3 mod4`, `6|p−1` (ρ exists).
- **Flap classifier ε (exact integer).** ρ primitive 6th root (`ρ²−ρ+1≡0`, e.g. `ρ=β+1`), fixed `a`
  from the established classifier. For field elt `X`: `s=(aX)%p`; `ε(X)=FLAP(1) ⟺ cent(s)−cent((ρs)%p)
  > p/2`, else `CORE(0)`; `cent(u)=u₀−p·(u₀>(p−1)//2)`, `u₀=u%p`. `>p/2 ⟺ ≥(p+1)//2` (exact). For a
  point `P`: `ε(P):=ε(X_P)`.
- **Established facts (ARM-0 gates, given):** `CORE:FLAP=3:1` (¼ flap); `ε(βX)=ε(X)`, `ε(−X)=ε(X)`
  (μ₆-invariant); `ε⊥` all multiplicative characters.
- **Property under test.** Does the GROUP LAW induce dependence between flap-states of arithmetically-
  related points beyond independent ¼-Bernoulli / a matched random-point sequence? Maps: doubling
  `X↦x(2P)`; addition `(P,Q)↦P⊕Q`.
- **Tautology check.** Feature `ε(X)`, target `ε(R(X))`, same classifier on two arguments linked only by
  the group-law map `R`. Neither is a sub-construction of the other ⇒ disjoint ⇒ NOT tautological.
- **Not-forced check.** `ε(2P)=ε(P)` forced only if `2P∈{±P,±ωP,±ω²P}` ⇒ `2≡unit mod N_ord`; `2` is not
  a `ℤ[ω]` unit ⇒ fails except the `≤2` 3-torsion abscissas (`3|N_ord`), which are **guard-excluded**.
- **Baselines.** `2` invertible mod `N_ord` ⇒ `P↦2P` bijection ⇒ `ε(2P)` is ¼-Bernoulli (same marginal);
  `Q↦P⊕Q` bijection ⇒ `ε(P⊕Q)` ¼-Bernoulli. Every null = independence with margins at the real ¼.

---

## 1. STATISTICS (1-bit ε readout; all primaries are single 1-df quantities)

- **T1 — doubling 2×2 (PRIMARY/HEADLINE).** `n` uniform random valid abscissas `X_i`; tally
  `n_ab=#{ε(X_i)=a, ε(x(2P_i))=b}`. **Fisher exact two-sided** (1 df, exact rational p). Characterize:
  `P(F|F)=n_FF/(n_FF+n_FC)` vs ¼; log-odds `θ` and its **SIGN** (`+`=Flap→Flap resonance, `−`=anti;
  both structure).
- **T2 — addition `N_FFF` (SECONDARY targeted).** `n` random pairs `(P_i,Q_i)` (guard `P≠±Q`), `R=P⊕Q`;
  `N_FFF=#{ε(P)=ε(Q)=ε(R)=F}`; null `n/64`; one-sided upper, integer rank vs Control-B.
- **T3 — addition 4×2 omnibus (SECONDARY).** predictor `(ε(P),ε(Q))∈{CC,CF,FC,FF}`, response `ε(R)`;
  `G²` (3 df), integer rank vs Control-B permutation null (log = named carve-out §5).
- **T4 — chain doubling stratum `b_i=0` (CHARACTERIZATION).** Along double-and-add of random `d`, pool
  `(ε(A_i),ε(A_{i+1}))` over pure-doubling steps into a 2×2; Fisher two-sided. Fixed map (`2×`) ⇒ pure
  group-law. Per-chain block cross-check (§2).
- **T5 — chain double-add stratum `b_i=1` (CHARACTERIZATION).** Same for the fixed map `A↦2A⊕G`.

### 1a. DISCARDED (named)
- **D1** transition-matrix deviation from analytic stationary `[[¾,¼],[¾,¼]]` — Markov-trivial null
  (rows identical); zero-power/wrong-null. Retained only ranked vs matched null, not vs the analytic matrix.
- **D2** Flap→Flap resonance tied to equal-bit RUNS in `d` — chain defined by `d`'s bits ⇒ recompute-fn-of-
  bits-vs-bits (tautology) / read `d`'s bits (generation-side). DISCARD; de-tautologized content = T4/T5
  (fixed map per stratum).
- **D3** recover bit `b_i` from `ε(A_i)` — generation-side; apparent recovery = "chain defined by `d`". DISCARD.
- **D4** pooled chain transition matrix WITHOUT bit-stratification — `d`'s bit composition drives the pooled
  off-diagonal (re-imports D2). DISCARD → T4/T5.
- **D5** max-over-lag / max-over-run-length score — upward-biased, low-power. DISCARD → single pooled Fisher.
- **D6** single-point chain flap-density vs ¼ — first-moment marginal (floored, guaranteed ¼). DISCARD.

**T1–T3 primary over T4–T5:** uniform independent points (clean, `n=10⁶`), one fixed map, zero `d`.

---

## 2. ARMS & CONTROLS

- **ARM 0 (GATE)** — deterministic pass/fail (§3), aborts on fail.
- **ARM 1 (doubling, PRIMARY)** — T1.  **ARM 2 (addition)** — T2+T3.  **ARM 3 (chain, char.)** — T4+T5.

**MATCHED NULLS.**
- **Control B (KEY).** Pure arms: replace group-law image by an INDEPENDENT uniform point (T1: `R⊥P`;
  T2/T3: `R⊥(P,Q)`). PRESERVES all ¼ margins, `ε` + its μ₆-invariance (real `ε` both arms — no
  μ₆-mismatch artifact), `n`. DESTROYS only the arithmetic link. `B=9999`, `seed=20260721`. (For T1 this
  is exactly Fisher's conditional null; Fisher = primary p, Control B = cross-check.) Chain arms:
  within-chain label permutation (PRESERVES sequence/counts/autocorr, DESTROYS serial order), `B=9999`.
- **Control A (chain only).** Random `d'` matched on bit-length `L` + Hamming weight `w`. PRESERVES `L,w`,
  chain, group law; DESTROYS the bit PATTERN. Target typical of Control-A ⇒ generic group-law; atypical ⇒
  `d`-pattern-specific ⇒ route to D2 (discount as tautological/generation-side).
- **Per-chain block guard.** T4/T5 p-value over `T` chains as independent replicates, not pooled steps.

**PLANTED POSITIVES (must fire or arm VOID).**
- **PC-max (μ₆ forced-equal, exact).** Same tally with map `P↦φ(P)` (`x(φP)=βX`); `ε(βX)=ε(X)` ⇒ forced
  diagonal ⇒ Fisher/`G²` at floor. VOID gate.
- **PC-α (tunable power).** Independence background + inject `m=⌊αn⌋` forced-equal `(ε(P),ε(φP))` pairs;
  `δ=P(F|F)−¼=3α/4`; sweep `α∈{0}∪{2^{−k}:k=1..10}`; smallest firing `α` (power ≥0.8, 100 reps) =
  threshold, must match analytic `δ_min`.
- **Disclosed power limit:** no cheap curve-native distinct-`x` weak-correlation plant; PC plants via exact
  μ₆ ⇒ calibrates `δ_min`, does not exercise distinct-`x` weak coupling (design boundary).

---

## 3. POWER

**ARM 0 gate (abort condition).** Fixed set: first `n_g=2²⁰` valid abscissas from `random.Random(20260721)`
(accept iff `pow((X³+7)%p,(p−1)//2,p)==1`). PASS requires ALL: (1) `check_no_float.sh` passes; (2)
μ₆-invariance ZERO exceptions: `ε(X)==ε(βX%p)==ε(β²X%p)==ε((p−X)%p)` ∀ gate `X`; (3) ¼-density
`|4·n_flap−n_g| ≤ 6·isqrt(3·n_g)`. Any fail ⇒ halt, no verdict.

**Detectable effect (2×2 at `π₀=1/16`):** `Δ_min=(z_{α*/2}+z_β)√(π₀(1−π₀)/n)`, `α*=1/120`
(`z=2.638`), power .8 (`z_β=.842`), `√(π₀(1−π₀))=√15/16`:
- **T1 `n=10⁶`:** `Δ_min≈8.4×10⁻⁴`, `δ_min=4Δ_min≈3.4×10⁻³` (`P(F|F): .250→~.2534`), `α_min≈4.5×10⁻³`.
- **T1 `n=10⁷`:** `δ_min≈1.1×10⁻³`.
- **T2 `n=10⁶`** (`π₀=1/64`, 1-sided): `Δ_min≈4.0×10⁻⁴`.
- **T4/T5** per-stratum `~1.28×10⁵` pairs: block-corrected `δ_min≈1%`, power .8 (weaker by design).

**Bonferroni family (counted now):** 6 cells `{T1@10⁶ HEADLINE, T1@10⁷, T2@10⁶, T3@10⁶, T4@T=1000,
T5@T=1000}` ⇒ `α*=0.05/6=1/120`. `B=9999` ⇒ min MC `p=10⁻⁴<α*`. PRIMARY = **T1 @ n=10⁶** (single; rest
secondary characterization, NOT max-over-cells). Control-A/B comparisons interpretive.

---

## 4. SCOPE & PARAMETERS

- Curve secp256k1 full-scale; `ε` params `(a,ρ,β)` fixed from established classifier.
- ARM 1: `n=10⁶` primary, `10⁷` secondary; uniform valid abscissas (seed 20260721 + QR filter); guards
  skip `≤2` 3-torsion abscissas and any `X` with `x(2P)=X`.
- ARM 2: `n=10⁶` independent pairs (guard `P≠±Q`).
- ARM 3: `T=1000` random `d`, `L=256`; Control A 100 matched-`(L,w)` per target (or shared pool 1000).
- `B=9999`. Fixed: curve, `G`, `(a,ρ,β)`, seed, `n_g=2²⁰`, `k=6`, family 6, `α*=1/120`. Varies: arm, `n`, `d`.
- **Untested readouts (null scoped to 1-bit ε ONLY):** (i) full rhombus/Dedekind position; (ii) `ν_π` /
  lattice class; (iii) higher iterates `2^k P` (k≥2), `mP` (m>2); (iv) `≥3`-point joints
  `(ε(P),ε(2P),ε(3P),…)`; (v) ε coupled to `y`. Not excluded by a null here.
- Compute: ARM 1 `n=10⁶` ≈ minutes; `10⁷` ≈ ~10 min; ARM 3 seconds. Bounded.

---

## 5. EXACTNESS

All signal-path `int`: `cent`, ε threshold `≥(p+1)//2`, QR `pow(...,(p−1)//2,p)`, doubling
`X2=((pow(X,4,p)−56·X)·pow(4·((X³+7)%p)%p, p−2, p))%p`, `φ`-image `(βX)%p`, `y=pow((X³+7)%p,(p+1)//4,p)`,
addition via one `pow(x_Q−x_P,p−2,p)`. Counts integer. **Banned:** `/`,`float`,`round`,`**0.5`,`math.*`,
`np.*` on any key/coord/feature. `check_no_float.sh` (ARM-0 gate). p-values: T1/T4/T5 Fisher exact via
`math.comb` (exact rational, compared to `1/120` by integer cross-mult); T2 exact tail (int); Control-B
rank `(1+#{b:stat_b≥stat_obs})/(B+1)`. **Named carve-out:** T3 `G²` `log` = monotone statistic ranked vs
integer permutation null only (matches the repo MI/z carve-out); no coord/key/classifier input is float.

---

## 6. DECISION RULE + PRE-COMMITTED OUTCOME TABLE

**Rule.** exact integer statistic; `p`=Fisher rational (T1/T4/T5) or integer rank (T2/T3). **FIRES ⟺
`p≤α*=1/120` AND that arm's PC-max fired.** VOID: PC-max fails ⇒ halt that arm. Report `{magnitude,
δ_min-power, scope}`; never "closed."

| Arm/test | Outcome | Pre-committed conclusion |
|---|---|---|
| **T1 doubling (HEADLINE)** | FIRES (PC-max fired) | Doubling induces ε-dependence: report `P(F|F)` vs ¼, `θ` + SIGN (`+`=resonance / `−`=anti; both structure), magnitude+power (`δ_min≈3.4e−3@n=10⁶`)+scope. NEXT PROBE: stratify by lattice class/`ν_π`; test `ε(2^kP)`; name symmetry type; confirm `n=10⁷`, T4. |
| **T1 doubling** | NULL (PC-max fired, PC-α calibrated) | SCOPED BOUND: `|δ|<δ_min≈3.4e−3` (`P(F|F)` within ~.0034 of ¼) @ n=10⁶, power .8, secp256k1, uniform points. NOT "no structure": finer rhombus/`ν_π`/`2^kP`/≥3-point/`ε`–`y` (§4) NOT excluded (1-bit projection would read null if effect is in the full lattice position). NOT "avenue dead." |
| **T1 doubling** | VOID (PC-max failed) | Detector broken; debug; re-run. |
| **T2 `N_FFF`** | FIRES/NULL (PC-max fired) | FIRES ⇒ all-flap addition resonance (excess over `n/64`, sign, β-check before μ₃). NULL ⇒ bound `Δπ_FFF<4e−4@10⁶` + finer-readout caveat. |
| **T3 `G²`** | FIRES/NULL (PC-max fired) | FIRES ⇒ `ε(P⊕Q)` depends on `(ε(P),ε(Q))`; identify driving row. NULL ⇒ omnibus bound + caveat. |
| **T4 chain `b=0`** | FIRES/NULL (block; PC-max fired) | Replicates T1 on scrambled points. FIRES+Control-A-typical ⇒ generic group-law; +atypical ⇒ `d`-specific ⇒ D2 discount. NULL ⇒ bound `δ_min≈1%`. |
| **T5 chain `b=1`** | FIRES/NULL (block; PC-max fired) | As T4, map `A↦2A⊕G`. |
| **PC-max** | fires / not | fires ⇒ detector live (no leakage info); not ⇒ VOID that arm. |

---

## 7. FALSIFICATION

- **GROUP-LAW FLAP-DEPENDENCE PRESENT ⇔** T1 @ n=10⁶ FIRES (`p_Fisher≤1/120`) with PC-max fired. Output =
  characterization (sign of `θ`, `P(F|F)`, next probe), never "break."
- **NO DEPENDENCE IN 1-BIT READOUT AT TESTED POWER ⇔** T1 `p>1/120`, PC-max fired, PC-α calibrated;
  reported as scoped bound (`δ_min` `3.4e−3@10⁶` / `1.1e−3@10⁷`), §4 untested list, phrase *"group-law
  doubling induces no dependence in the 1-bit flap ε at this power; finer rhombus/`ν_π`/`2^kP`/≥3-point/
  `y`-coupled readouts not excluded"* — never "closed."
- **VOID ⇔** ARM 0 gate fails, OR any arm's PC-max fails.

---

**Load-bearing:** (1) ε is a 1-bit projection of the full Eisenstein/Dedekind position — a null bounds
that bit only (finer-coordinate escape written into every null). (2) The matched null applies the real
μ₆-invariant ε in both arms and only cuts the arithmetic link — no null-symmetry-mismatch artifact.
(3) Every non-bit-stratified chain statistic (D2/D4) is tautological/generation-side, discarded by name;
curve-side content survives only in the fixed-map strata T4/T5.
