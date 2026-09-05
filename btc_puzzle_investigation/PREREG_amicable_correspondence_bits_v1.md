# PREREG — Amicable-partner correspondence: bits about `d` beyond the `log₂6` Aut ceiling (v1)

**Date 2026-07-23. Written BEFORE any data from this experiment exists.** The only computations run at
spec time were (a) the *sample frame* enumeration in §6 and (b) the *power* arithmetic in §5. No test
statistic of §2 has been evaluated on any curve. Design scripts:
`/private/tmp/claude-501/-Users-trentpalelei-Desktop-Math-Ex/8768fbbd-6a94-4336-9780-bc5eb7ec9a3b/scratchpad/frame2.py`,
`.../pw.py`. Any deviation from this document goes in
`PREREG_amicable_correspondence_bits_v1_DEVIATIONS.md`, dated, with cause, before the affected data are read.

Inherited facts (verified against disk at spec time, not taken on trust):
`RESULT_secp_amicable_pair_v1.md` (F1), `RESULT_orbit_bit_ladder_v1.md` (F2),
`RESULT_d1_information_extraction_v1.md` + `RESULT_D1_lift_affine_test_v1.md` (F3),
`PREREG_localized_bit_extraction_v1_DEVIATIONS.md` D1 (the generator-swap trap).

---

## 1. OBJECT

**The object is the symmetry group of the scalar-space partition induced by a partner-side, `P`-only map.**

Setting. `E_b : y² = x³ + b` with `b = 7`, over `F_p`, `p ≡ 1 mod 3`, `p > 7`, `n := #E(F_p)` prime.
Then `Aut(E) = μ₆` and (verified over the whole §6 frame) `n ≡ 1 mod 6`, so `μ₆ ≤ (Z/n)^*` exists on the
scalar side. `Ẽ := E_7` reduced mod `n`, over the field `F_n`. The pair is **amicable** iff `#Ẽ(F_n) = p`
(F1: true at secp, at full 256-bit scale, exact).

Let `Φ` be a map from `E(F_p)∖{O}` to a finite label set, computed **only** from the integer coordinate
representatives `x, y ∈ [0,p)` of `P` and the public constants `(p, n, b=7)` and objects derived from them.
Enumerate the group as `P_j = [j]G`, `j = 1..n−1`, and write `Φ_j := Φ(P_j)`. The object is

> `Γ*(Φ) := { t ∈ (Z/n)^* : ∃ σ ∈ Σ_Φ such that Φ_{t·j} = σ(Φ_j) for all j }`,

a subgroup of `(Z/n)^*`, where `Σ_Φ` is a **pre-declared** group of label-set symmetries (§2, frozen).
`Γ*(Φ)` is exactly the group whose orbits are the fibres (or `σ`-twisted fibres) of `Φ` on the scalar
space. F2's ceiling is the statement `|Γ*| ≤ 6` for every `Aut`-quotient map. **The hypothesis under test
is `|Γ*(Φ)| > 6` for some partner-side `Φ`, replicating, and specific to amicability.**

**Why this and not mutual information.** `d ↦ P_d` is a bijection, so `I(feature; d)` is maximal
(`log₂ n`) for *any* injective feature — e.g. the raw `x`-coordinate. An MI/bit-count statistic on this
question is a **proxy that is tautologically saturated**, and it is the same shape as the recorded
`r = v − w` failure. `Γ*` is immune: an injective `Φ` has `Γ* = {1}`, not a large value.

**Two tautology boundaries, drawn now.**
- **(T1) The CM coordinate map is not available.** `cm_amicable_correspondence_v1.py` records
  `E(F_p) ≅ Z[ω]/(π_p − 1) ≅ F_n`, i.e. "the partner field IS the coordinate ring". The induced
  coordinate `φ(P) ∈ F_n` **is the discrete logarithm** — computing it *is* solving for `d`. Any feature
  built from `φ` smuggles `d` into the feature path. **`φ` is banned from `Φ`.** Consequently the *only*
  `d`-free partner-side constructions available are those built from the **integer representatives** of
  `P`'s coordinates reduced mod `n`, plus public constants. That non-canonicity (a representative choice,
  not a morphism) is exactly why no homomorphism exists (F4/F5) and is what makes the construction
  non-trivial rather than tautological.
- **(T2) Injective recodings are forced.** Any `Φ` that is injective as a function of `x(P)` has fibres
  `= {±d}` **by construction**, so `Γ* = μ₂` is forced and carries zero information. This is pre-declared
  per feature in §2 as `Γ*_forced`; only `|Γ*| / |Γ*_forced|` is counted (project rule: count only
  unforced hits).

**Disjoint construction (constraint 1) — satisfied structurally, not by convention.** `Γ*` quantifies over
all points and **never references `G` or `d`**. The index `j` is used only to enumerate the group in a
fixed order; `Φ` receives a *point*, never `j`. Moreover `Γ*` is **provably generator-invariant**: with
`G' = [s]G`, `P'_j = P_{sj}`, so `Φ'_{tj} = σΦ'_j ⟺ Φ_{t(sj)} = σΦ_{sj}`, and as `sj` ranges over all
residues this is the same condition. `(Z/n)^*` is abelian, so no conjugation term survives. Hence the
recorded trap `P_d^{[7]G} = P_{7d}^{G}` (`PREREG_localized_bit_extraction_v1_DEVIATIONS.md` D1) **cannot
contaminate the primary statistic**, and a generator swap is barred from use as a replicate (§3).

---

## 2. STATISTIC

**Primary (exactly one): `|Γ*(Φ)|`, an integer, reported with the group named** (order, a canonical
generator, and the associated `σ`'s). Its distribution under the null: for a label distribution with
collision probability `q = Σ_v (m_v/(n−1))²`, a fixed `t` of order `k` lies in `Γ*` by chance with
probability `≈ |Σ_Φ| · q^{(n−1)(1−1/k)}`, i.e. `< 2^{−(n−1)/4}` for every `n` in scope. **The exact arm's
false-positive rate is numerically zero and its power against an exact symmetry is 1** (full enumeration,
no sampling). Its blind spot is *approximate* symmetry — which is why §2b exists and is registered now.

**Validity gate (pre-declared, reported never silently applied): faithfulness.** `Φ` is *`Γ*`-faithful*
iff `|image(Φ)| = (n−1)/|Γ*(Φ)|` exactly. A non-faithful `Φ` collapses more than its symmetry group
explains (a constant map is the extreme). Every row reports `(|Γ*|, |image Φ|, faithful Y/N)` and the
**exact fibre-size multiset**. Non-faithful rows are reported, not dropped.

**Frozen feature list (4 hypothesis features + 1 degenerate control). No additions after this document.**
Write `x̄ = x mod n`, `ȳ = y mod n`, `δ = (ȳ² − x̄³ − 7) mod n`, `χ_n(·)` the quadratic character mod `n`.

| id | `Φ(P)` | `Σ_Φ` | `Γ*_forced` (analytic, pre-computed) |
|---|---|---|---|
| `ΦA` | `χ_n(x̄³ + 7) ∈ {−1,0,+1}` — does the reduced `x` land on `Ẽ(F_n)` or its quadratic twist | `{id}` | `μ₂` (`x`-only) |
| `ΦB` | `χ_n(δ) ∈ {−1,0,+1}` — quadratic character of the amicable defect | `{id}` | `{1}` (`y`-dependent; `y ↦ p−y` does not fix `ȳ`) |
| `ΦC` | `δ mod n` (the full defect) | `{id}` | `{1}` |
| `ΦD` | `±`-class of `e(P) := dlog_{G̃}(Q(P))` in `Ẽ(F_n)`, where `Q(P)` is the point with `X = x̄` and canonical `Y` (smaller representative), `⊥` on the twist branch | `{±1} × (Z/#Ẽ(F_n))^*`-multiplication | `μ₂` (`x`-only) — **and by T2 `Γ*(ΦD) = μ₂` is forced for the invariance part; the unforced content of `ΦD` is entirely in the `σ ≠ id` (equivariance) part** |
| `N0` | `ord(Q(P))` in `Ẽ(F_n)` | `{id}` | — **degenerate control**: on the amicable arm `#Ẽ(F_n) = p` is prime so `ord ≡ p` identically ⇒ `|image| = 1`, `Γ* = (Z/n)^*`. **This row must be caught by the faithfulness gate and must NOT be reported as a finding.** If it is reported as a finding, the pipeline is broken. |

`Q(P)` and `e(P)` are defined for every curve in scope; on non-amicable curves `#Ẽ(F_n)` need not be prime,
so `e` is the dlog in `⟨G̃⟩` when `Q ∈ ⟨G̃⟩` and `⊥` otherwise. `⊥` is a label value, not a discard; its
rate is reported per curve.

**2b. Registered secondary statistic (graded / subspace-escape).** Required by the rule that a bound may
not become a verdict: an effect could be an *approximate* rather than exact symmetry, invisible to `|Γ*|`.
Since `(Z/n)^*` is cyclic, for each divisor `k | (n−1)` with `k > 6` there is a unique subgroup `Γ_k`; let
`t_k` be its canonical generator (smallest residue generating `Γ_k`). Define

> `a(k) := #{ j : Φ_{t_k · j} = Φ_j }`,  `z(k) := (a(k) − (n−1)q) / sqrt((n−1)q(1−q))`,

with `q` computed exactly from `Φ`'s own image histogram. **Secondary statistic: `z_max := max_{k>6, k|(n−1)} z(k)`**,
with Holm correction across the (typically 4–35, see §6) divisor cells and an exact integer rank p-value
against the §3 matched null. Exact invariance under `Γ_k` is equivalent to invariance under `t_k`, so §2b
degrades continuously to §2. `z_max` is a max over a **small pre-declared cell set indexed by subgroups**,
not over all `n−1` elements; pooling over all `t` was rejected at design time because it dilutes a
single-subgroup effect (design calc: pooled `e_min ≈ 0.40` at `n = 2000` vs `0.10` for the subgroup form).

**α:** primary arm `α = 0.01` on the §3 contrast test; secondary arm `α = 0.01` Holm-corrected within
prime, then the §5 replication rule across primes. The two arms are reported separately and never merged.

---

## 3. MATCHED CONTROL

**M1 — modulus swap (the matched null for "the modulus is the curve order").** Recompute every feature
with `n` replaced by `n'`, a prime `≡ 1 mod 3` drawn from the 199 primes nearest `n` in that class,
excluding `n` itself and excluding any `n'` with `#E_7(F_{n'}) = p`. Everything else is byte-identical:
same `p`, same curve, same points, same enumeration, same `Φ` formula, same `Γ*`/`z_max` code.
- **Preserves:** the curve and all its points; the group order `n` on the scalar side; `μ₆` and every
  automorphism structure; the modulus size and residue class; each feature's forced symmetry `Γ*_forced`;
  the label alphabet and (to sampling error) the image histogram.
- **Destroys:** the identity `modulus = #E(F_p)` — i.e. the CM/amicable link between the field the feature
  reduces into and the curve it reduces from.
- **Explicitly NOT a shuffle.** No relabelling of points or scalars occurs, so M1 cannot destroy a
  symmetry the readout has by definition. This is the direct fix for the recorded "6–7σ soft shadow"
  null-mismatch failure: the μ₆ structure the readout has by construction survives M1 intact, and is
  therefore *not* what M1 tests.

**M2 — scalar relabel: registered as a NULL, barred as a replicate.** `Φ(P_{t·d})` paired against `d` is
exactly the generator swap `G → [t]G` (D1 identity, verified on disk). Under §1 the primary statistic is
provably invariant under this relabel, so M2 has no discriminating power here and is **not run as a
replicate**. Replication is **across primes only** (§5). Any future analysis that treats a generator swap
as an independent replicate is a deviation and must be logged.

**C — the amicability contrast (this is what attributes the effect).** M1 isolates "modulus = curve
order", which holds on amicable *and* non-amicable curves alike. It therefore **cannot** attribute
anything to amicability. Attribution comes from the matched contrast in §6: 21 amicable units vs 21
size-matched non-amicable units, same `b = 7`, same `p ≡ 1 mod 3`, same `n` prime, differing only in
whether `#Ẽ(F_n) = p`. Both arms are run through the identical pipeline including M1.

---

## 4. PLANTED CONTROL

**P1 — exact-arm plant (must fire, deterministically).** Pick `k | (n−1)`, `k > 6`, and its subgroup `Γ_k`.
Define `Φ^plant_k(P) := ` the lexicographically smallest `(X, Y)` over the orbit `{ [t]P : t ∈ Γ_k }`
(computable from `P` alone; uses `d` nowhere). Then `Γ*(Φ^plant_k) ⊇ Γ_k` **by construction**. The test
must return `|Γ*| ≥ k` and must return `Γ_k` by name. Ladder: run every `k | (n−1)` with `k > 6`, on every
curve in scope. **If any planted `k` is missed, the pipeline is broken and the entire null is
uninformative — reported as instrument failure, with no conclusion drawn about the hypothesis.**

**P2 — graded-arm plant with a measured `e_min` ladder (must fire).** For `ε ∈ {0.02, 0.05, 0.10, 0.20,
0.40, 0.80}`, define `Φ^ε_k(P) := Φ^plant_k(P)` for `P` in a pre-declared deterministic subset of density
`ε` (the `⌈ε(n−1)⌉` points of smallest `X`), and `Φ^ε_k(P) := ΦC(P)` otherwise. Report, per curve, the
smallest `ε` at which `z_max` clears the Holm-corrected `α = 0.01` threshold against M1. That measured
value **is** `e_min(n)` and every §9 null cell must quote it.
- The plant deliberately injects a known symmetry; it is a positive control, not a candidate feature, and
  it is built from `P` only (so it does not even require the `d`-side exemption).

**N0 — negative control (must NOT fire as a finding).** The degenerate row of §2. If `N0` is reported as
a beyond-ceiling finding, the faithfulness gate has failed and the run is void.

---

## 5. POWER

**Exact arm.** Full enumeration over all `d ∈ [1,n)` and all `t ∈ (Z/n)^*`: no sampling. Power against an
exact symmetry `Γ_k ⊋ μ₆` is **1**; false-positive probability `< 2^{−(n−1)/4}` (§2). The exact arm has
**zero power against approximate symmetry** — this is stated now, not discovered later, and is the reason
§2b is registered.

**Graded arm — design estimate `e_min ≈ z*/sqrt((n−1)(1−q)/q)` with `z* = 4.5`, `q = 1/2`** (superseded by
the measured P2 ladder wherever they disagree; the measured value governs):

| `n` | 79 | 967 | 2143 | 4243 | 6091 | 8863 | 13759 | 18793 | 19483 |
|---|---|---|---|---|---|---|---|---|---|
| design `e_min` | 0.51 | 0.145 | 0.097 | 0.069 | 0.058 | 0.048 | 0.038 | 0.033 | 0.032 |

`n = 79` (the smallest amicable unit) is power-starved and contributes to replication counting only; it
may not carry a bound on its own.

**Contrast arm — exact Fisher one-sided, 21 vs 21 matched units (computed at spec time, `pw.py`):**

| amicable arm fires | significant at `α = 0.01` iff non-amicable arm fires at most |
|---|---|
| 21/21 | 14/21 |
| 19/21 | 11/21 |
| 17/21 | 8/21 |
| 15/21 | 6/21 |
| 12/21 | 3/21 |

`21/21` vs `0/21` gives `p = 1.86 × 10⁻¹²`. The **minimum detectable rate difference** with a perfect
amicable arm is **0.33** at `α = 0.01`; a difference of `0.23` would need 30 matched pairs, which the
frame does not contain at `p < 20000`. Paired (McNemar, exact binomial) alternative: `b` discordant pairs
all favouring amicable gives `p = 2^{−b}`, so **`b ≥ 7` discordant pairs are required** to reach
`p < 0.01` on the paired test. **Any effect whose amicable-vs-non-amicable rate difference is below 0.33
is undetectable at this frame size, and §9 cell 8 (abstention) applies.**

---

## 6. SCOPE

Every number this run produces inherits the following and may not be quoted without it.

- **Curve:** `E_7 : y² = x³ + 7` (F1's curve, fixed; not a twist sweep). No other `b`.
- **Prime frame (enumerated at spec time, `frame2.py`; this is the *complete* frame, no selection):**
  `p` prime, `p ≡ 1 mod 3`, `11 ≤ p < 20000`, `p ≠ 7`, `n = #E_7(F_p)` prime, `n ≠ p`. This yields
  **42 amicable curves and 93 non-amicable curves**; observed amicable fraction `42/135 = 31%`, consistent
  with the recorded `~26%` density (F1 §2).
- **Independence unit.** Amicable curves come in 2-cycles: `(67,79)` and `(79,67)` are the same object.
  Units are **one curve per 2-cycle, the one with `p < n`** → **21 independent amicable units**:
  `p ∈ {67, 907, 1249, 2089, 2647, 3739, 4159, 4513, 5953, 6043, 6343, 7369, 8209, 8467, 8779, 12757,
  12919, 13567, 13933, 18541, 19471}`.
- **Matched non-amicable controls:** for each amicable unit, the qualifying non-amicable curve with `p`
  nearest (ties → smaller `p`), sampled without replacement in increasing order of the amicable `p`.
  → **21 matched pairs.** The remaining non-amicable curves form a pre-declared secondary unmatched arm
  (up to 93 units) reported separately.
- **Divisor cell counts** for §2b, per unit (`#{k | n−1 : k > 6}`): ranges **4 to 35** over the frame
  (e.g. `n=79`: 4; `n=6091`: 27; `n=18793`: 35). Holm is applied within unit over exactly these cells.
- **Generator:** canonical (smallest `x`, then smallest `y`) on both `E(F_p)` and `Ẽ(F_n)`. Primary
  statistic is generator-invariant by the §1 proof; `G̃` affects `ΦD` only up to the `Σ_ΦD` action, which
  absorbs it.
- **Scale honesty (constraint 7).** `p < 20000` is **under 14.3 bits**; secp is **256 bits**. This run
  spans none of that gap.
  - **F1 is exact at full scale.** Nothing here strengthens or weakens it.
  - **A positive result** (`Γ_k` named on a curve) is an **exact algebraic fact about that curve**:
    grade `[VERIFIED-INSTANCE]`, `p < 20000`. It becomes a claim about `E_7/F_p` in general, or about
    secp, **only by proof** — never by extrapolating the frame.
  - **A null result** is `[EMPIRICAL, scoped]`: bounded to these 4 features, this frame, and the measured
    `e_min` floor. It is not a statement about secp, not a statement about untested features, and per
    project rule **not a closure of the amicable channel**.
  - `ΦD` costs an `O(√p)` discrete log on the partner curve. It is feasible only inside this frame and
    **cannot** be evaluated at secp scale by anyone, including under a positive result.

---

## 7. FALSIFICATION

The hypothesis ("some `P`-only partner-side object carries `d`-information beyond `log₂6`, attributable to
amicability") is **abandoned** if all four hold:

1. `|Γ*(Φ)| = |Γ*_forced(Φ)|` for all 4 hypothesis features on all 21 amicable units (and, in `ΦD`'s case,
   no `σ ≠ id` equivariance beyond `Γ*_forced`); **and**
2. `z_max` fails Holm-corrected `α = 0.01` against M1 on at least 18 of 21 amicable units; **and**
3. the P1 ladder fires on every planted `k`, and P2 fires at or below the design `e_min` of §5 (so the
   instrument is demonstrably live); **and**
4. `N0` is caught by the faithfulness gate.

If (3) fails, nothing is abandoned — the run is void. If (1)–(2) hold but the amicable and non-amicable
arms are indistinguishable, the *amicability* attribution is abandoned while the underlying structure
question is not (§9 cell 2/7).

**What this design cannot falsify, stated now:** (i) features outside the frozen list of §2; (ii) effects
below the measured `e_min`; (iii) effects appearing only at `p ≫ 20000`; (iv) non-group-structured fibre
patterns that are neither exact `Γ_k`-orbits nor `t_k`-approximate — partially covered by the reported
fibre-size multiset, not by either statistic. These four are the declared blind spots and must be restated
verbatim beside any null.

---

## 8. EXACTNESS

Signal path is `int` throughout, per `btc_puzzle_investigation/CLAUDE.md`:
- point arithmetic, coordinate representatives, `x mod n`, `δ`, characters via `pow(a,(n−1)//2,n)`,
  orbit enumeration, `Γ*` membership tests, subgroup generators, divisors, `a(k)`, image histograms,
  fibre multisets, discrete logs (integer BSGS): all `int`.
- Permutation/rank p-values against M1 are **exact integer ranks** over 199 replicates; Fisher exact and
  McNemar use `math.comb` and `fractions.Fraction` (§5 numbers were produced this way).
- **Float carve-outs, all analytic-size-only, none in the signal path and none deciding a threshold on raw
  data:** (a) `z(k)` and `z_max` are monotone re-expressions of the integer counts `a(k)` and are ranked
  against the M1 integer ranks — the rank decides, the `z` is display; (b) `log₂` of exact integers when a
  `|Γ*|` is quoted in bits; (c) Holm's comparison arithmetic on already-exact rank p-values.
- `check_no_float.sh` must pass on all run scripts before any statistic is read.

---

## 9. PRE-COMMITMENT

Filled in before the run. Each cell is the conclusion; no cell may be renegotiated after seeing data.
"Fires" = `|Γ*|/|Γ*_forced| > 1` with the faithfulness gate passed (exact arm), or Holm-corrected
`α = 0.01` vs M1 (graded arm).

| # | Outcome | Pre-committed conclusion |
|---|---|---|
| 1 | Exact arm: `|Γ*|/|Γ*_forced| > 1`, faithful, on **≥ 15 of 21** amicable units, **and** the matched contrast is Fisher-significant at `α=0.01` (per §5 table, e.g. 15/21 vs ≤6/21) | **A symmetry beyond the F2 ceiling exists on the amicable arm.** Report it by *name*: the group `Γ*`, its order, canonical generator, the `σ`'s, the fibre multiset — never as a bit count alone. Grade `[VERIFIED-INSTANCE]`, scope `p < 20000` verbatim from §6. Immediate next step is a *proof* attempt that `Γ_k` is forced by the amicable relation, since only a proof reaches secp. **No ECDLP claim is made or implied at this cell.** |
| 2 | Exact arm fires on ≥15/21 amicable **but the contrast fails** (non-amicable fires at a statistically indistinguishable rate) | **The structure is a CM / `j = 0` family law, not an amicable one.** The amicability attribution is withdrawn in the same sentence that reports the structure. Re-registered as a CM-family question; F1 is not invoked. |
| 3 | Exact arm fires on **< 15 of 21** amicable units, no replication | **Chance pattern, not named.** Per the retest-out-of-sample rule, an unreplicated `Γ*` is reported as a per-curve coincidence with its unit list, and no group is named. Nothing is escalated. |
| 4 | Exact arm at forced value everywhere; **graded arm fires** (≥18/21, Holm `α=0.01`, contrast significant) | **Approximate, not exact, symmetry.** Output is a *characterization*: which divisors `k`, which `t_k`, the agreement excess, the fibre multiset — routed to an anomaly drill under the §X protocol. This is **not** called a leak and **not** called bits. |
| 5 | Exact arm at forced value everywhere; graded arm within M1 null on ≥18/21; **P1 and P2 both fire** at measured `e_min` | **Scoped null with power.** Statement form, mandatory: "Among the 4 frozen partner-side features, on `E_7/F_p` for the 21 amicable units with `p < 20000`, no symmetry beyond `μ₆`-forced was detected, exactly or approximately above `ε = e_min(n)` (measured, per-curve table)." Followed verbatim by the four §7 blind spots. **This is not a closure of the amicable channel and may not be written as one** (`feedback_negative_bias_enlarge_nulls`). |
| 6 | **P1 or P2 fails to fire** on any curve | **Run void — instrument failure.** No conclusion about the hypothesis, in either direction. The null is uninformative. Fix and re-run under this same spec. |
| 7 | Amicable-vs-non-amicable contrast is null (arms indistinguishable) while *something* fires | Whatever fired is attributed to the shared structure (CM by `Z[ω]`, `j = 0`, `n` prime), **not** to amicability. F1's amicability is not evidence for it. Same as cell 2 but stated for the graded arm too. |
| 8 | Frame yields fewer than 21 usable matched pairs, or the observed rate difference is < 0.33, or `e_min` exceeds the effect the plant ladder can resolve | **Abstain on that arm.** Per `feedback_prereg_abstention_is_the_finding`: abstention is reported as abstention. It is **not** a null, **not** a closure, and does not license a post-hoc statistic on the same data. |
| 9 | `N0` is reported as a finding | Faithfulness gate failed. **Run void** (same handling as cell 6). |
| 10 | A `d`-dependent quantity is found anywhere in a hypothesis feature's evaluation path | **Stop and report the construction defect as the finding** (constraint 1). No statistic from that feature is reported, at any significance. |

**Standing constraints on every cell.** No number is quoted without its §6 scope. No cell licenses a
statement about secp or about ECDLP. No cell licenses adding a feature to §2 and re-running; a new feature
requires a new prereg. Deviations go to the DEVIATIONS file before the affected data are read.
