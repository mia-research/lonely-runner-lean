# PREREG — μ₃ PHASE alignment within GLV triples of U(a,b,c)  [v1]

**Status: PRE-REGISTRATION. Written before any 9-prime run. No verdict here.**
Object script header: `xy_interference_U_v1.py`. Runner to be built:
`mu3_phase_within_triple_v1.py` (reuses `mu3_glv_frequency_support_v1.py`).
Companion magnitude probe (already done, scoped null): `RESULT_mu3_glv_frequency_support_v1.md`.

Grade of any number this spec licenses: **EMPIRICAL, scoped** to §6. This spec cannot
promote a grade; it can produce a scoped null or a scoped fired-cell.

---

## 1. OBJECT

`U(a,b,c) = Σ_{d=1}^{n-1} e_p(b·x_d + c·y_d)·e_n(a·d)` on the CM curve `y²=x³+7`,
`n=#E` prime, `(x_d,y_d)=[d]G`. At FIXED nonzero a-rep `a₀` and column `c`, the μ₃/GLV
triple is `u_0=U(a₀,b,c)`, `u_1=U(a₀,βb,c)`, `u_2=U(a₀,β²b,c)`, `β`= order-3 elt of F_p*.

**What we measure:** whether, at fixed magnitudes `|u_j|`, the three complex values of a
μ₃-triple carry a μ₃-isotype organization in their PHASE — i.e. concentrate in the
`u_j ≈ ω^{j}·C` isotype (ω=e^{2πi/3}) more than a phase-marginal-preserving null. This is the
PHASE complement of the magnitude co-occurrence already tested (that came back a τ-robust
scoped null, pooled |Z|<3 over the same 9 primes).

**Disjointness / tautology check.** The feature (a μ₃-isotype energy of the real parts) and
the target (chance under repartition of reps) are NOT co-constructed: the null preserves the
exact per-rep multiset `{(|u_j|, Re u_j)}` and destroys ONLY the μ₃-orbit grouping `{b,βb,β²b}`.
The statistic reads the grouping; the null erases the grouping; they are disjoint. No shared
construction. (Contrast the r=v−w tautology in memory — here feature and target do not share
a build step.)

**Forced structural identity (documented, not a defect).** By the pullback
`U(a,b,c)=U(λa,βb,c)`, at fixed a₀ the b-triple equals `(U(a₀,b,c), U(λ⁻¹a₀,b,c), U(λ⁻²a₀,b,c))`
— the SAME (b,c) across the λ-orbit of a₀. So the b-μ₃-triple is the a-λ-orbit at fixed b.
This makes the triple a genuine structural object (not a proxy) and is consistent with the
a-reps being λ-orbit representatives (`a_reps` excludes λa₀). It does not force the phase
(§ non-forced below).

---

## 2. STATISTIC  (exactly one; pooled, targeted; gauge-invariance PROVED)

Per triple, with `r_j := Re(u_j)` and `ω=e^{2πi/3}`:

```
        | r_0 + ω⁻¹ r_1 + ω⁻² r_2 |²        |R_ω|²
  ψ  =  ---------------------------------  =  ---------- ,   R_ω := Σ_j ω^{-j} r_j
          |u_0|² + |u_1|² + |u_2|²           Σ_j |u_j|²
```

Block statistic (one per `(a₀,c)`): `S = Σ_{triples t} ψ_t`.
Per-prime standardization: `Z = (S_obs − E_null)/√Var_null`, moments from Null-P (§3), by
permutation. Pooled over the 9 primes: **Stouffer `Z* = (Σ_p Z_p)/√9`** — this is the ONE
number the run reports. (A sum over triples, not a max: pooled and unbiased.)

### 2a. Gauge-invariance — PROOF (load-bearing)

The forced ± gauge is independent per-rep conjugation `u_j → conj(u_j)` (fact 1:
`U(a₀,−b,c)=conj U(a₀,b,c)`, and {b,−b} are one ±-rep, so the fold picks one branch freely).
`ψ` is built only from `Re(u_j)` and `|u_j|`, each invariant under `u_j→conj(u_j)`
(conjugation preserves real part and modulus). Hence `ψ` is invariant under all `2³=8` gauge
choices. **Verified mechanically on F_61: max|ψ − ψ_flip| over the full 8-element gauge orbit
of every triple = 0.00e+00.**

### 2b. Why `Re` and not the raw isotype `|T_ω|²` — derivation, not choice

`ψ` is the gauge-symmetrization of the raw isotype energy. With `T_ω=Σ_j ω^{-j} u_j`,
averaging `|T_ω|²` over the 8-element gauge orbit uses `⟨u_j ū_k⟩_gauge = Re(u_j)Re(u_k)`
(j≠k) and `⟨|u_j|²⟩=|u_j|²`, giving
`⟨|T_ω|²⟩_gauge = Σ_j Im(u_j)² + |R_ω|²`.
The `Σ Im²` term is an isotropic (non-μ₃-aimed) background; stripping it and normalizing yields
`ψ`. Consequence: **at quadratic order the ONLY gauge-invariant μ₃-phase content lives in the
real parts** — the raw `|T_ω|` (gauge-DEPENDENT, fact 3: 16.8→19.6 under a flip) is not a valid
statistic; `ψ` is its correct symmetrized, targeted form. `ψ` also excludes the trivial isotype
`|Σ r_j|²` (aimed purely at the μ₃ subspace, not the mean).

### 2c. Non-forced — PROOF sketch + runtime guard

- Not forced by the pullback: `U(a₀,βb,c)=U(λ⁻¹a₀,b,c)` couples the triple to the λ-orbit in a,
  not to a fixed phase relation among `u_0,u_1,u_2`; no identity pins `R_ω`.
- Not gauge-variant (§2a). Does NOT use `arg(u_0u_1u_2)` (which fact 3 flags as sign-flipping
  under odd gauge flips) — that flagged variant is explicitly avoided (§Flags).
- **Empirically unforced (F_61):** `ψ` ranges 0.004–0.79 across triples (var 0.080 > 0);
  Null-P mean 0.448. **Runtime guard: abort as forced if per-block Var(ψ_t)=0.**

---

## 3. MATCHED CONTROL — Null-P (phase analogue of the validated Null-B)

Within each `(a₀,c)` block, keep every rep's full complex value `U(a₀,·,c)` intact — hence
every `|u_j|`, every `Re u_j`, and each rep's forced Hermitian conj-gauge are preserved
EXACTLY — and re-draw the partition of the `R=(p−1)/2` reps into `R/3` groups of three,
uniformly at random. This is the exact phase analogue of the validated Null-B
(equipartition of near-zero labels into triples).

- **Preserves:** the exact multiset `{(|u_j|, Re u_j, u_j)}` — full phase marginal, all
  magnitudes, the per-rep Hermitian ± structure. Magnitude co-occurrence is preserved in
  distribution (it is an established scoped null from the magnitude probe).
- **Destroys:** ONLY the μ₃-orbit grouping `{b,βb,β²b}` — the tested alignment.
- **Avoids the documented wrong-null (`RETROSPECTIVE_FINDING_01` §2):** that artifact came from
  omitting `g(n−d)=conj g(d)`. Null-P never touches Hermitian structure — it operates on the
  already-Hermitian-folded ±reps and moves whole intact complex values, so the ± symmetry the
  readout has by definition is preserved, not shuffled away.

Moments per block by Monte-Carlo permutation of Null-P (B≥2000 repartitions); optionally the
exact uniform-3-subset moments of ψ. Verdict = ranked permutation statistic (monotone), never a
float threshold — matches the magnitude probe's carve-out.

---

## 4. CONTROLS

- **PLANT (must FIRE, Z≫0):** for a fraction `f` of true triples, overwrite
  `u_j ← |u_j|·e^{i(φ+2πj/3)}` (true magnitudes, μ₃-aligned phases; φ fixed per block). On F_61
  this lifts block-mean ψ from 0.448 (null) to ~0.63 (aligned). **Gauge-robustness of the
  plant:** apply a random per-rep conj flip to each planted triple before scoring — because ψ is
  gauge-invariant the plant must fire identically (this doubles as a live gauge-invariance test).
- **NEGATIVE (must stay FLAT, Z~0):** same magnitudes, phases `θ_j` iid uniform (no μ₃ step),
  grouped into the true triples. Must return Z within ±3.
- **Forced-diagonal implementation self-test (reuse):** intra-λ-orbit `Var(|U|)=0` on
  `{(a₀,b),(λa₀,βb),(λ²a₀,β²b)}` (magnitude invariance) — already in
  `mu3_glv_frequency_support_v1.selftest`.
- **Gauge-orbit self-test:** assert `max|ψ−ψ_flip|` over all 8 flips of every triple < 1e-9
  (passed on F_61 at 0.00e+00).

**If PLANT does not fire, the null is uninformative and the run is void — full stop.**

---

## 5. POWER  (computed now)

Grounded on F_61: null block-mean μ₀≈0.448, per-triple SD(ψ)≈√0.08≈0.28; a fully μ₃-aligned
triple has ψ≈0.63 (Δ≈0.18 above null, magnitude-limited by unequal |u_j|).

Per prime the pooled block count is `N_tri ≈ 24 a-reps × (p−1) cols × (p−1)/6 triples`; for
p≈2089, `N_tri ≈ 24·2088·348 ≈ 1.7×10⁷`. Injecting a fraction `f` of aligned triples gives
within-prime `Z_p ≈ f·Δ·√N_tri / SD(ψ) ≈ f·(0.18/0.28)·√(1.7×10⁷) ≈ f·2650`.
So a single prime reaches |Z|=3 at `f ≈ 1.1×10⁻³`; Stouffer over 9 primes reaches |Z*|=3 at
**`f ≈ 4×10⁻⁴`** (probability ~0.5), near-certain by `f ≈ 1×10⁻³`.

**Honest caveat (deflates the floor):** columns within a prime are correlated, so the effective
independent N is far below `N_tri`; treat the true replication unit as the 9 primes. Conservative
detectable effect: **a per-block μ₃-phase energy excess of ~1–2% of the isotype range, or `f`
on the order of 10⁻³ aligned triples, at pooled |Z*|>3.** A bound below this is a size at this
power, not "no structure" (see §7).

---

## 6. SCOPE

Every number inherits this scope: CM curve `y²=x³+7`; 9 prime-order curves
`n∈{2089,2143,4159,8191,8209,8293,16477,19231,19249}`; 24 a-orbit reps (λ-orbit reps of F_n*);
all columns `c∈{1,…,p−1}` (c=0 excluded); μ₃-triples under `b→βb` on the (p−1)/2 ±reps;
statistic ψ (§2), Null-P (§3), Stouffer pooling. No claim outside this scope; in particular
nothing about 2²⁵⁶-scale curves and nothing generation-side.

---

## 7. FALSIFICATION

- **Abandon** the "μ₃ phase organization" hypothesis at this power/scope if pooled
  **|Z*| < 3** AND the PLANT fired (Z_plant ≫ 3) AND the NEGATIVE stayed flat (|Z_neg|<3).
- **Void the run** (uninformative, not a null) if PLANT does not fire, or if the gauge self-test
  or forced-diagonal self-test fails, or if per-block Var(ψ)=0 (forced statistic).
- A pooled |Z*|<3 is a **scoped null with the §5 power floor**, NOT a closure of phase structure:
  it bounds the μ₃-isotype energy of the REAL PARTS at quadratic order. It says nothing about
  (i) higher-order phase invariants, (ii) the imaginary-part isotype (gauge-washed at 2nd order —
  a DIFFERENT object), (iii) phase structure keyed to specific c-columns not visible after pooling.
  Any dismissal must name object+observable-class+power+scope (closure-grade bar).

---

## 8. EXACTNESS

Int/Fraction signal path: EC point enumeration, `a·d mod n`, `(b·x_d + c·y_d) mod p` are exact
`int` (reused from the validated runner). Float carve-out: `|U|`, `Re U`, roots of unity, and ψ
are analytic magnitudes only — no key in the path. The verdict is a permutation-ranked monotone
statistic (Stouffer Z of block permutation Z's), never a float threshold on the data. Identical
carve-out to the magnitude probe. `check_no_float.sh` must pass on the signal-path functions.

---

## 9. PRE-COMMITMENT  (filled BEFORE the run)

| Outcome | Conclusion (scoped to §6) |
|---|---|
| PLANT fires, NEG flat, **\|Z*\|<3** | §1 result: **scoped null** — no μ₃ phase organization in the real-part isotype at the §5 power floor over these 9 primes. Companion to the magnitude null: both phase and magnitude co-occur at chance within μ₃-triples. Grade EMPIRICAL, scoped. Does NOT close phase structure (§7). |
| PLANT fires, NEG flat, **\|Z*\|≥3** | §1 result: **fired cell** — μ₃ phase alignment detected in the gauge-invariant real-part isotype. Pre-committed conclusion goes to §1; report per-prime Z_p, sign, and the isotype (ω vs mean) energy split. Any follow-up (which columns, effect size, OOS on new primes) is EXPLORATORY, below the fired cell. Retest out-of-sample on ≥3 fresh prime-order CM curves before naming a mechanism. |
| PLANT does NOT fire | **VOID** — null uninformative; fix Null-P/statistic and re-register. No conclusion. |
| NEG not flat, or any self-test fails | **VOID** — implementation/null defect; no conclusion. |

Pre-committed: a fired cell's conclusion is §1 and is NOT overridden by any post-hoc statistic on
the frozen window (memory: prereg-abstention-is-the-finding). Abstaining on an arm ≠ closing it.

---

## FLAGS — forced / gauge-variant variants that MUST NOT be substituted post-hoc

- **`|T_ω|²` (raw isotype energy)** — GAUGE-DEPENDENT (fact 3, 16.8→19.6 under one flip).
  Invalid as a statistic. Only its gauge-symmetrized form ψ (§2b) is admissible.
- **`arg(u_0 u_1 u_2)`** — sign-flips under an odd number of gauge flips (fact 3). Not
  gauge-invariant; explicitly excluded. `|u_0 u_1 u_2|` is invariant but is a MAGNITUDE
  (already probed), not phase-alignment.
- **`Im`-part μ₃ isotype `|Σ ω^{-j} Im u_j|²`** — gauge-washes to `Σ Im²` at 2nd order (no
  μ₃ structure survives); a bound on it is NOT a bound on ψ (different object — §7).
- **max-over-gauge-orbit of ρ_ω** — admissible (gauge-invariant) but max-of-8 is upward-biased
  and lower-power; kept only as a SECONDARY robustness check, never the primary.
- **The full gauge-average Φ=(Σ Im² + |R_ω|²)/Σ|u|²** — gauge-invariant but carries the
  isotropic Im background; SECONDARY only, ψ (background-stripped, μ₃-targeted) is PRIMARY.
- **Choosing c-subset or τ after seeing Z** — post-hoc filter; forbidden. Scope is all c
  (§6); any column-restriction is EXPLORATORY under a fired cell only.
- **ω vs ω² isotype** — for real `r_j`, `|R_ω|²=|R_{ω²}|²`; ψ is already symmetric, no choice
  to tune.
