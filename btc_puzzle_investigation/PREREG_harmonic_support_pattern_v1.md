# PREREG — Per-harmonic support pattern of |U(a0,b,c)| within the conserved budget

**File:** `PREREG_harmonic_support_pattern_v1.md`  **Date:** 2026-07-20  **Status:** PRE-RUN. No `(b,c)`-distribution statistic has been computed. No arm has been scored.

**One-line scope, up front.** Enumerable model curves `E : y^2 = x^3 + 7` over small `F_p` only (a few hundred to a few thousand). secp's `p = 2^256 - 2^32 - 977` is **not** enumerable and **nothing in this run transfers there** — every object below requires a full group sum over all `d`, which is exactly what is unavailable at `2^256`.

---

## 1. OBJECT

`E : y^2 = x^3 + 7` over `F_p`, prime group order `n`, generator `G`, `d = 1..n-1` fully enumerable via `t_y_maxbound_v1.prime_order_curve` / `group_coords` (exact integer curve arithmetic). Fix `a0 = 1` (the frequency matched to the target character `e_n(a0 d)`).

Exact definitions (already coded in `joint_shadow_decompose_v1.build_U`, `t_y_maxbound_v1.U_all_a`):
```
x_d, y_d       = coords of d*G           (exact int)
T(a,b)         = sum_d e_p(b x_d) e_n(a d)
U(a,b,c)       = sum_d e_p(b x_d + c y_d) e_n(a d)          (d=1..n-1; d=0 excluded)
```
Aligned readout on frequency support `S`:
```
Fhat(b,c) = conj(U(a0,b,c)) / |U(a0,b,c)|      on S, else 0
Corr(a0)  = (1/(n-1)) sum_d F(P_d) e_n(a0 d),   F(P) = sum_{(b,c) in S} Fhat(b,c) e_p(-b x - c y)
```

**Algebraic consequence (well-posedness, verify in the run's own output).** With phase-only `Fhat = conj(U)/|U|`, the point-space pairing contributes back `conj(Fhat) = U/|U|`, so each `(b,c)` term contributes `Fhat * conj(U) = |U|` with **no cancellation**:
```
Corr(a0) = (1/(n-1)) * sum_{(b,c) in S} |U(a0,b,c)|.
```
The run MUST print `Corr(a0)` computed both ways (via the point-space `F` reconstruction and via the direct sum of `|U|`) and confirm they agree to the float carve-out tolerance. This is a **well-posedness check, not evidence.**

**The per-harmonic contribution is the exact nonnegative number `|U(a0,b,c)|`.** The target of this run is the **distribution of these numbers across `(b,c) in S`** — a within-budget quantity that no sector total can see.

---

## 2. FORCED FACTS — mark as contributing ZERO evidence

These are established and constrain `|U|`; any statistic dominated by them is uninformative and must be reported as forced.

- **F1 conservation (sector total):** `sum_b |T(a,b)|^2 = p(n-2)`, i.e. mean square exactly `p` per harmonic. Bounds the *total* budget, says nothing about the *distribution*.
- **F2 ceiling (individual):** `|U(a,b,c)| <= 4 sqrt(p) + 1` (Weil II / Kohel–Shparlinski, uniform in `(b,c)`; `secp_ks_bound_verified_2026_07_17`). A per-harmonic cap, not a shape.
- **F3 equivariance (readout check, §7):** `U(a,b) = U(lambda a, beta b)`, `beta^3=1 mod p`, `lambda^3=1 mod n` (GLV), verified to `0.00e+00`. Gives the exact free prediction `|U(a0, beta b, c)| = |U(lambda^{-1} a0, b, c)|`. Checked to machine precision as a **readout validation**; forced, zero evidence.
- **F4 already measured as sector totals (`joint_shadow_mu3_v1`):** `e_n(a0 d)` energy per μ6-isotype = exactly `1/6` in five isotypes (trivial-isotype deficit = the excluded point `d=0=O`); aligned-readout alignment flat across CM weights `w0 ~ w1 ~ w2`. **These are the objects this run must NOT re-measure.** A within-sector claim is only new if it survives conditioning on the sector.

The mask is a **shear, not a flattening**: F3 ties the three `b`-sectors of row `a0` to *other* `a`-rows, not to each other within `a0`. So the within-row/within-sector distribution of `|U|` is genuinely unconstrained by F1–F4.

---

## 3. STATISTICS (frozen, per arm)

All primary statistics are **rank / permutation** based so no pass/fail is decided by float precision (see §8). Magnitudes `|U|` are normalized by `sqrt(p)` before any comparison.

### ARM A — characterization (NO pass/fail; bounded magnitude only)
Multiset `M = { |U(a0,b,c)|/sqrt(p) : (b,c) in S }`. Report the shape:
- `topk(f)` = mass fraction in the top `f` of harmonics, for `f in {0.01, 0.05, 0.10, 0.25}`.
- `Neff = (sum |U|)^2 / sum |U|^2`  (effective support; `Neff/|S|` in `[0,1]`).
- `max/sqrt(p)` and the empirical CDF quantiles `{0.5,0.9,0.99}`.
- **The same profile computed WITHIN each μ6 sector separately** (using the isotype machinery of `joint_shadow_mu3_v1`), so a within-sector claim is separable from a between-sector one.

Arm A is a **characterization**. It has no hypothesis and is reported as a bounded magnitude with power and scope — never as a verdict.

### ARM B — does the active set carry `d`, or is it the coordinate geometry's?
The scalar precedent failed to separate: `joint_shadow_decompose_v1` found char-vs-random phase-only reconstruction gave the *same* scalar fidelity (joint `0.999` vs `0.999`; x-only `0.66` vs `0.67`). Arm B re-runs that control **against the PATTERN statistic, not the scalar.**

- **Pattern statistic** `P` = the vector of Arm-A shape descriptors `(topk(0.05), Neff/|S|, max/sqrt(p))` — AND, load-bearing, the **support-set identity**: which `(b,c)` are in the top-`f` set, as a 0/1 indicator vector `chi_top(f)` over `S`.
- **Matched control (state exactly what is held fixed / destroyed):**
  - *Held fixed:* the point set `{(x_d,y_d)}`, the support `S`, the phase-only reconstruction map, `p`, `n`, `a0`.
  - *Target swapped:* replace the leaking character `e_n(a0 d)` with a **random unit-phase target `g(d)`** (iid unit phases over `d`), rebuild `U_g(b,c) = sum_d g(d) e_p(b x_d + c y_d)`, recompute `P`.
  - *Null distribution of `P`:* over `R >= 200` independent random targets `g`. For each shape descriptor: the two-sided rank of the character's value within the `R` null values (report as an empirical `p`-value, no threshold pre-set — the *number* is the output). For the support-set: Jaccard overlap `J = |top_char ∩ top_g| / |top_char ∪ top_g|` between the character's top set and each random target's top set; report the character-vs-character-stability baseline (re-draw nothing; this is 1) is meaningless, so instead report the **null Jaccard distribution among random targets** and ask whether the character's top set is more/less self-consistent under the F3 equivariance map than a random target's (see §7 tie-in).
- **Artifact-preservation requirement (load-bearing, `feedback_residue_vs_component_tautology`):** the swap changes ONLY the target `g(d)`; it does NOT touch the point geometry, so it does **not** destroy the coordinate-geometry artifact the same way it would destroy a genuine `d`-carrying signal. This is the property the prior `r = v - w` failure lacked (its shuffle broke artifact and signal identically). State in the outcome table what a flat `P`-null means without dismissal.

### ARM C — locality / cheapness (the actual question)
Is the active set at row `a0` predictable by a selector that does **NOT** compute `U` (a full group sum over all `d`, unavailable at `2^256`)?

**Pre-committed `d`-free selectors** (frozen now; none may be added post hoc). Each is a function of `b` (and optionally `c`) ONLY:
- `s1 = Legendre(b | p)`
- `s2 = chi3(b)`  (μ3 weight of `b`, via `order3(p)` as in `joint_shadow_mu3_v1`)
- `s3 = 1[ |b| small ]`  (`b` in a fixed interval `[1, floor(p/10)]`, fixed pre-run)
- `s4 = 1[ b in fixed GLV sector ]`  (β-orbit class of `b`, fixed pre-run)
- `s5 = 1[ c = 0 ]` vs `1[ c != 0 ]`

**Statistic:** AUC (equivalently, Mann–Whitney rank statistic) between each selector and the target `y(b,c) = |U(a0,b,c)|`; for real-valued `s2`, Spearman rank correlation. **Matched null:** permute the `(b,c) -> |U|` assignment (destroys any selector→magnitude association; preserves the `|U|` multiset and each selector's marginal). Report AUC/`rho` against the null band from `R>=200` permutations.

---

## 4. TAUTOLOGY GUARD (code-level, load-bearing)

`|U(a0,b,c)|` is defined **using `a0`**, and `a0` is the frequency matched to the target character. Any selector that reads `a0`, `d`, or any quantity derived from them is **circular** and its result is uninformative (`feedback_residue_vs_component_tautology`).

State as a decidable code condition, not an intention:
- Each selector `s_i` is implemented as a Python function whose signature is **exactly** `s_i(b, c, p, n)` — it may read `b, c, p, n` and nothing else. It may NOT take `a0`, `d`, `xs`, `ys`, `U`, or any array indexed by `d` as an argument.
- The run MUST print, for each selector, the tuple of argument names its function accepts (via `inspect.signature`), and assert the set is a subset of `{b, c, p, n}`. A selector failing this assertion aborts the run.
- The target `y = |U(a0,b,c)|` is computed in a separate code path that never passes its intermediate `d`-indexed arrays to any selector.

The control in each arm is chosen so it does **not** destroy artifact and signal identically: Arm B swaps only the target (geometry intact); Arm C permutes only the `(b,c)->|U|` map (selector marginals intact). Neither is a global shuffle of the kind that broke the `r = v - w` test.

---

## 5. CONTROLS (must all fire; no verdict if any fails)

- **C1 — well-posedness (F-consequence):** the two computations of `Corr(a0)` (point-space vs direct `sum|U|`) agree to `< 1e-6` relative. Fires by agreeing.
- **C2 — equivariance readout (F3):** `max over (b,c) of | |U(a0, beta b, c)| - |U(lambda^{-1} a0, b, c)| |` `< 1e-6`. Forced, zero evidence; fires by holding.
- **C3 — planted concentrated positive (Arm A / Arm B MUST detect):** build a synthetic `U_plant(b,c)` whose magnitude is a deliberately concentrated active set — e.g. `|U_plant| = 4 sqrt(p)` on a pre-chosen `1%` of `(b,c)` and `~sqrt(p)/10` elsewhere, phases carrying a genuine `e_n(a0 d)` signal by construction. Arm A `topk(0.01)` must be far above the diffuse baseline; Arm B must separate `U_plant` from random targets (its pattern `p`-value must be extreme). **If C3 does not fire, no result is reported for any arm.**
- **C4 — negative selector plant (Arm C):** a selector that is pure noise of `(b,c)` (e.g. `hash(b,c) mod 2`, still `d`-free) must score AUC `~0.5` within the permutation band. Fires by landing in-band.
- **C5 — floor calibration (Arm A):** a random-phase `U` (iid unit phases) gives the diffuse-baseline profile (`Neff/|S| ~ 1`, `topk(0.01) ~ 0.01`); Arm A magnitudes are reported relative to this floor.

---

## 6. POWER & SCOPE (per arm)

- **Primes:** enumerable model primes, `p ≡ 1 mod 6`, `p` from `~163` up to a few thousand (target set e.g. `{163, 211, 349, 433, 577, 1009, 2011, ~6000}` as compute allows). `n` prime, `|S| = p^2 - 1` grid points, subsampled if needed with the subsample fixed pre-run.
- **Arm A power:** smallest detectable concentration = a top-`1%` mass fraction exceeding the C5 floor by more than the C5 spread; report the measured floor spread so the detectable step is a printed number, not an assumption.
- **Arm B power:** with `R` null targets, the smallest separable pattern shift is the `1/R`-resolution of the rank `p`-value; state `R>=200` gives resolution `<= 0.005`.
- **Arm C power:** AUC detectable above the permutation band at the given `|S|`; report the band width (it shrinks like `1/sqrt(|S|)`).
- **Scope (restated):** model curves only; `2^256` not reachable; every reported number carries `p`-range and power. Nothing here is a statement about secp.

---

## 7. EQUIVARIANCE TIE-IN (readout check, forced)

F3 predicts `|U(a0, beta b, c)| = |U(lambda^{-1} a0, b, c)|` exactly. Two uses, both forced (zero evidence):
1. **C2** validates the readout.
2. In Arm B's support-set descriptor, the character's top set must be **exactly equivariant** under `b -> beta b` composed with `a0 -> lambda a0`; a random target's top set need not be. This is a structural difference that is *forced* for the character and therefore reported as a readout property, NOT as evidence that the active set carries `d`. (It distinguishes character from random trivially; the informative question is whether anything *beyond* this forced symmetry distinguishes them — that is what Arm B's `p`-values on the un-forced descriptors measure.)

---

## 8. FLOAT CARVE-OUT

Curve/group arithmetic and the `(b,c)` grid are **exact integers** (`t_y_maxbound_v1`, `sympy.isprime`, `ec_add`). `numpy` float appears ONLY in the `|U|` magnitudes and the FFT (`build_U`, `fft2`). No key or `d`-secret is on the float path. **No pass/fail threshold is decided by float precision:** all arm decisions are rank/permutation statistics; the only float thresholds are the `1e-6` readout-agreement checks C1/C2, which are validations, not evidence.

---

## 9. PRE-COMMITTED OUTCOME TABLE (say it now, no dismissal language)

| Case (from printed output) | Reported as |
|---|---|
| C1/C2/C3 all fire; Arm A shows concentration above C5 floor | "Within the conserved budget, `|U(a0,·)|` mass concentrates on a fraction `~f` of harmonics on these primes (magnitude `topk`, `Neff`), with `p`-range and power stated." Characterization only. |
| Arm A shows concentration AND Arm B: random targets produce the **same** pattern statistic | "The support-pattern magnitude, in the tested descriptors, does **not** separate the leaking character from a random target on this point geometry: it is a bounded property of the coordinate geometry's phase distribution, magnitude `X` with power `Y`, in this basis. This is a flat pattern statistic — a bounded magnitude in the tested basis, **not** an absence of structure; the frequency-support identity and finer/ higher-degree descriptors are untested and explicitly out of scope." |
| Arm A concentration AND Arm B: character's pattern is extreme vs the random-target null (beyond the F3-forced symmetry of §7) | "On these primes the active-set pattern carries character-specific structure beyond the forced equivariance, magnitude `X`, power `Y`, scope model-curves-only. Next probe: [Arm C / higher-degree / larger p]. Not a verdict; not transferable to `2^256`." |
| Arm C: a `d`-free selector `s_i` scores AUC/`rho` above its permutation band | "Selector `s_i` (function of `(b,c)` only, tautology-guard asserted) predicts the active set with AUC `X` on these primes — a bounded, scoped association. States nothing about extractability at `2^256` (still requires the full `U` sum). Next probe: [robustness across p / other selectors]." |
| Arm C: all selectors in-band | "No pre-committed `d`-free selector predicts the active set above the permutation floor on these primes (power `Y`). Scoped null bound to selector list + sample + floor; a flat selector score is a bounded magnitude, not proof no cheap selector exists." |
| C3 does not fire | **No result reported for any arm.** Debug the detector; re-run. |

---

## 10. OUTPUT TYPE (pre-committed)

A **characterization plus bounds with power and scope.** Never a verdict about ECDLP, extraction, security, or an avenue being open or closed. Nulls are conditional (method + sample + floor). A `sqrt(p)` bound / `1/sqrt(n)` decay is a **magnitude**, not "no structure" (`feedback_negative_bias_enlarge_nulls`). Dissolution of a proposed active/starved split is a positive result (a sharper law or bounded magnitude), reported as such.

---

## Files this run will produce
- `harmonic_support_pattern_v1.py` — the run (≤ ~300 lines; reuses `t_y_maxbound_v1`, `build_U`/`glv_beta` from `joint_shadow_decompose_v1`, `order3`/isotype helpers from `joint_shadow_mu3_v1`).
- `harmonic_support_pattern_v1.log` — printed output; every §9 row decidable from it.
- `RESULT_harmonic_support_pattern_v1.md` — characterization + bounds.
- `PREREG_harmonic_support_pattern_v1_DEVIATIONS.md` — any departure from this spec.
