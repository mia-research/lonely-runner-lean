# PRE-REGISTRATION — Structured-pair (diagonal `v=k·u`) single-index bilinear witness

**Status: SPEC ONLY. Written before any structured-pair data is seen. Decidable artifact.**
**Date: 2026-07-19. Author role: experiment-designer (context-isolated, object-level).**

This witness CONFIRMS or REFUTES an already-written ANALYTICAL reduction. It is not the primary
claim. The primary claim is the reduction (below); this run only checks it numerically and reports a
magnitude with power+scope. Per the folder's language rule, the null branch is a **magnitude**, never
"no signal" / "closed".

---

## 0. THE REDUCTION BEING TESTED (the primary claim; stated so the witness is decidable)

`bilinear_closure_proof_v1.md` (Theorem B) bounds the **full** two-point sum over independent `(u,v)`:
`S(a,b)=Σ_{u,v} A(P_u)B(P_v)C(P_{u+v}) e_n(au+bv)`, giving `|S|/n² = O(p^{−1/2})`. The **structured
pair** (`POSITIVE_FINDINGS_MASTER_v3.md` §X, frontier 7 / "§X.7", carried OPEN) is the **diagonal
slice** `v = k·u` of that grid — a measure-zero restriction Theorem B does NOT bound directly. Setting
`v=k·u` collapses the two-index sum to the **single-index** sum

> `Ĉ_k(a') = Σ_{u∈ℤ/n} A(P_u)·B(P_{k·u})·C(P_{(1+k)·u})·e_n(a'·u)`,  `a' = a+bk`.

REDUCTION CLAIM: `[k]` is the scalar-multiplication map on `E`, a rational map with
`x∘[k] = φ_k(x)/ψ_k(x)²`, `deg = k²`. Hence the compound readout
`F_k(P_u) := A(P_u)B(P_{ku})C(P_{(1+k)u}) = e_p( b₁x_u + b₂x_{ku} + b₃x_{(1+k)u} + y-terms )`
is a **single** nonconstant rational readout on `E` of pole order `D_k = O(k²)` (dominant term
`2·(1+k)² ≈ 2k²`). The **Kohel–Shparlinski** single-sum bound (`[CITED]` Appendix C; additive ψ only,
§XI.10) then gives, on a **prime-order** curve where `ω([d]G)=e_n(a'd)` is the DL twist,
> `max_{a'} |Ĉ_k(a')| ≤ 2·D_k·√p ≈ c·k²·√p`  (`c` a small constant, `+1` for the `d=0` pole).

So the normalized structured-pair correlation `C_k := (1/n)·max_{a'≠0}|Ĉ_k(a')|` is
`≤ c·k²·√p / n = O(k²·p^{−1/2})` at fixed `k`. **Structured pairs at fixed `k` do NOT escape KS.**
The only escape routes are (i) `k ≳ p^{1/4}` (degree grows with `p` ⇒ KS bound goes vacuous = the
separate **unbounded-degree GAP**, §X-frontier list) or (ii) the `m=1` **aligned** readout
`F̂=conj(Ĉ)/|Ĉ|` which needs `Ĉ` itself ⇒ all `x_d` ⇒ **the DLP**.

### 0a. TWO DESIGN CORRECTIONS baked into this spec (so the run cannot misfire)

**CORRECTION 1 — `∝k²` is a CEILING, not the OBSERVED scaling.** `F_k` is a pure phase (`|F_k|=1`),
so Parseval pins `avg_{a'}|Ĉ_k(a')|² = n·(n−1)` **exactly, independent of `k`**. A *generic*
(non-aligned) bounded-degree phase does **not** saturate its KS ceiling: its observed
`max_{a'}|Ĉ_k| ≈ √(n·ln n)` sits at the **floor**, essentially **`k`-independent** for small `k`. The
`k²` factor bounds only the *worst case*. Therefore the OBSERVED `C_k` staying **flat at the floor as
`k` grows** is what CONFIRMS the reduction; a run that expected observed `C_k ∝ k²` and found flatness
would wrongly cry "prediction failed." The `k²`-scaling is witnessed only via (a) the **ceiling
consistency check** `C_k·n ≤ (2D_k+1)√p` never violated, and (b) the **planted** ladder, whose
saturating readout is allowed to climb with its planted degree/strength. **Observed flatness at the
floor = confirmation.**

**CORRECTION 2 — the μ₆-sextant-aligned pair COLLAPSES to degree 3.** For `k=λ` a root of unity mod
`n` (the GLV/μ₆ multipliers, `λ³=1` or `λ=−1`), `[λ]` is an **automorphism** of `E` (norm-1
endomorphism, degree 1), so `x_{λu}=β·x_u` **exactly** (Part I: `x_{λd}=βx_d`). The μ₆-aligned readout
`e_p(b₁x_u + b₂·β·x_u + …) = e_p((b₁+b₂β)x_u + …)` **collapses to a plain degree-3 single-point
readout**. So μ₆-aligned pairs carry **no `k²` inflation at all** and must sit **exactly at the plain
`T`/degree-3 floor**. This is a *stronger* prediction than the generic-`k` case and gets its own
matched control (plain degree-3 random readout). Any escape here would be an algebraically degree-3
sum concentrating — a very sharp anomaly.

---

## 1. OBJECT  (name the mathematical object, not a proxy)

- **Target object.** The **discrete-log frequency** `χ_{a'}(u)=e_n(a'·u)` on the index `u∈ℤ/n` of
  `P_u=[u]G`, `E:y²=x³+7 / F_p`, prime order `n`, generator `G`. "Escape" = a cheap FIXED-coefficient
  structured-pair readout correlating with some `χ_{a'}` above the degree-matched floor.
- **Feature object.** The single-index structured-pair character sum `Ĉ_k(a')` above, built from the
  FIXED cheap readout `F_k(P_u)=e_p(b₁x_u+c₁y_u)·e_p(b₂x_{ku}+c₂y_{ku})·e_p(b₃x_{(1+k)u}+c₃y_{(1+k)u})`.
  Coefficients FROZEN NOW to `(b₁,c₁,b₂,c₂,b₃,c₃)=(3,1,5,2,7,4)` — the identical coefficients
  `difference_set_closure_verify_v1.py` line 14 already uses (continuity + pre-data pinning).
- **Tautology check (mandatory).** Feature and target are **disjointly constructed**: `F_k` is a
  fixed rational readout of the *field coordinates* `x,y`; the target `χ_{a'}` is the *index*
  frequency. The readout coefficients are FIXED small integers chosen BEFORE any FFT — they are **not**
  the data-derived aligned readout `conj(Ĉ)/|Ĉ|` (that one is the DLP and would tautologically fire).
  This is the exact tautology-avoidance the folder's `residue_vs_component` memory demands. **No shared
  construction ⇒ not a tautology ⇒ the test is valid before it runs.**
- **Not-already-closed check.** Theorem B bounds the *full* `(u,v)` sum; the *diagonal* `v=ku` is not a
  triangle-inequality consequence of it. The structured pair is a genuinely distinct single-index
  object requiring the degree-`k²` reduction above, not Theorem B. So §X.7 is a real open item and this
  witness is meaningful (not a re-run of a closed result).

---

## 2. STATISTIC  (exactly one, named now, with its null distribution)

**Primary statistic (per curve `p`, per multiplier `k`):**
> `C_k := (1/n)·max_{a'≠0} |Ĉ_k(a')|`,  `Ĉ_k(a') = Σ_{u=1}^{n−1} F_k(P_u)·e_n(a'·u)`  (drop `u=0`=`O`, a pole).

Computed as `Ĉ_k = FFT_u[ F_k(P_u) ]` (length `n`), `F_k` a length-`n` complex phase vector from
**exact** integer coordinates (see §8). `C_k∈[0,1]`; "at the floor" is a definite number fixed
empirically by the matched control (§3), and analytically `C_k^{floor} ≈ √(ln n / n) ≈ √(ln n)·p^{−1/2}`.

**Null distribution of `C_k`.** Under the matched random-readout null (§3), `|Ĉ_k(a')|²` for `a'≠0`
are ≈ iid `Exp(mean n)` (Parseval: `Σ_{a'}|Ĉ_k|²=n(n−1)`), so `max_{a'}|Ĉ_k|² ≈ n·(ln n + Gumbel)`,
i.e. `C_k^{null} ≈ √(ln n / n)` with rep-to-rep std `≈ 1/(2√(n ln n))` (relative width `≈ 1/(2 ln n)`).

**Max-over-cells bias is CONTROLLED, not ignored.** `max_{a'}` over `n` frequencies is upward-biased;
this is neutralized because the null (§3) takes the identical `max_{a'}` over the same `n` cells, so the
bias is matched and cancels in the rank comparison. The verdict is a **rank of `C_k` against the
null's `C_k` distribution**, never `C_k` vs a bare formula.

**Pooled cross-check statistic (guards a normalization bug).** `Q_k := avg_{a'≠0}|Ĉ_k(a')|² / n`.
Parseval forces `Q_k = (n−1)/n → 1` EXACTLY for any pure phase. If `Q_k` departs from `1`, the readout
is mis-normalized (e.g. a `residue_vs_component`-style tautology) and the run **halts** — no verdict is
emitted. (This is the object-level guard, not a proxy count.)

---

## 3. MATCHED CONTROL / NULL  (reproduces every structure EXCEPT the [k]-diagonal alignment)

Three nulls, each preserving the single-index KS structure and the readout complexity, destroying only
the specific arithmetic being tested. For each, PRESERVES / DESTROYS is stated.

- **NULL-A — degree-matched random rational readout (primary floor).**
  Replace `F_k` by `F_rand(P_u)=e_p(g(x_u,y_u))` where `g` is a random rational function of pole order
  `≈ D_k` (concretely: `g = Σ_{i≤D_k} r_i·x_u^i + s_i·x_u^i·y_u`, random integer `r_i,s_i mod p`),
  same length-`n` FFT.
  PRESERVES: single-index sum over `ℤ/n`; pole degree `≈D_k`; pure phase `|F|=1`; the `max_{a'}` bias.
  DESTROYS: the specific `[k]`-diagonal arithmetic (the tested structure). **This is THE floor `C_k`
  must match.** `R_A = 200` reps per `(p,k)`.
- **NULL-B — random-multiplier diagonal (is the *value* `k=32,64` special?).**
  Replace `k` by a uniform random `k_rand∈(ℤ/n)*` of comparable bit-size; same `F_{k_rand}`.
  PRESERVES: the diagonal single-index form `v=k·u`, pure phase. DESTROYS: the specific value of `k`
  (and, for μ₆-aligned, the automorphism property). `R_B = 100` reps per `(p,k)`.
- **NULL-C (μ₆ case only) — plain degree-3 random readout.** For `k=λ` (μ₆ multipliers), the matched
  floor is the plain `T`-type degree-3 readout `e_p(b·x_u+c·y_u)`, random `(b,c)`, since μ₆-aligned
  collapses to degree 3 (Correction 2). `R_C = 200` reps.

**Negative-prediction baseline.** The analytic floor `C_k^{floor} ≈ √(ln n)·p^{−1/2}` and the ceiling
`(2D_k+1)√p/n ≈ c·k²·p^{−1/2}` are both plotted; the confirm branch is `structured ≈ NULL-A floor ≪
ceiling`.

**Invalid-null guard (stated to avoid the documented failure modes).** A pure index-shuffle of `u`
would destroy the `[k]`-alignment AND the `e_n(a'u)` phasing simultaneously (it breaks the artifact
exactly as it breaks a real signal — the §XI.6 / `residue_vs_component` failure). We therefore do
**not** shuffle the index; NULL-A/B/C keep the exact index arithmetic and vary only the readout /
multiplier. This is the matched-surrogate discipline (DRILL 01: a matched surrogate needs no fit).

---

## 4. PLANTED CONTROL  (must fire or the null is uninformative — full stop)

Inject a KNOWN aligned coupling of KNOWN size `ρ` at a FIXED frequency `a₀=1`:
> `F_plant(P_u) = F_k(P_u) + λ_plant·e_n(a₀·u)`  (unnormalized; the `+ρ·character` term concentrates).

Then `Ĉ_plant(a₀) ≈ λ_plant·(n−1) + O(√n)`, so `(1/n)|Ĉ_plant(a₀)| ≈ λ_plant`; set `λ_plant = ρ`.
(Carve-out: this plant is NOT unit-modulus — allowed, it is a positive control, not a candidate cheap
reader.) Effect-size ladder, per `(p,k)`:
`ρ ∈ {0} ∪ {0.5, 1, 2, 4} × C_k^{floor}` and one large `ρ = 0.10`.

**FIRE / SILENT thresholds (pre-set).**
- FIRE at `ρ`: planted `a₀` ranks strictly #1 in `|Ĉ|`, ranks strictly above the `R_A`-rep NULL-A max,
  AND recovered `(1/n)|Ĉ_plant(a₀)| ∈ [0.8,1.2]·ρ`.
- SILENT: fails either.
- **REQUIRED:** the statistic MUST FIRE at `ρ = 4·C_k^{floor}` and at `ρ=0.10`. **If it does not fire
  there, the null is uninformative and the run is void** (no confirm/escape verdict may be issued).
- The smallest `ρ` in the ladder that FIRES is reported as the **empirical power floor** `ρ_min(p,k)`.
- **`ρ=0` sanity:** the un-planted structured `F_k` must sit at the NULL-A floor (rank-consistent);
  if `ρ=0` already "fires," the statistic is broken (a `Q_k≠1` bug) — halt.

---

## 5. POWER + SCOPE

**Power.** Null-A width is relative `≈ 1/(2 ln n)`; a `z=5` escape needs
`C_k ≳ C_k^{floor}·(1 + 5/(2 ln n))`. Concretely: `n≈10³` ⇒ detect escape `≳ +36%` above floor
(`floor≈0.083`); `n≈10⁴` ⇒ `≳ +27%` (`floor≈0.026`); `n≈10⁵` ⇒ `≳ +22%` (`floor≈0.011`). The
**planted ladder calibrates this exactly** — `ρ_min(p,k)` is the reported detectable correlation, not
the asymptotic formula. Min detectable normalized correlation is therefore `≈ a few × C_k^{floor}`
(absolute `~0.002` at `n≈10⁵`), stated per cell.

**Scope (every number the run emits inherits this).**
- Curve family: `E:y²=x³+7`, `p≡1 mod 3`, **prime group order `n`**, via `prime_order_curve(lo,hi,0,7)`
  (`t_y_maxbound_v1.py`). Generator `G` from that routine.
- Primes: one prime-order curve in each window spanning `p∈[≈200, ≈100000]` (≈8–10 curves; e.g.
  windows near `2^8…2^16`, reusing the closure-verify ladder `≈127,313,691,1663,2557` plus larger).
  `n`-range = the group order `≈p`.
- Multipliers: `k ∈ {2,3,5,8,16,32,64}` (generic, degree `k²`) **and** `k ∈ {−1, λ, λ²}` (μ₆-aligned,
  degree collapses to 3; `λ³=1 mod n` from the GLV routine).
- **Hard scope (state on every number):** `p ≤ ~2^17`, `b=7` only. Says **nothing** about
  `k ≳ p^{1/4}` (the unbounded-degree GAP) nor about `p=2^256`. A structure switching on near `2^256`
  has zero power here (master SCALE BANNER).
- **In-power vs out-of-power cells (finite-size caveat).** The ceiling `(2D_k+1)√p` is only a
  *non-vacuous* constraint (`< n`) when `c·k²√p ≪ n≈p`, i.e. `k ≪ p^{1/4}/√c`. At `p≈10⁵`
  (`p^{1/4}≈17.8`): the **ceiling/`k²`-scaling test** is in-power only for `k≲8`; `k=16,32,64` have a
  *vacuous* ceiling at these `p` and CANNOT test the `k²` bound. **But** the **floor test**
  (structured vs NULL-A) is a matched comparison and is **in-power for ALL `k`** at every `p`. Report a
  `(k,p)` grid tagging each cell `CEILING-IN-POWER` (floor + ceiling) vs `FLOOR-ONLY` (floor test valid,
  ceiling vacuous). The `p^{−1/2}` decay test uses fixed small `k∈{2,3}` across the `p`-ladder (always
  ceiling-in-power).

---

## 6. EXACTNESS  (signal path int/Fraction; float carve-out named)

- **Exact (int) in the signal path:** all curve/group arithmetic (`ec_add mod p`), the orbit
  enumeration `P_u=[u]G`, the index multiplications `k·u mod n`, `(1+k)·u mod n`, and every readout
  exponent `(b₁x_u+c₁y_u+…) mod p` — Python `int`, no `/`, no `float`, no `**0.5`. Reuse
  `prime_order_curve` / `orbit` / coordinate tables from `t_y_maxbound_v1.py` / `xy_interference_U_v1.py`.
- **Float carve-out (named, justified):** the character-sum magnitudes `|Ĉ_k|` via
  `exp(2πi·e/p)` and `numpy.fft` are analytic-size roots-of-unity quantities with **no key / no
  leakage-signal in the path** — the identical carve-out used by `difference_set_closure_verify_v1.py`,
  `xy_interference_U_v1.py`, `t_y_maxbound_v1.py`. The float appears only AFTER the exact integer
  exponent is formed, and only as a magnitude ranked against the matched null. No float decides a
  threshold on the data (per folder CLAUDE.md). `check_no_float.sh` must pass on the signal-path portion.
- **Pooled `Q_k=1` guard** (§2) is the exact-arithmetic tripwire: a float leak into the exponent would
  perturb Parseval; `Q_k≠1` halts the run.

---

## 7. FALSIFICATION  (both directions, written before the run)

- **What refutes the REDUCTION (⇒ §X.7 stays OPEN with a named object):** for some **in-power** `(k,p)`,
  the structured `C_k` exceeds the NULL-A floor by more than the planted-calibrated threshold
  (`C_k` ranks above the `R_A`-rep NULL-A max AND `> C_k^{floor}·(1+5/(2 ln n))`), *and* this excess
  **does not decay** as `p` grows (fixed small `k`). Equivalently: the ceiling `C_k·n ≤ (2D_k+1)√p` is
  respected but `C_k` tracks the `k²` CEILING rather than the floor — the diagonal structure saturates
  KS = a handle.
- **What refutes the ESCAPE hypothesis (⇒ reduction confirmed):** `C_k ≈ NULL-A floor` at every
  in-power `(k,p)`, `k`-independent at fixed `p` (Correction 1), decaying `∝ p^{−1/2}` (matched to the
  floor with NO fitted exponent — DRILL 01 discipline), planted control FIRES, ceiling never violated,
  μ₆-aligned pairs sit at the plain degree-3 NULL-C floor.
- **Void condition (neither branch):** planted control does not FIRE at `ρ=4·floor`/`ρ=0.10`, OR
  `Q_k≠1`, OR `ρ=0` fires — the null is uninformative; report void, no verdict.

---

## 8. PRE-COMMITMENT  (what we conclude for EACH outcome — filled BEFORE the run)

| Outcome | Pre-committed conclusion (with power + scope; null branch is a MAGNITUDE) |
|---|---|
| **CONFIRMS-REDUCTION:** structured `C_k ≈ NULL-A floor` at all in-power `(k,p)`; `k`-independent at fixed `p`; decays `∝ p^{−1/2}` (matched, no fit); μ₆ pairs at degree-3 floor; ceiling `C_k·n ≤ (2D_k+1)√p` never violated; planted FIRES at `ρ_min`. | Report: **"Structured pairs at fixed `k` are KS-covered at the tested scale: `C_k` sits at the degree-matched random-readout floor `≈√(ln n)·p^{−1/2}`, magnitude bounded by the KS ceiling `≈c·k²·p^{−1/2}`, on `E:y²=x³+7`, `p∈[200,10⁵]`, `k≤64`, planted power `ρ_min` per cell. §X.7's structured-pair sub-object is closed **given KS via the bounded-degree diagonal reduction** for fixed `k` at this scale. Residual OPEN and NAMED: (i) `k ≳ p^{1/4}` — the unbounded-degree GAP; (ii) the `m=1` aligned readout — the DLP; (iii) `p=2^256` (SCALE BANNER, zero power here)."** Move frontier-7's structured-pair clause to `bounded-by PREREG_structured_pair_bilinear_v1` for fixed `k`; keep (i)(ii)(iii) OPEN verbatim. |
| **ESCAPE:** in-power `C_k` exceeds floor beyond planted threshold and does not decay with `p`. | Report: **"A structured-pair handle at multiplier(s) `k=…`, `p=…`: normalized correlation `C_k=…` exceeds the degree-matched floor by factor `…` (power `ρ_min`, scope `E:y²=x³+7`, prime order, this `p`), persisting/growing across the `p`-ladder — a diagonal `v=k·u` readout **not covered by the fixed-`k` KS reduction**. §X.7 stays OPEN with this NAMED object; next probe = its symmetry type / which `a'` carries it / its μ₃-GLV grading."** State as a magnitude with power+scope; **forbidden** to write "no signal" or "closed" for either branch. Anomaly-Drill protocol then applies (characterize, do not verdict). |
| **VOID:** planted silent at `ρ=4·floor`/`0.10`, or `Q_k≠1`, or `ρ=0` fires. | Report: **"Uninformative — the statistic failed its own positive/normalization control at `(p,k)=…`; no confirm/escape verdict. Fix the estimator (Parseval `Q_k`, plant recovery) and re-run."** No structural claim either way. |
| **MIXED / partial:** confirms at small `k`, only-FLOOR cells at large `k` (ceiling vacuous). | Report per-cell: floor-test result for ALL `(k,p)` (valid everywhere) + ceiling result ONLY for `CEILING-IN-POWER` cells; explicitly mark `k=16,32,64` at small `p` as **FLOOR-tested, ceiling-untested** (finite-size, §5). No global verdict beyond the in-power cells. |

---

## 9. Implementation pointers (so the run reuses exact infrastructure, not new float paths)
- Curve + generator + prime order: `prime_order_curve(lo,hi,0,7)`, `orbit(G,p,n,0)` — `t_y_maxbound_v1.py`.
- Single-index FFT of a phase vector: `U_row`-style `numpy.fft.fft` over `d` — `xy_interference_U_v1.py`.
- GLV `λ,β`: the cube-root detection block in `xy_interference_U_v1.py` (`x_{λd}=βx_d`).
- Fixed readout coefficients `(3,1,5,2,7,4)`: `difference_set_closure_verify_v1.py` line 14.
- KS citation + scope (additive ψ only; NOT χ₂): master Appendix C / §XI.10; SHA-256 `645d9022e029…5d8d2a`.
- New script (to be written AFTER this spec is locked): `structured_pair_bilinear_v1.py`.
