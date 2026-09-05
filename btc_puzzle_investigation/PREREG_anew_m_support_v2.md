# PREREG v2 — realized support of `m = b₂/p`; does `m = −1` occur? (SUPERSEDES v1)

**Written 2026-08-02. No `m`-support script has been executed. v1 was submitted to the
`experiment-designer` gate before freezing; the gate returned 14 mechanical + 10 frame findings, six
of them blocking. v2 applies them. v1 is retained unmodified so the amendment is auditable.**
Amendments are marked `[G:id]` against the finding they answer. Everything in v1 not listed here is
carried unchanged.

---

## 0. The independent theory leg has ALREADY RETURNED — and it kills one branch of v1 §0

v1 §5 posed the Honda–Tate question as open. It has since been answered by a `citation-verifier` run
(2026-08-02), **before** any measurement:

> **All five `m ∈ {−2,−1,0,1,2}` are realized as characteristic polynomials of abelian surfaces over
> `F_p`, for `p > 3`, `p ≡ 3 mod 4`.** For `m = −1` the class is a **simple** surface of dimension
> **2, not 4**: `π` is a root of `x⁴ − px² + p²`, `K = ℚ(π) = ℚ(√−3, √−p)` is quartic CM, every local
> invariant above `p` vanishes (`v(π)/v(q) = 1/2` times an even local degree, at both `p ≡ 7` and
> `p ≡ 11 mod 12`), so `e = 1` and `dim = 1·4/2 = 2`.
> Sources: Singh–McGuire–Zaytsev Thm 12.1(2)(a) (`n` odd = our `q = p`); Howe–Nart–Ritzenthaler
> Table 10.1 + Thm 10.1; own Honda–Tate computation calibrated against Waterhouse Thm 4.1, 29 primes.
> HNR Thm 10.1 further gives: `q = p` is never a square, so **every** simple supersingular isogeny
> class over `F_p` contains a Jacobian — the `m = −1` class is populated by a genus-2 Jacobian.
> Weakest link, carried: for `m = ±1` at `p ≡ 7 mod 12` the only published support held is the SMZ
> preprint; Xing and Maisner–Nart Table 1 were **not obtained**.

**Consequences, fixed before data `[G:F2]`:**

1. **v1 §0's "not realizable ⇒ `g = 2 ⟺ m = +1`, which shortens the anchor's dependence on Katre
   caveat 1" is STRUCK.** `m = −1` *is* realizable by a surface. Only the theory leg could have
   shortened that dependence, and it has returned the opposite. **No outcome of this run shortens the
   anchor's dependence on Katre caveat 1.** v1 slid from "realized" (family) to "realizable"
   (any surface); the two are now kept apart by construction.
2. The measurement's meaning is **sharpened**: a null is now a fact about **our family `w⁴ = f`**,
   not a triviality about abelian surfaces. There is no a-priori obstruction to find.
3. v1 §0's *"realized ⇒ a second lock family, **reached by covers outside `x³+B`**"* — the clause in
   bold is **STRUCK** `[G:F3]`. Where a hit lives is an outcome, not a premise.

---

## 1. Object amendments

- **`b₁` SIGN CORRECTED `[G:M2]`.** v1 wrote `b₁ = #E(F_p) − #C(F_p)`. From `L_C = L_E·L_new` the
  correct relation is **`b₁ = #C(F_p) − #E(F_p)`**. Gate artifact: at `p = 13`, `f = x³+7`, true
  `b₁ = −6`, v1's formula gives `+6`; 3 flipped rows, exactly those with `b₁ ≠ 0`. **The reused
  artifact `anew_cartier_audit_v2.sage:190` carries the same flip** and its printed `b1` therefore has
  the wrong sign on the `p ≡ 1 mod 4` arm. `b₂` is unaffected (it uses `b₁²`), and the
  supersingularity gate is unaffected (it uses `b₁ mod p`), so **no `m` value reported by the earlier
  run changes**. Recorded, corrected here, and flagged for the earlier artifact.
- **`b₁ = 0` is a PREMISE, not an omission `[G:M3]`.** The normalization `z⁴ + mz² + 1`, the a-priori
  range `{−2,−1,0,1,2}`, and T3's `g = 2 ⟺ m = ±1` **all require `b₁ = 0`**. With `b₁ ≠ 0`, Weil
  gives `b₂ = 2p + a₁a₂` with `|aᵢ| ≤ 2√p`, so `m ∈ [−2, 6]`; the gate exhibits a Weil-admissible
  `m = 3` at `p = 13`. On the MAIN arm `b₁ = 0` is `[VERIFIED 42/42]` + argued
  (`RESULT_mu6_cohomology_supersingular_v2.md:86`) and, since 2026-08-02, follows from the reviewed
  Cartier derivation. **`b₁` is now a reported quantity per row**, and `b₁ ≠ 0` on a MAIN-arm row is
  an outcome with its own row in §6.
- **CM-type criterion WRITTEN OUT `[G:M10, F4]`:** **CM-type ⟺ `cover_class(p,f)[0] == 0`**, i.e. the
  depressed cubic has zero linear term, i.e. the cover is isomorphic to some `w⁴ = x³+B`. Gate
  artifact: exhaustive at `p ∈ {11,19,23,31}`, `{labels of the x³+B family} == {labels with first
  coordinate 0}` — **equal at all four**. Decidable from the label alone; no separate test needed.
- **`cover_class` is SOUND AND COMPLETE `[G:M9]`.** Gate artifact: exhaustive enumeration of all
  separable cubics at `p ∈ {11,19,23,31}` (12100 / 116964 / 256036 / 864900 cubics) — the label
  partition **equals** the true orbit partition under `f ↦ c·f(αx+β)`, `c ∈ (F_p*)⁴`, at every prime
  (22/42/46/66 classes). Completeness is the direction the power bound depends on; it is verified, at
  those four primes only.

---

## 2. Hypotheses (amended `[G:F8, F10]`)

- **H1 (promoted to primary).** **Does `m = −1` occur on a `p ≡ 3 mod 4` cover class of `w⁴ = f`?**
  v1's headline ("the realized support is a proper subset") is demoted to background — it is *already
  true* from `RESULT_mu6_cohomology_supersingular_v2.md:101` and could only be falsified by all five
  values appearing, so it was not a hypothesis.
- **H2 (tagged).** *Out-of-sample replication* of `:101`'s non-CM support `{−2,0,1,2}` on a disjoint
  prime set — **not a new measurement**. Falsifier: any non-CM class with `m ∉ {−2,0,1,2}`.
- **H3 (now measurable).** Within CM-type, the support is determined by `p mod 12` and the cubic
  residue symbol `χ₃(B)`. v1 asserted this but computed no residue symbol. **`χ₃(B)` is now computed
  and reported for every CM-type class.** Falsifier: two CM classes at one prime with equal
  `(p mod 12, χ₃(B))` and different `m`.

---

## 3. Statistic and sampling (amended)

Per `(p,f)`: exact `#C, #E` over `F_p` and `F_{p²}`; `b₁ = #C(F_p) − #E(F_p)`;
`b₂ = (b₁² − (s₂C − s₂E))/2`; `m = b₂/p` **only if `p ∣ b₂`**, else `UNDEFINED`. Also per row: `b₁`,
the Cartier new-part stable rank, `cover_class` label, CM-type flag, and `χ₃(B)` for CM rows.

**Counting method `[G:M13]`.** `#C(F_{p²})` is computed by an exact **numpy int64** counter, not the
`O(p²)` Sage loop the gate timed (which projects to 4.6 days and is why v1's sample was infeasible).
int64 is exact integer arithmetic; an overflow guard `(p−1)² + d(p−1)² < 2⁶²` is asserted per prime.
**Measured, not extrapolated:** at `p = 2467`, table 0.17s, 0.163s per cubic, peak RSS 481 MB;
projected **~25 min for both arms**. The stated sample is therefore feasible as written.

**Stratified sampling `[G:M12]` — the CM stratum is now EXHAUSTIVE, not sampled.** CM-type classes are
only `2` (at `p ≡ 11 mod 12`) or `6` (at `p ≡ 7 mod 12`) per prime — index `lcm(gcd(3,p−1),
gcd(4,p−1))` in `F_p*`. v1's 40 random cubics per prime would have supplied **~2.3 CM rows across the
entire 96-prime arm** (CM-type is a `1/p` fraction of cubics), leaving 50–83% of CM classes at
`p ≡ 7 mod 12` — the class the disputed `:112` claim lives in — with **no power at all**.

> **Per prime: enumerate ALL CM-type classes exhaustively** (iterate `B ∈ F_p*`, dedup by
> `cover_class`), **plus 40 seeded-random general cubics** for the non-CM stratum.

This converts the CM arm from a weak null into a **complete census over the sampled primes**.

**Sample.** MAIN: the 96 primes `p ≡ 3 mod 4` in `(1039, 2500)` — disjoint from every prior sample.
CONTROL: `p ≡ 1 mod 4` in `(1033, 2500)`. Seed **`20260804`**. Exclusions (`disc f ≡ 0 mod p`) derived
from the sample, never copied, and reported with `N`.

**Power, restated conservatively `[G:M11]`.** The algebra `q ≤ 1 − 0.05^{1/N}` is correct, but
independence is not: H3 asserts `m` is largely a function of `p`, so classes at one prime are not
independent draws. Pre-committed:

| stratum | what is reported | headline bound |
|---|---|---|
| **CM-type** | a **complete census** at all 96 primes — every CM class observed | no sampling bound needed *within* the sampled primes; extrapolation beyond them is not claimed |
| **non-CM** | 40 classes sampled per prime out of `≈2p` | **`N_eff = 96` primes ⇒ `q ≤ 3.07%`** is the headline |
| non-CM, class-level | `N ≈ 3840` ⇒ `q ≤ 0.078%` | reported **only if** the run demonstrates within-prime variation of `m`, measured as the number of primes at which ≥2 distinct `m` occur |

`N_primes` is stated alongside `N_classes` on every bound. **The 20× weaker prime-based bound is the
headline**; v1's `q ≲ 0.15%` is withdrawn.

**Float carve-out `[G:M14]`.** The signal path is exact throughout (integers, `GF(p)`, `ZZ`). The sole
float is the power bound `q = 1 − 0.05^{1/N}` — analytic sizing, no key or feature in path.

---

## 4. Controls and guards — relabelled honestly

The gate's central finding: **three of v1's four "controls" were guards whose pass is forced.** This
is the same defect class logged three times already on this project, and v1 reproduced it in controls
written *in response to* the previous instance. Relabelled:

| id | type | statement | pass condition |
|---|---|---|---|
| **K1** | **control** | Synthetic-input: feed `extract_m` counts built backwards from each `m ∈ {−2,−1,0,1,2}`; it must report that `m`. Pure integer fixture — **no surface is presupposed**, hence no circularity `[G:M6]`. **Scope, stated:** exercises only the `b₂` expression, *not* `counts()`, the sampler, or `cover_class`. | all five returned; else **VOID** |
| **K3a** | **control (REPLACES v1 K3) `[G:M8]`** | v1's K3 was **forced**: both instruments are constant on each arm (`p ≡ 3 mod 4` all supersingular, `p ≡ 1 mod 4` all ordinary), so a stub `srank_fake = 0 if p%4==3 else 1`, reading **no curve data at all**, passes at 100%. Replacement: **Manin's congruence `Tr(M) ≡ p+1−#C(F_p) (mod p)` on the `p ≡ 1 mod 4` arm.** There the grading gives `V₃ → V₃`, so the new-part block sits **on the diagonal and contributes to `Tr(M)`** — the same `cartier_matrix` code path the MAIN arm uses is therefore genuinely tested. (At `p ≡ 3 mod 4` the new part is off-diagonal and can *never* contribute to the trace, which is precisely why this control cannot live on the MAIN arm.) | **zero disagreements**, and `Tr(M) mod p` must take **≥5 distinct values** so a constant stub fails; else **VOID** |
| **K3b** | **control `[G:M8]`** | `D = 5`, `p ≡ 3 mod 4` planted arm, where `dim V₁ = 1` so new-part vanishing is **not** forced: the new-part block must come out **non-zero**, through the identical exponent arithmetic that returns zero at `D = 3`. This is what shows the MAIN-arm zero is a property of the object, not of the code. | non-zero on **≥5** planted rows; else **VOID** |
| | *amendment note, pre-data* | v2 first specified K3′ as "point-count verdict agrees with Cartier stable-rank verdict" on the `D=5` arm. **Withdrawn as infeasible**: the point-count `p`-rank verdict for a genus-6 curve needs `#C(F_{p^k})` for `k` up to 6, which is `O(p⁶)`. K3a + K3b replace it, are cheap, and both can fire. Recorded here rather than silently substituted. | |
| **K4′** | **control (two-sided) `[G:M9]`** | Labels must not merge non-isomorphic covers (v1's K4) **and** must not split isomorphic ones — the direction the power bound depends on. Brute-force orbit-partition check at `p ∈ {11,19,23}`. | partitions equal at all three; else class counts void, raw counts + prime-level bound only |
| G1 | **guard** (was "K2") `[G:M7]` | `m` UNDEFINED on the `p ≡ 1 mod 4` arm. **Not a firing control** — `p ∣ b₂` has probability `~1/p` there, so the true rate is `≈99.9%` and v1's 2/3 threshold could fail only under gross breakage (gate measured 131/131 = 100%). Guards against coercion/rounding of `m`. | **≥95%** UNDEFINED, with every DEFINED row listed individually |
| G2 | **guard** (was "K5") `[G:M10]` | CM-type detector: curated `x³+B` classify CM, random cubics mostly do not. Forced by construction once the criterion is written. | both halves |
| V1 | instrument check | numpy counters vs the Sage reference implementation | zero mismatches |

---

## 5. Outcome table — the six uncovered outcomes added `[G:F5, F6, F7, F9]`

| # | outcome | permitted | forbidden |
|---|---|---|---|
| 1 | `m = −1` on ≥1 MAIN-arm class | *"`m = −1` is realized at `(p,f) = …`; `g = 2` there by T3."* `[VERIFIED-INSTANCE]`. Report `p mod 12`, CM-type, `χ₃(B)`. | *"a second 120°-lock **branch**"* — a branch is a rule over `p` and the cubic and needs its own law-fit + OOS retest `[G:F6]` |
| 2 | no `m = −1`, K1 fired | *"`m = −1` occurs in at most `q` of non-CM classes (`N_eff = 96`, `q ≤ 3.07%`), and in **none** of the CM classes at the 96 sampled primes (complete census)."* | *"`m = −1` does not occur"*; any unqualified support claim; any statement about Katre caveat 1 (§0) |
| 3 | `m = 0` on a non-CM class | *"`:112`'s support claim is **over-scoped as written**: `m = 0` is realized at `(p,f) = …`."* A replication of `:101`, not a new measurement `[G:F10]`. | *"…and is correct for CM-type"* — that is a separate null needing row 4 `[G:F5]` |
| 4 | **no** CM class with `m ∉ {−2,1,2}` | *"the CM-type support is exactly `{−2,1,2}` at the 96 sampled primes — complete census, no within-prime sampling."* | extrapolating beyond the sampled primes |
| 5 | **a CM class with `m ∉ {−2,1,2}` at `p ≡ 7` or `11 mod 12`** | *"counterexample to the `m`-law H1/H2 at `(p,f) = …`"* `[VERIFIED-INSTANCE]`; **open a separate re-audit of the `m`-law** `[G:F9]` | re-deriving the `m`-law from this sample; restating its support in either direction |
| 6 | **`m` UNDEFINED on a MAIN-arm row** | **VOID-and-investigate.** This contradicts the reviewed supersingularity result — it is either a bug or a retraction of a proved claim `[G:F7.1]` | any support statement from that run |
| 7 | **`m` DEFINED but `∉ {−2,−1,0,1,2}`**, or **`b₁ ≠ 0` on a MAIN-arm row** | **VOID-and-investigate**; the a-priori range premise (§1) has failed `[G:F7.2, M3]` | reporting `m` as if the normalization held |
| 8 | `m = −1` only on the `p ≡ 1 mod 4` arm | report separately as a control-arm observation; the arm is ordinary and outside the object `[G:F7.4]` | reading it as a MAIN-arm finding |
| 9 | K4′ fails, K1 passes | raw row counts + **prime-level bound only**; all class-level `N` and `q` withdrawn `[G:F7.5]` | quoting any class-level bound |
| 10 | H3 falsified (two CM classes, same `(p mod 12, χ₃(B))`, different `m`) | report as a counterexample to H3 `[VERIFIED-INSTANCE]` | restating H3 in either direction |

**Scope, unchanged and binding.** Everything here is the **`a = 0` fibre**; this run has **zero power**
over any `a ≠ 0` cell and no outcome may be phrased as progress on uniformity. Nothing reaches
`p = 2²⁵⁶−2³²−977`; the `m` value at secp is a separate `[CONDITIONAL]` claim resting on the Jacobi
sign law and Katre caveat 1, **untouched by this run in either direction**.

---

*Frozen at first v2 script execution. Deviations → `PREREG_anew_m_support_v2_DEVIATIONS.md`.
If a control fires, the sample is contaminated and a disjoint v3 sample is required.*
