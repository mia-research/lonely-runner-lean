# PREREG — Individual Frobenius eigenvalues of A_new via the quantum number m
**File:** `PREREG_mu4_eigenvalue_individual_v1.md`  **Date:** 2026-07-20  **Status:** PRE-RUN. No out-of-sample row has been computed.

**Provenance of the hypothesis (declared IN-SAMPLE).** H1 and H2 below were formed by reading the
rows of `supersingular_mu4_mechanism_v1.log` (6 cubics x 42 primes, 13 <= p <= 199). Those rows are
**training data** and may never be counted as evidence for H1/H2. Every number this run reports as
evidence must come from the out-of-sample window in §6.

---

## 1. OBJECT

For a separable cubic `f` over `F_p`, the curves
`C : w^4 = f(x)`, `E : y^2 = f(x)`, with `Jac(C) ~ E x A_new`, `dim A_new = 2`.
The object is **the multiset of the four Frobenius eigenvalues of `Frob_p` acting on `H^1(A_new)`**,
i.e. the roots of `char(t) = t^4 + b1 t^3 + b2 t^2 + p b1 t + p^2`, where
`L_new(T) = 1 + b1 T + b2 T^2 + p b1 T^3 + p^2 T^4`.

Established already (in-sample, 42/42 rows, all 6 cubics, with the mu4 argument): for `p = 3 mod 4`,
`b1 = 0` and `b2 = m p` with `m` in `{-2,-1,0,1,2}`. Then `t = sqrt(p) z` gives `z^4 + m z^2 + 1 = 0`,
so the **individual** eigenvalues are `sqrt(p) * (root of unity)` with the order named by `m`.

**Tautology check.** The feature (`B` mod cubic/quadratic characters, `p mod 12`) and the target
(`m`, from integer point counts of `C` and `E`) are computed by disjoint code paths from disjoint
inputs. `m` is not a function of the feature by construction. No tautology risk of the
`r = v - w` vs `w` type. `b1 = 0` **is** forced (mu4 argument) and is therefore *not* evidence — see §4.

---

## 2. STATISTIC

**Exactly one per row:** the integer
```
m(f, p) := b2 / p          (row is valid only if p | b2 ; b2 from exact F_p, F_{p^2} point counts)
```
Row key = `(f, p)`. A row is a single integer. No maxima, no sweeps, no thresholds.

**Derived readout (deterministic function of `m`, not a second statistic).** The four eigenvalues are
`alpha = sqrt(p) * exp(i pi theta)` with `theta` the exact rationals:

| m  | z-polynomial      | theta (multiples of pi), as exact `Fraction` | root-of-unity order |
|----|-------------------|----------------------------------------------|---------------------|
| -2 | `(z^2-1)^2`       | `0, 0, 1, 1`                                 | 1 and 2 (each double)|
| -1 | `Phi_12 = z^4-z^2+1` | `1/6, -1/6, 5/6, -5/6`                    | 12 (primitive)      |
| 0  | `Phi_8 = z^4+1`   | `1/4, -1/4, 3/4, -3/4`                       | 8 (primitive)       |
| 1  | `Phi_3 Phi_6`     | `2/3, -2/3, 1/3, -1/3`                       | 3 and 6             |
| 2  | `(z^2+1)^2`       | `1/2, -1/2, 1/2, -1/2`                       | 4 (each double)     |

The run MUST print `theta` as `Fraction` objects taken from this table by table lookup on `m`.
It MUST NOT obtain `theta` by numerical root-finding (see §8).

**Null distribution of the statistic:** see §5.

---

## 3. HYPOTHESES (frozen)

Scope of H1/H2: **the three j=0 (CM) cubics `f = x^3 + B`, `B in {7, 2, 11}`, at `p = 3 mod 4`.**

- **H1.** `p = 11 mod 12`  =>  `m = 2`.
- **H2.** `p = 7 mod 12`   =>  `m = -2` if `B^((p-1)/3) = 1 mod p` (B a cubic residue),
                                `m = 1`  otherwise.
- **H2b (rider, tested by the same rows).** Within `p = 7 mod 12`, `m` depends on `B` **only**
  through the cubic character. Decidable form: any two rows with the same `p` and the same cubic
  class but *different* quadratic class `B^((p-1)/2)` must have equal `m`.

**Exploratory arm (cannot confirm or refute anything).** The three non-CM cubics
`x^3+2x+5`, `x^3+x+1`, `x^3-x+3`. **No hypothesis is offered for them.** Their `m` values are
RECORDED in the output table and reported under a heading `EXPLORATORY — no prediction`. They may
not be used to support or attack H1/H2, and no rule for them may be stated in this run's write-up
(any pattern noticed there requires its own prereg and its own fresh window).

---

## 4. UNFORCED ROWS AND DISTINCT CONFIGURATIONS

**Forced, contributes zero information (report but do not count):**
- `b1 = 0` at `p = 3 mod 4` — forced by the mu4 conjugation argument, already 42/42 in-sample.
- `|m| <= 2` given supersingularity — a Weil/Newton-polygon constraint, not a prediction of this run.
- No row is dropped for singular reduction: `4A^3+27B^2 = 27B^2` and `p > 200 > B` for `B in {7,2,11}`,
  so **no skips are expected**. If the run skips any row it must print the row key and reason.

**Rows are NOT independent configurations.** `C : w^4 = x^3 + B` depends on `B` only modulo 12th
powers (`x -> t^4 x`, `w -> t^3 w` sends `B -> B/t^12`). With `g = gcd(12, p-1)`:
- `p = 11 mod 12` => `g = 2`: `B` matters only through the **Legendre symbol**. Three cubics collapse
  to at most 2 classes per prime.
- `p = 7 mod 12` => `g = 6`: `B` matters only through the **(cubic, quadratic) character pair**.

Pre-committed configuration counts for the §6 window (computed from the scope alone — no `m` value
was used):

| arm | primes | rows | DISTINCT configurations |
|---|---|---|---|
| H1 (`p=11 mod 12`) | 14 | 42 | **K1 = 26** distinct `(p, Legendre(B|p))` |
| H2 (`p=7 mod 12`), main | 12 | 36 | **K2 = 22** distinct `(p, cubic class of B)` |
| H2b rider (extra resolution) | — | — | 29 distinct `(p, (cubic, quad))` => **7** configs test H2b |

H2 cell sizes: cubic-residue rows = 12 (over 10 distinct primes), split by B as `{7: 6, 2: 5, 11: 1}`;
non-residue rows = 24 (over 12 distinct primes). **The `m = -2` cell rests on 12 rows, of which B=11
contributes 1.** The run must print this per-B breakdown next to any H2 pass rate.

The run MUST print, per arm, both `rows_checked` and `distinct_configs`, and MUST use
`distinct_configs` in every significance statement.

---

## 5. MATCHED CONTROL (the chi4-sum identity) — the FIRING control

Because `b1 = 0`: `P1 = 0`, so `e2 = -P2/2` and `b2 = -P2/2` with
`P2 = a_{p^2}(C) - a_{p^2}(E)`. Counting 4th roots over `F_{p^2}` (`p^2 = 1 mod 4`) gives the claimed
identity
```
m = Re(S) / p ,      S = sum over x in F_{p^2} of chi4(f(x)) ,   chi4 a quartic character, chi4(0)=0.
```
**Implementation requirement (binding).** `m_chi4` must be computed by a **separate function with its
own enumeration of `F_{p^2}`**, taking `f` and `p` as its only inputs. It may NOT read `b2`, `P2`,
`aC`, `aE`, `L_new`, or any intermediate of the §2 path. Exact integer form (no character lift needed,
`Re(S)` is independent of the embedding `mu4(F_q) -> mu4(C)` because the two embeddings conjugate `S`):
```
q = p^2 ;  e = (q-1)/4
N_plus  = #{ x in F_q : f(x) != 0 and f(x)^e = 1 }
N_minus = #{ x in F_q : f(x) != 0 and f(x)^e = -1 }
m_chi4 := (N_plus - N_minus) / p
```
**What the control preserves:** the same curve, same prime, same field, same object. **What it
destroys:** nothing about the arithmetic — it is an *independent route to the same integer*, not a
randomization. It is the right null here because the risk being controlled is a broken readout
(mis-derived `b2`, off-by-one point at infinity, wrong `L_E` split), not a chance pattern; the chance
pattern is handled by §5b/§7.

**Control pass/fail, per row:** `p | (N_plus - N_minus)` AND `m_chi4 == m`.
- **Pass condition:** exact agreement on **100% of rows in the window (all 6 cubics, 156 rows), and
  additionally on 30 in-sample rows re-run from 13..199** (the re-run rows are a readout check only,
  never evidence for H1/H2).
- **FAIL on any single row => the readout is broken. No verdict on H1, H2, H2b, or the exploratory
  arm may be reported. The run's only output is the disagreement table.**

### 5b. PLANTED CONTROL (positive control — the test must fire)

All three plants are run and their outcomes printed BEFORE the H1/H2 verdict block.

1. **Mutated-hypothesis plant.** Evaluate the deliberately false `H1' : p = 11 mod 12 => m = 1`
   against the same rows. The verdict machinery MUST report `H1'` FAILED with a nonzero violation
   count. If `H1'` passes, the comparator is broken; halt.
2. **Perturbed-object plant.** Run the chi4 route on `f'(x) = f(x) + 1` while running the `b2` route
   on `f`, for 3 named rows (`(B,p) = (7,211), (2,227), (11,239)`). The control MUST report
   disagreement on at least 1 of the 3. If it agrees on all 3, the control cannot fire; halt.
3. **Even-char-poly plant.** Include 4 primes `p = 1 mod 4` (`p = 229, 233, 241, 257`) for `B = 7`.
   The pipeline MUST report `b1 != 0` on at least one of them (in-sample `p=1 mod 4` rows show
   `b1 != 0`), confirming that the `b1 = 0` column is a measurement and not a hard-coded constant.
   These 4 rows are diagnostic only and are excluded from H1/H2/H2b counts.

---

## 6. SCOPE (every number this run prints inherits this string)

```
6 cubics {x^3+7, x^3+2, x^3+11, x^3+2x+5, x^3+x+1, x^3-x+3};
primes p = 3 mod 4 with 200 < p < 500  (26 primes; 14 with p=11 mod 12, 12 with p=7 mod 12);
m = b2/p for A_new = new part of Jac(w^4=f), from exact integer point counts over F_p and F_{p^2}.
```
This window is **strictly disjoint** from the in-sample window `13 <= p <= 199`.
Row totals: **156** (26 primes x 6 cubics), of which **78 CM rows** carry H1/H2/H2b and **78 non-CM
rows are exploratory**. Plus 4 diagnostic `p = 1 mod 4` rows (§5b.3).

**Cost.** The `F_{p^2}` loop is `O(p^2)`. `sum p^2` over the 26 primes = `3.60e6` field elements per
cubic; x6 cubics = `2.16e7`, and the independent chi4 route doubles it to `~4.3e7` exponentiations in
`F_{p^2}`. Order-of-magnitude budget: tens of minutes in Sage.

**Only permitted truncation** (must be disclosed in the output header, all-or-nothing, from the top):
window shrinks to `200 < p < 400` (`sum p^2 = 1.46e6`; 8+8 primes; `K1 = 16`, `K2 = 14`). No other
truncation, no per-row dropping, no per-cubic dropping. **Any row that is computed must be printed.**
A truncated run is reportable only if the §7 adequacy bar still holds.

---

## 7. POWER AND ADEQUACY

**Null model (pre-committed).** Under H0, `m` on a `p = 3 mod 4` CM row is drawn uniformly from the
support observed in-sample for CM curves, `S = {-2, 1, 2}` (`|S| = 3`; using the smaller observed
support rather than all of `{-2..2}` is the conservative choice), independently across **distinct
configurations** (§4), not across rows.

| arm | distinct configs K | P(all K match | H0) |
|---|---|---|---|
| H1 | 26 | `3^-26 = 4.0e-13` |
| H2 | 22 | `3^-22 = 3.2e-11` |
| H2b | 7 | `3^-7 = 4.6e-4` |
| truncated window (400) H1 / H2 | 16 / 14 | `2.2e-8` / `2.1e-7` |

**Adequacy bar (pre-committed):** an arm is reportable only if `K >= 10` for that arm
(`3^-10 = 1.7e-5`). H1 (26) and H2 (22) clear it in both the full and truncated windows; H2b (7) does
**not** — H2b is therefore pre-declared **underpowered**, and a H2b pass must be reported as
"consistent, K=7, null prob 4.6e-4, underpowered" and never as a confirmed independence.

**Detectable effect size.** With K configs the test detects any deviation affecting `>= 1`
configuration — i.e. it has power 1 against "H1/H2 wrong on any single configuration", and power
`1 - (1/3)^K`-ish against a random alternative. It has **zero power** to distinguish H1/H2 from any
rule that agrees with them on this window (e.g. a rule keyed to `p mod 24`, or to the quartic
character of `B`). That indistinguishability is stated as a limitation regardless of outcome.

**What a pass does NOT establish** (must be copied verbatim into the run's conclusion):
- It is an **empirical law over 200 < p < 500**, tagged `[EMPIRICAL]`, not `[PROVED]`.
- It does **not** transfer to `p = 2^256 - 2^32 - 977`. No statement about secp256k1's `m`, its
  eigenvalues, or its supersingularity may be made from this run. (The scale-free part of the mu4
  story is `b1 = 0`; the value of `m` is **not** covered by that argument and is exactly what this
  run leaves open at large `p`.)
- It says nothing about ECDLP, key recovery, or security (§9).

---

## 8. EXACTNESS

- Signal path is Sage `Integer` / `GF(p)` / `GF(p^2)` arithmetic and Python `int`. Point counts,
  `aC`, `aE`, `P1`, `P2`, `e1`, `e2`, `b1`, `b2`, `m`, `N_plus`, `N_minus`, `m_chi4` are all exact
  integers. Divisions are exact-divisibility-checked (`b2 % p == 0`, `(N_plus-N_minus) % p == 0`)
  before `//`. Angles are `fractions.Fraction`. `check_no_float.sh` must pass before the run.
- **Named float carve-out — REMOVED, not carved out.** `supersingular_mu4_mechanism_v1.py`'s
  `roots_are_sqrtp_zeta()` uses `QQbar` root-finding and the float test `(abs(z)-1).abs() < 1e-9`.
  That path is **banned from the verdict path** in this run. The root-of-unity structure is obtained
  by table lookup on the integer `m` (§2). If the QQbar column is printed at all it is labelled
  `informational, not used for any pass/fail`.
- No `float()`, `/`, `**0.5`, `math.*` anywhere a row's `m` or a pass/fail depends on it.

---

## 9. FALSIFICATION, AND THE PARTIAL-RATE RULE

**Falsified if:** any single CM row in the §6 window has `m != ` the H1/H2 prediction, with the chi4
control passing on that row. One violation falsifies the hypothesis **as stated**. There is no
"mostly holds" verdict.

**Pre-committed handling of a partial rate (no post-hoc rescue).** If H2 fails on some rows and holds
on others, the run MUST, in this order and before any explanation:
1. print the raw split as `a/b` per cell of the pre-committed covariate grid, and only that grid:
   `{B} x {p mod 12} x {cubic class of B} x {quadratic class of B} x {gcd(12, p-1)}`;
2. report the split by DISTINCT CONFIGURATIONS as well as rows;
3. stop. **No covariate outside that grid may be introduced in this run's write-up.** Any new
   covariate that appears to explain the split is a NEW hypothesis requiring its own prereg and a
   fresh window (`500 < p < 700` is reserved for that purpose and must not be touched by this run).

**A failure is not a closure.** `m` is a coarse invariant: it names the multiset of eigenvalue angles
and nothing finer. If H1/H2 fail, the pre-committed next probe (named now, so it cannot be chosen
post hoc) is the finer data the run should then record for the failing rows: the factorization of
`char(t)` over `Q`, the `F_p`-isogeny decomposition of `A_new`, and the pair `(m, twist class of B in
F_p*/(F_p*)^g)`. Failure of the `m`-level rule means the effect is not on the `m` projection; it does
not mean there is no rule.

---

## 10. PRE-COMMITMENT TABLE (filled in BEFORE the run)

| # | Outcome | Pre-committed conclusion |
|---|---|---|
| 0 | chi4 control disagrees on >= 1 row, OR any §5b plant fails to fire | **Readout broken / control uninformative.** Report only the disagreement table. **No** statement about H1, H2, H2b, or the exploratory arm. Nothing about eigenvalues is reported. |
| 1 | Control passes; H1 holds 42/42 rows (K1=26) and H2 holds 36/36 rows (K2=22) | `[EMPIRICAL]` **Characterization:** for `f = x^3+B`, `B in {7,2,11}`, `200<p<500`, `p=3 mod 4`, the individual Frobenius eigenvalues of `A_new` are `sqrt(p)*zeta` with `zeta` of order 4 when `p=11 mod 12`; of order 1 and 2 when `p=7 mod 12` and `B` is a cubic residue; of order 3 and 6 otherwise. Null prob `3^-26` / `3^-22` over distinct configurations. Tagged EMPIRICAL, scoped to the window, explicitly **not** transferred to secp256k1. Next step named: an analytic derivation (Jacobi-sum / CM evaluation of `S`), which is what would upgrade the tag. |
| 2 | Control passes; H1 holds, H2 fails on >= 1 row | **H2 is FALSIFIED as stated.** H1 reported as in row 1 (its own arm, its own K). H2 reported as falsified with the §9 covariate split printed and **no** explanation attached. |
| 3 | Control passes; H1 fails on >= 1 row | **H1 is FALSIFIED as stated.** Report the violating `(B,p,m)` rows and the §9 grid. H2 adjudicated independently on its own rows. |
| 4 | Control passes; both fail | Both falsified as stated; report both grids; the §9 "failure is not a closure" clause applies and the finer invariants are recorded for the failing rows. |
| 5 | H2b: rows with equal `(p, cubic class)` but different quadratic class disagree in `m` | H2's stated covariate is **incomplete**: `m` depends on more than the cubic character. Report as a refinement of scope (the twist class matters), not as a failure of the eigenvalue characterization. |
| 6 | Any `p = 3 mod 4` row has `b1 != 0` or `p` does not divide `b2` | Report immediately as a violation of the in-sample-established CLAIM(A)/(B) at larger `p`; this supersedes all other outcomes and is reported as the headline, with the row keys. |
| 7 | Exploratory (non-CM) arm shows any pattern | Recorded under `EXPLORATORY — no prediction`. **No rule is stated, no significance is computed, no conclusion is drawn.** It requires its own prereg and the reserved `500<p<700` window. |

**Output-type pre-commitment (binding, all outcomes).** The output of this run is a
**characterization** — which individual eigenvalue occurs (as an exact rational angle), under which
arithmetic condition on `(B, p)`, over the stated window — together with the null probability over
distinct configurations. It is **never** a verdict about ECDLP, about secp256k1's security, or about
any avenue being open or closed. The words "closes", "rules out", "secure", "no structure", and
"break" may not appear in the run's conclusion.
