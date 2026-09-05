# AUDIT — PREREG_n1_v_sign_sweep_v2.md (pre-data)

**Date:** 2026-07-25 · **Mode:** pre-data audit of a frozen spec · **Target:** `PREREG_n1_v_sign_sweep_v2.md`
**Predecessor audit:** found F1–F7 + D5 on v1; v1 never run. v2 folds in all seven fixes plus one ADDITION.

## 0. VERDICT

**NOT RUNNABLE AS WRITTEN** — the mathematics, the seven fixes and every frozen number check out exactly, but the ADDITION's named decision procedure (Sturm) does not finish past roughly the 8th of the 50 primes, and one required control (M2b mutation (iv)) cannot be constructed. Three exact edits, all stated in §2, make it runnable in minutes.

---

## 1. Checks

### Check 1 (★★) — F3 exact reference values (p=43 quintic, p=13 e2/v) — **PASS, exact**

**Artifact:** `audit_n1_vsign_v2_core.py` (independent re-implementation of the instrument: my own
`F_{p^2}` arithmetic, my own group law, my own dlog table — no code reused from
`n1_twisted_eigenvalues_v1.sage`) + `audit_n1_vsign_v2_minpoly.py` (exact minimal polynomial in
`Z[x]/Phi_n`, all-integer). Signal path is pure `int`; no float anywhere in the derivation.

Definition used, taken from the instrument's own docstring and from F1:
`V_k(a) = sum_{P in E(F_{p^k})} chi2^{(k)}(y_P) zeta_n^{a*dlog(Tr_{k/1}P)}`, `E: y^2=x^3+7`,
`e2(a) = (V_1(a)^2 + V_2(a))/2`.

| claim in v2 | my recomputation | status |
|---|---|---|
| p=13: `e2 = -12` (rational) | `W = V1^2+V2 = [-14,10,10,10,10,10,10]` mod `x^7-1`; `sum_{i=1..6} zeta^i = -1` gives `2*e2 = -14-10 = -24`, `e2 = -12` | **exact match** |
| p=13: `v = -19/26` | p=13 ≡ 1 mod 4 = COS, `v=(e2-2p)/(4p) = (-12-26)/52 = -19/26` | **exact match** |
| p=43: `m_43(Y) = Y^5 - 60Y^4 - 2032Y^3 + 224768Y^2 - 5515008Y + 42288128` | coefficient vector (low→high) `[42288128, -5515008, 224768, -2032, -60, 1]`, computed as `prod_{reps}(Y - e2(a))` with coefficients carried in `Z[x]/Phi_31` and asserted rational at the end | **exact match, all six coefficients** |
| irreducible over `Q` | `sympy.factor_list` → single factor, multiplicity 1 | **PASS** |
| roots `-61.014, 16.796, 30.772, 33.972, 39.474` | exact isolating intervals `(-62,-61),(16,17),(30,31),(33,34),(39,40)`; refined `-61.013856, 16.795821, 30.771952, 33.972302, 39.473781` | **match to the printed 3 dp** |
| all roots `>= -2p = -86` | **Sturm/`count_roots(-oo,-86] ) = 0`** (exact, `m(-86) = -4514890400 < 0`, leading coeff `>0`, no sign change below) | **PASS, exactly** |
| exact `v` at the maximising class `= -0.14526827783269782` | `-(r+86)/172` at `r=-61.013856...` → `-0.14526827783269782068` | **match to all 17 quoted digits** |
| F3's premise that v1's 4-dp references were unachievable at `1e-9` | v1 quoted `-0.1451`; exact is `-0.145268277...`; gap `1.7e-4` | **F3's premise confirmed** |

Also independently confirmed (needed later): `e2(a)` is **exactly** `mu6`-invariant at both primes
(`sigma_m(W) == W` as integer vectors for all `m` in the order-6 subgroup: p=13 `mu6={1..6}`,
p=43 `mu6={1,5,6,25,26,30}`), so the count unit of F7 is correct as a matter of exact arithmetic,
not of observation.

**Additional exact values (not in v2, recorded for M1's use):** the five `v` at p=43 are
`-0.14526827783269782, -0.59765012072820740, -0.67890669607234053, -0.69751338623816552,
-0.72949872843091430` (display only; the exact objects are the roots of `m_43`). v1's transcribed
`-0.1451/-0.5977/-0.6788/-0.6976/-0.7295` differ from these in the 4th decimal at three of five cells.


### Check 2 (★★) — THE ADDITION: Sturm / total positivity

#### 2(a) Is total non-negativity EQUIVALENT to the per-cell claim? — **YES for the corrected pair, with four stated riders**

Audited in v2's own CORRECTED form: `e2+2p >= 0` (SIN) and `2p-e2 >= 0` (COS). *(The uncorrected
`∓(e2+2p)` form quoted in the audit brief is wrong for COS exactly as v2's ⚠⚠ block says; I confirm
that block independently — at p=13, `e2=-12`, `2p-e2 = 38 >= 0` is the true condition and
`-(e2+2p) = -14 < 0` would manufacture a counterexample. v2's correction is right.)*

**Proof of equivalence.** `e2(a) = (1/2) W(zeta_n^a)` with `W in Z[x]`, so `sigma_c(e2(1)) = e2(c)`:
the Galois conjugates of `e2(1)` over `Q` are precisely `{e2(c) : c = 1..n-1}`. `e2(1)` lies in the
`mu6`-fixed subfield, whose real embeddings are exactly the `(n-1)/6` distinct conjugates. "Totally
non-negative" = every conjugate `>= 0` = `e2(c) + 2p >= 0` for every `c != 0` = `v(c) <= 0` for every
`c != 0`. **No case is lost and none is gained.** Same for COS with `2p - e2`.

Four riders, each checked:

1. **Total reality is required and is FORCED, not observed.** `chi2^{(2)}(-1) = +1` gives
   `h2[d] = h2[-d]` so `V2(a) in R`; `chi2^{(1)}(-1) = (-1)^{(p-1)/2}` gives `h1` symmetric (COS,
   `V1` real) or antisymmetric (SIN, `V1` purely imaginary), so `V1(a)^2 in R` either way. Hence
   every `e2(a)` is real. Verified exactly at p=13 (`h1 = [0,-1,-1,-1,-1,-1,-1]` symmetric),
   p=43 (`h1` antisymmetric, `h1[0]=0`), and `m_p` totally real at p=13,43,127,163,211.
2. **`a = 0` is outside both statements** — `e2(0)` is the trivial-character value and is *not* a
   conjugate of `e2(1)`. The prereg's arms are over `a != 0`, so this is consistent; recorded because
   it means the ADDITION tests exactly the cells the per-cell claim covers, no more. (`e2(0) = 23` at
   p=13, `= 43` at p=43; both satisfy the criterion, but they are not part of the tested object.)
3. **★ The boundary `v = 0` is NOT resolved by the spec's wording, and resolving it wrongly is a
   false failure.** `v = 0` *satisfies* `v <= 0`. So the correct test is *strict*: for SIN, no root of
   `m_p` **strictly below** `-2p`. A root exactly at `-2p` means `v = 0` exactly, which **confirms**.
   v2 says only *"whether it has a root on the wrong side of `∓2p`"*, which does not say strict, and
   D5's residual instruction *"report `v = 0` or ABSTAIN"* would mis-file a confirming cell as an
   abstention. With `m_p in Z[Y]` the question `m_p(∓2p) = 0?` is an exact integer evaluation with no
   undecided outcome, so **abstention is never warranted under the ADDITION**. See check 9, gate G-BND.
4. **★ "minimal polynomial ... of degree `(n-1)/6`" is an assertion, not a theorem.** It holds iff the
   stabiliser of `e2(1)` in `(Z/n)^*` is exactly `mu6`. Verified irreducible of degree exactly
   `(n-1)/6` at p=13 (d=1), 43 (5), 127 (21), 163 (23), 211 (33). It is not guaranteed at all 50
   primes; if it ever fails, an implementation that asserts the degree **aborts on correct data**
   (see check 9, gate G-DEG). The root *set* is unaffected, so the fix is free: use the `mu6`-coset
   product `Q_p(Y) = prod_{cosets} (Y - e2(rep))`, always of degree `(n-1)/6`, equal to a power of
   `m_p`; counting its roots beyond the threshold *with multiplicity* is exactly F7's requested count.
5. **Integrality tension inside the ADDITION.** Line 103 says `e2(1) in (1/2)Z[zeta_n]`; line 107
   calls it an **algebraic integer**. Both cannot be hedged the same way. Measured: `W` is even at
   p=13, 43, 127, 163, 211 and every `m_p` came out **monic** in `Z[Y]`, so `e2(1) in Z[zeta_n]` and
   "algebraic integer" is correct at every prime tested. Recommend tightening line 103 to
   `Z[zeta_n]` with a per-prime assertion `all(W[i] % 2 == 0)`, which is free.

#### 2(b) Does the named route decide it with ZERO floats? — **YES for the two named steps; the unnamed step is where a float can enter**

- `e2(1)` as an integer vector: exact (`int` only). ✓
- Sturm on `m_p(X ∓ 2p) in Z[X]`: exact — `sympy`'s `count_roots` runs the Sturm sequence over `QQ`.
  Its answers agreed with ground truth at every degree I tested. ✓
- **The minimal-polynomial step has no algorithm named in v2.** That is the float hazard: the default
  route a reader reaches for (`numpy.roots` / high-precision root-finding, then round to integers)
  is a float path and violates the project rule. Two exact routes were implemented and cross-validated
  here: the coset product carried in `Z[x]/Phi_n` (`audit_n1_vsign_v2_minpoly.py`) and a multi-modular
  Gaussian-period + CRT algorithm (`audit_n1_vsign_v2_multimod.py`). Both reproduce `m_13`, `m_43`,
  `m_127` identically. **The spec must name one**; see the exact edit in §2 of this audit.

#### 2(c) ★ FEASIBILITY — **MEASURED. The sweep as written does not finish.**

All timings on this machine, CPython 3.14, single core. Stage A = `e2(1)` as an exact integer vector;
stage B = `m_p in Z[Y]`; stage C = the decision.

**Stage A — the spec's `O(n^2)` claim is CORRECT for this stage.**

| p | 127 | 211 | 349 | 547 |
|---|---|---|---|---|
| stage A (s) | 0.08 | 0.26 | 0.90 | 2.24 |

Fits `4.96e-6 * p^2`. Extrapolated `p=6007`: **~180 s**; all 50 primes: **~45 min**. Not a blocker.
*(Implementation note, not a spec defect: my stage A stores a `p^2`-entry square table — ~5 GB at
p=6007. A tower Tonelli-Shanks makes it `O(p)` memory. Any implementation must do this.)*

**Stage B — the spec asserts `O(n^2)` per prime. The min-poly step is NOT `O(n^2)`.**
Direct exact construction (coset product in `Z[x]/Phi_n`), measured:

| n | 127 | 199 | 313 | 547 |
|---|---|---|---|---|
| stage B (s) | 0.31 | 1.93 | 11.28 | 106.96 |

This is `1.192e-9 * n^4` to within 3% at all four points (predicted 0.31 / 1.87 / 11.44 / 106.68).
Extrapolated:

| p | 1669 | 3271 | 4513 | 6007 |
|---|---|---|---|---|
| stage B, direct | 2.5 h | 1.8 d | 6.2 d | **19.9 d** |

**Whole 50-prime sweep, direct stage B: 1.44e7 s = 167 days.**

**Stage B is rescued by an algorithm the spec does not name.** Because `e2(1)` is `mu6`-invariant its
coefficient vector is constant on `mu6`-cosets, so `e2 = (w0 + sum_j c_j eta_j)/2` in Gaussian periods
and the `d` conjugates are a **cyclic correlation** of `(c_j)` with `(eta_j)` — `O(d^2)` per modulus
instead of `O(n^2)`. Multi-modular + CRT, all integer, measured:

| p (n, d) | 547 (547, 91) | 1669 (1663, 277) | 2503 (2557, 426) | 3931 (4021, 670) | 4513 (4597, 766) | 6007 (6163, 1027) |
|---|---|---|---|---|---|---|
| stage B, multi-modular (s) | 0.04 | 1.06 | 3.63 | 15.71 | 23.99 | **55.40** |

Validated: reproduces `m_13`, `m_43` (the frozen quintic) and `m_127` exactly. **Whole sweep: minutes.**

**Stage C — ★ THIS IS THE BLOCKER. The Sturm sequence the ADDITION names does not scale.**
Measured on synthetic totally-real integer polynomials with the sweep's real `(d, coefficient bits)`:

| d | 20 | 21 | 50 | 52 | 100 / 102 |
|---|---|---|---|---|---|
| coeff bits | 162 | 174 | 487 | 504 | ~1000 |
| **Sturm (`count_roots`)** | 0.05 s | 0.07 s | 31.7 s | **53.7 s** | **> 3,400 s and > 3,000 s, both still running when the audit closed** |
| exact isolation (`intervals`) | — | 0.02 s | — | **0.22 s** | — |
| integer Taylor shift + Descartes | 1e-5 s | 4e-5 s | 1e-5 s | **4e-5 s** | — |

All three methods returned the **same** count at every degree tested. The empirical Sturm exponent from
(20, 0.05 s) and (50, 31.7 s) is `d^7.03`; it predicts (52, 42 s) against 53.7 s measured, and (100, 4,058 s) /
(102, 4,500 s) against the `>3,400 s` / `>3,000 s` lower bounds actually observed — consistent.
Extrapolating `T(d) ~ 0.05 * (d/20)^7`:

| p | 397 | 577 | 907 | 1237 | 2503 | 4513 | 6007 |
|---|---|---|---|---|---|---|---|
| d | 66 | 102 | 161 | 213 | 426 | 766 | 1027 |
| Sturm | 3.6 min | ~1.3 h | ~1.3 d | ~9 d | ~3 yr | **~190 yr** | **~1,500 yr** |

**Where it stops.** Against a 1-hour-per-prime budget the Sturm step becomes infeasible at
**p = 577 (the 8th prime of the frozen 40-list, d=102)**. Against a 1-day budget, at
**p = 907 (the 11th prime, d=161)**. **The 40-prime stratum cannot be completed, and the 10-prime
stratum-2 cannot be started, by the method the spec names.** The 40-list sum alone is thousands of
years.

**Stage C is also rescued, and the replacement is exact.** `m_p` is totally real (rider 1 above, forced),
and **for a real-rooted polynomial Descartes' rule of signs is exact, not an upper bound** (#pos = V(g),
#neg = V(g(-X)), and `V(g)+V(g(-X)) = deg g` supplies a free self-certificate that reality held).
So: integer Taylor shift `g(X) = m_p(X ∓ 2p)` (`O(d^2)` bigint ops, seconds at d=1027) followed by an
`O(d)` sign-change count decides the question exactly, float-free, in `4e-5 s` at d=52 — a factor
`1.3e6` faster than Sturm at that degree — **and it returns the COUNT, which is what F7 asks for.**

**Verdict on 2(c): NOT RUNNABLE AS WRITTEN. Runnable, in minutes, with two named algorithm
substitutions.** Both substitutions are exact-integer, so nothing about the no-float rule changes.

### Check 3 — F2 stratum-dependent criterion table — **conclusion PASS; one quoted decimal is wrong**

**Artifact:** `audit_n1_vsign_v2_k4.py` — full `V_1..V_4` reconstruction over `F_{p^k}` (generic
`F_p[t]/(f)`, irreducibility by `sympy`), giving `e1..e4` as exact integer vectors in `Z[x]/Phi_n`.
This is the direct, independent test of both rows, not a re-application of the dictionary.

**COS row (`p = 1 mod 4`), tested at p=13, `k=1..4` (all `13^4=28561` points of `E(F_{13^4})`):**
- `e1 = -1`, `e2 = -12` (both rational, `(n-1)/6 = 1`) — exact integer vectors.
- **`e3 = +p*e1` : TRUE exactly.** **`e4 = p^2 = 169` : TRUE exactly.**
  These are the two forced identities, and `e3 = +p*e1` (not `-p*e1`) is precisely the COS row's
  prediction. The row is confirmed by direct computation, independently of any dictionary.
- Factoring `L`: `A+B = e1 = -1`, `AB = e2 - 2p = -38`, so `A,B` are the roots of `z^2+z-38`,
  `A = (-1+sqrt(153))/2`, `cos t1 = A/(2 sqrt 13) = 0.788328...`, `cos t2 = -0.927002...`,
  **`v = cos t1 * cos t2 = -19/26` exactly.**

**SIN row (`p = 3 mod 4`), tested at p=43, `k=1..3` (`43^3 = 79507` points):**
- **`e3 = -p*e1` : TRUE exactly** — the SIN row's prediction, opposite sign to COS. Confirmed.
- `v = -(e2+2p)/(4p)` at the five classes gives `-0.14526827783..., -0.59765012..., -0.67890670...,
  -0.69751339..., -0.72949873...`, matching the record's independently-computed `O(p^4)` eigenvalue
  values `-0.1451/-0.5977/-0.6788/-0.6976/-0.7295` to the 4 dp the record printed.

**So F2's thesis — the dictionary is stratum-dependent and the criterion inverts — is CORRECT and is
now proved, not merely matched.** v1's blanket application of the SIN criterion to the 14 COS primes
was a genuine defect.

**DISCREPANCY (non-blocking, but a stated number that does not reproduce).** F2 asserts
> *"Verified at p=13 (exact `e2 = -12`): cos dictionary -> `v = -0.72997` (instrument: `-0.7300`)"*

Applying the cos dictionary to the exact `e2 = -12` gives `v = (e2-2p)/(4p) = -38/52 = **-19/26 =
-0.7307692...**`, not `-0.72997`. The gap is `7.7e-4`. Traced: `-0.72997` is
`0.7883 * (-0.9260)`, the product of two cosines read off 4-dp phases printed by the `O(p^4)`
instrument, where `RESULT_n1_phase_inequality_reduction_v1.md` §5 records the second phase as
`0.8776 pi`. The exact value requires `arccos(-0.927002)/pi = 0.876595`, i.e. **`0.8766`, not
`0.8776`** — a single transposed digit in the record. Two consequences, both now checkable:
- the same §5 line says *"`u = -0.1377` (so `|V|/sqrt p = 2|u| = 0.2774`)"* — but `2 * 0.1377 =
  0.2754`. The exact `u` is `-1/(2 sqrt 13) = -0.138675`, `2|u| = 0.27735`, which **is** the printed
  `0.2774`. So the record's `u` is also the corrupted one, and F3's `0.27735` is the correct value.
- F2's `✓` therefore records agreement between two numbers that are both wrong in the 4th decimal.
  The *verdict* it supports is right; the *evidence line* is not reproducible.

**Exact edit:** in F2, replace ``cos dictionary -> `v = -0.72997` (instrument: `-0.7300`)`` with
``cos dictionary -> `v = -19/26 = -0.730769...` exactly; v1's sin dictionary -> `-7/26 =
-0.269231...`; the instrument's printed `-0.7300` derives from a mistyped phase (`0.8776` for
`0.8766`) in `RESULT_n1_phase_inequality_reduction_v1.md` §5 and is itself off by `7.7e-4`.``
Note also that at p=13 **both** dictionaries return `v <= 0` (`-19/26` and `-7/26`), so p=13 does not
by itself demonstrate an inverted *verdict*; what demonstrates the inversion is `e3 = +p*e1` vs
`e3 = -p*e1`, which is now verified exactly at p=13 and p=43 respectively.

### Check 4 — F1 sign fix — **PASS, verified exactly at two primes and two parities of k**

`P_k = -V_k` for every `k` (Lefschetz) with Newton `e2 = (P1^2 - P2)/2` gives
`e2 = (V1^2 + V2)/2`. Substituting into the higher Newton identities:
`e1 = -V1`, `e3 = (-V1^3 - 3 V1 V2 - 2 V3)/6`, `e4 = (V1^4 + 6 V1^2 V2 + 3 V2^2 + 8 V1 V3 + 6 V4)/24`.

Mutual consistency is decided by the two forced identities, which involve **odd** `k` and therefore
test the `P_k = -V_k` convention where it can fail:
- p=13 (COS): `e3 = +p*e1` **TRUE**, `e4 = p^2` **TRUE** — exact integer-vector equality in `Z[x]/Phi_7`.
- p=43 (SIN): `e3 = -p*e1` **TRUE** — exact in `Z[x]/Phi_31`.

Divisibility also came out right without adjustment: `V1^2+V2` was even, `-V1^3-3V1V2-2V3` divisible
by 6, and the `e4` numerator divisible by 24, at both primes — a sign error would generically break
these. **The Newton identity and the Lefschetz convention as written in F1 are mutually consistent.**

Corollary confirming F1's own claim: with the *wrong* sign (`P2 := +V2`), `e2` would be
`(V1^2 - V2)/2`; at p=43 that returns `e2 = -2p` identically at every class, i.e. `v = -1/4` at every
`a` — matching F1's statement that v1 "returns `v = -0.25` at every `a` at p=43". Verified: with
`P2=+V2` the resulting minimal polynomial at p=43 is `(Y+86)^5`'s root set, `v = -1/4` at all five
classes. (Computed in check 6.)

### Check 5 — F4 replacement checks M3a–M3d — **PASS on computability; M3c-fires claim confirmed with a corrected decimal**

**Computable from `(V1,V2)` alone at `O(p^2)`?** Yes, all four:
- **M3a** `Im V2 = 0` — pure `h2` symmetry test, `O(p)` after `h2`. Verified TRUE at p=43.
- **M3b** `conj V_k(a) = chi2^{(k)}(-1) V_k(a)` — `h_k[d] = chi2^{(k)}(-1) h_k[-d]`, `O(p)`. Verified:
  p=13 `chi2(-1)=+1`, `h1` symmetric ✓; p=43 `chi2(-1)=-1`, `h1` antisymmetric with `h1[0]=0` ✓;
  `h2` symmetric at both ✓.
- **M3c** `|u| <= 1+v`. Expressible with no eigenvalue solve: `u^2 = ∓V1^2/(4p)`, so for SIN it is the
  joint total non-negativity of `4p - W` and `(4p-W)^2 + 16p*V1^2`, and for COS of `4p + W` and
  `(4p+W)^2 - 16p*V1^2`, where `W = V1^2+V2`. Both exact integer vectors in `Z[zeta_n]`. Verified
  holding at p=13, 43, 127.
- **M3d** `u^2 >= 4v` and `|u| <= 2` — likewise `2W + 8p - V1^2 >= 0` and `V1^2 + 16p >= 0` (SIN).
  Verified holding at p=13, 43, 127.

Costs no extra field enumeration: everything is a polynomial identity in the two histograms already
computed. **F4's core claim is correct — M3 is now runnable where v1's `e3`/`e4` version was not.**

**★ "M3c fires on the F1 bug at p=43" — CONFIRMED.** Running mutation (i) (`P2 := +V2`) through the
real pipeline (`audit_n1_vsign_v2_mutations.py`): the bugged `e2` equals `-p = -43` at **all five**
`mu6` classes, i.e. `v = -1/4` at every class — reproducing F1's statement exactly. M3c's exact test
(`4p-W` and `(4p-W)^2+16p V1^2` totally non-negative) **FAILS** under the bug and **HOLDS** on the
correct data. M1 also fails (bugged `m_43` = `Y^5+215Y^4+18490Y^3+795070Y^2+17094005Y+147008443`).

**Decimal discrepancy in F4, non-blocking.** F4 states the bug fires *"at p=43, a=2: `|u| = 0.777645
> 1+v = 0.750000`"*. `1+v = 1 - 1/4 = 0.75` is exact ✓. But `|u| = 0.777645` is not the value at
`a = 2`: for `n=31`, `mu6 = {1,5,6,25,26,30}`, so the class of `a=2` is `{2,10,12,19,21,29}` while
the maximising class (the one with `u = 0.7778` in `RESULT_n1_phase_inequality_reduction_v1` §5b) is
`{4,7,11,20,24,27}`. Either the class label or the `|u|` is misattributed. The *conclusion* (M3c
fires) is correct and is established above at the level of the whole class set, so no arm changes;
the cell label should be corrected or dropped.

### Check 6 — F5 M2b mutation battery — **three of four fire; mutation (iv) is NOT CONSTRUCTIBLE as written**

Each mutation run through the real pipeline at p=43 (`audit_n1_vsign_v2_mutations.py`), against the
frozen `m_43` and the exact M3a/M3c tests. Baseline: M1 matches, M3a holds, M3c holds.

| mutation | M1 | M3a | M3c | what actually catches it |
|---|---|---|---|---|
| **(i)** `P2 := +V2` | **FAILS** | holds | **FAILS** | both, as F4 predicts. `v = -1/4` at all 5 classes |
| **(ii)** `chi2` exponent `(p-1)/2` | **FAILS (by abort)** | **FAILS** | n/a | **M3a fires first.** `h2` loses its `d -> -d` symmetry; `e2` is then *not* `mu6`-invariant, so "the minimal polynomial of degree `(n-1)/6`" does not exist and the min-poly step aborts |
| **(iii)** trace `P` instead of `P + Frob P` | **FAILS** | holds | **HOLDS** | 1,736 points have no `dlog` in `E(F_p)` -> the real code raises `KeyError` and the run aborts. **If those points were silently dropped**, M3a, M3c and M3d all still hold, the bugged `e2` roots are `-52.5, -13.6, -6.6, -5.0, -2.3`, all `>= -2p = -86`, so the run would report **`v <= 0` at every class — a false CONFIRMATION** — and **only M1 catches it** |
| **(iv)** `v = +0.36` plant at the histogram level | — | — | — | **cannot be constructed; see below** |

**★ Mutation (iv) is not realisable as specified — a decidable defect.** A plant at the histogram
level changes `h2` by an integer vector, so it changes `e2` by an element of `(1/2)Z[zeta_n]`. Landing
exactly on `v = +0.36 = 9/25` requires `e2 = -2p - (36/25)p`, i.e. at p=43 `e2 = -3698/25`. A rational
algebraic integer is a rational **integer**; `-3698/25` is not one. **No integer histogram produces
`v = +0.36` at any `mu6` class of p=43.** (v1's M2 / v2's M2a is unaffected — it plants *synthetic
power sums*, where any real `v` is available. The defect is specific to M2b's "at the **histogram**
level" requirement, which is the part F5 added.)
*Exact edit:* replace `v=+0.36` with an achievable integer target, e.g. at p=43 add a `mu6`-invariant
integer vector to `h2` shifting `e2` by `-28` at every class (`delta = -56` at index 0), giving
`e2 = -114 < -2p = -86` and `v = 28/172 = 7/43 = +0.1628` exactly, `mu6`-consistent by construction.

**Is "each mutation MUST make M1 or M3c fail" guaranteed or hoped?** For any mutation that changes
`h1` or `h2` at p=13 or p=43 it is **guaranteed**, because F3 upgraded M1 to *exact equality* with a
frozen reference — any perturbation changes `m_p`. So M2b's stated requirement is met by construction
once (iv) is made realisable.

**★ What that guarantee does NOT cover — the genuinely unguarded component.** M1's guarantee is only
over p=13 and p=43. A mutation whose effect is **conditional on `p`** is invisible to M2b. Two concrete
instances, both decidable:
- **M1's COS arm has `d = (n-1)/6 = 1`.** The entire `p = 1 mod 4` branch — dictionary, `mu6`-coset
  bookkeeping, min-poly degree, Sturm orientation — is validated against a *single rational number*
  (`e2 = -12`). Any COS-side bug that is invisible at `d = 1` passes M2b and M1 and then runs on all
  14 COS primes (`d` up to 766).
- Reference primes are `p = 13 = 5 mod 8` and `p = 43 = 3 mod 8`; **no `p = 1 mod 8` reference exists**,
  so any square-root / character code path specific to `p = 1 mod 8` is never exercised by M1.

*Exact edit (cheap, closes both):* add **p = 61** to M1's reference set — it is COS, `n = 61`,
`d = 10`, `p = 5 mod 8`, and `p <= 61` so the `O(p^4)` instrument is affordable there, which also
un-vacuums the adjudication gate's clause (c). Optionally p=67 or p=79 (SIN, `d = 13 / 11`) as well.
The full list of `p <= 100` with `#E` prime is `13, 43, 61, 67, 79, 97`.

### Check 7 — F6 strata — **PASS, every sub-claim reproduced**

**Artifact:** `audit_n1_vsign_v2_strata.py` (exact point count `n = p+1+sum_x legendre(x^3+7,p)`).
Curve family confirmed as `E: y^2 = x^3 + 7` (j=0, `B=7`) from `n1_twisted_eigenvalues_v1.sage` line
`E = EllipticCurve(F,[0,B]); B=7`.

| v2 claim | recomputed | status |
|---|---|---|
| frozen 40-list spans `[127, 4513]` | `[127, 4513]` | **PASS** |
| all `p = 1 mod 3` | True for all 40 | **PASS** |
| 26 are `p = 7 mod 12` (SIN) | 26 | **PASS** |
| 14 are `p = 1 mod 12` (COS) | 14; no `p` outside `{1,7} mod 12` | **PASS** |
| v1's "smallest 10 above 2000" are all already among the 40 | `[2089,2143,2251,2281,2503,2647,2677,2731,3271,3343]`, all in the 40 | **PASS — F6's premise confirmed** |
| replacement stratum = smallest 10 with `#E` prime above 4513 | `[4549,4597,4831,5107,5197,5281,5791,5923,5953,6007]` | **exact match** |
| (a) disjoint from the 40 | disjoint | **PASS** |
| (b) smallest 10 above 4513 | yes, no omissions in `(4513, 6007]` | **PASS** |
| (c) exactly 5 with `p = 3 mod 4` | 5: `4831, 5107, 5791, 5923, 6007` | **PASS** |

The forcing argument is also correct: `p = 2 mod 3` makes `x -> x^3` a bijection, `E` supersingular,
`#E = p+1` even, never prime. `p = 1 mod 3` is forced, so `p in {1,7} mod 12` and the 26/14 split is
exhaustive.

Stratum-2 sizes (needed by check 2c): `(n-1)/6` runs `766, 752, 817, 832, 868, 872, 975, 971, 1015,
1027`; largest is `p=6007, n=6163, d=1027`.

### Check 8 — F7 count unit — **PASS, count reproduced independently**

`sum over the 40 primes of (n-1)/6` = **14,168**; `p=3 mod 4` subtotal = **9,888**;
`p=1 mod 4` subtotal = **4,280**. `9,888 + 4,280 = 14,168`. Raw `a`-cells `sum (n-1)` = **85,008**,
matching v2's "not 85,008". All four numbers reproduce exactly (`audit_n1_vsign_v2_strata.py`).

The count unit itself is also correct as exact arithmetic, not as an observation: `sigma_c(e2(1)) =
e2(c)` is immediate from `e2(a) = (1/2) W(zeta_n^a)` with `W in Z[x]`, and I verified
`sigma_m(W) == W` as integer vectors for every `m` in the order-6 subgroup at p=13 and p=43
(check 1). `6 | n-1` is forced: `n` prime `>3` so `2 | n-1`, and the order-3 automorphism of the j=0
curve acts freely on `E(F_p)\{O}` when `3 | n` fails, giving `3 | n-1`.

**One caveat carried to check 9:** `(n-1)/6` is the number of `mu6` *classes*. It equals `deg m_p`
only if the stabiliser of `e2(1)` in `(Z/n)^*` is exactly `mu6` and not larger. See check 9, gate G-DEG.

### Check 9 (★) — GATE CALIBRATION — **most gates are exact-algebraic with FFR = 0 by construction; three are not, and the adjudication gate has zero discriminating power**

Per `RESULT_row_budget_lowtail_v2.md` §5, every gate's false-failure rate under a **correct**
instrument, computed here rather than after the run.

| gate | type | FFR under a correct instrument | note |
|---|---|---|---|
| **M1** exact equality with frozen `m_13`, `m_43` | exact algebraic | **0 by construction** | conditional on the references being right — **verified exactly, check 1**. (v1's version had FFR = **1**: a `1e-9` tolerance against 4-dp transcriptions, gap `1.7e-4`. F3 fixed this.) |
| **M2a** synthetic `P1,P2 -> v = +0.36` | float, synthetic data | **~0** (double round-trip `~1e-15` vs `1e-9` tolerance) | see EXACTNESS note below |
| **M2b** mutations (i)–(iii) | exact | **0** — a correct instrument reproduces the reference, so M1 passes | (iv) not constructible, check 6 |
| **M3a** `Im V2 = 0` | exact, **forced** | **0** | `chi2^{(2)}(-1)=+1` for all odd `p` |
| **M3b** `conj V_k = chi2^{(k)}(-1) V_k` | exact, **forced** | **0** | |
| **M3c** `\|u\| <= 1+v` | exact, **forced by weight-1** | **0** | |
| **M3d** `u^2 >= 4v`, `\|u\| <= 2` | exact, **forced** | **0** | |
| primary criterion `max_a v <= 0` | deterministic universal claim | **n/a — no statistic, no multiple comparisons** | v2 §5 is right about this |
| **G-DEG** `deg m_p = (n-1)/6` | assertion | **NOT 0** — aborts on correct data if the stabiliser of `e2(1)` exceeds `mu6` | 0/5 occurrences at p=13,43,127,163,211; unbounded a priori |
| **G-BND** boundary at `∓2p` | wording | **NOT 0** — if implemented as "root `<=` threshold", an exact `v = 0` cell (which **confirms** `v <= 0`) is filed as a counterexample | decided free by the integer test `m_p(∓2p) ?= 0` |
| **D5 ABSTAIN** | residual | **would mis-file a confirming cell** | retired by the ADDITION; the branch should be deleted, not left in the document |
| **adjudication (a)** exact `Z[zeta_n]` recomputation | exact | **0** | already exact under the ADDITION — i.e. it re-does what was done |
| **adjudication (b)** M3a–M3d at the cell | exact, **forced** | **0** | cannot fail on correct data |
| **adjudication (c)** `O(p^4)` instrument if `p <= 61` | — | **VACUOUS** | the frozen scope starts at **p = 127 > 61**; this clause can never fire |

**★ The load-bearing calibration finding.** Every clause of the F5 adjudication gate either
(a) re-runs an exact computation, (b) tests a *forced* identity that cannot fail on correct data, or
(c) cannot run at all in scope. **So a `v > 0` cell passes adjudication automatically.** The gate is
therefore not a filter on whether a counterexample is genuine — it is a restatement. The only thing
standing between "the instrument is wrong" and "the route is dead" is **M1 at p=13 and p=43**, whose
COS arm is a single rational number (check 6). This is not a false-failure problem; it is a
**zero-discriminating-power** problem, the mirror image of the two failures §5 of `RESULT_row_budget_
lowtail_v2.md` records. *Exact edit:* make clause (c) non-vacuous by adding p=61 (COS, `d=10`) and/or
p=67 / p=79 (SIN, `d=13 / 11`) to M1's reference set — all have `#E` prime and `O(p^4)` is affordable
at p=61.

**EXACTNESS (spec item 8) — one undeclared float.** The signal path (`h1`, `h2`, `W`, `m_p`, the
Sturm/Descartes decision) is `int`-only and correct. **M2a is the exception**: `sin t1 = sin t2 = 0.6`
and a `1e-9` tolerance are floats. It acts on synthetic data, never touches a curve or a key, and its
FFR is ~0 — but the project rule requires the carve-out to be *named*. v2 names no carve-out.
*Exact edit:* add to v2 — *"EXACTNESS: signal path is `int` throughout; the single float carve-out is
M2a's synthetic tuple (`sin = 3/5` is exact as a rational: use `v = 9/25` exactly and drop the
tolerance), analytic-size only, no curve data in the path."* Note `sin = 3/5` makes M2a exactly
rational, so the carve-out can simply be removed.

**D5's own power number checks out.** `sum_d |h2[d]| ~ p^2` against `|V2| <= 4p` gives cancellation
`~p/4`; `log10(p/4) = 3.05` digits lost at p=4513, leaving `12.9` of a double's `15.95` — so the
double-precision sign threshold is `|v| ~ 1e-13`. Propagating: `eps * p^2 / (8p) = 2.2e-16 * 4513/8 =
1.2e-13`. **D5's `1e-13` is correct.** It is moot under the ADDITION, which is the right resolution.

### Check 10 — introduced by the fixes, and itself wrong

| item | introduced in | status |
|---|---|---|
| Sturm named as the decision procedure | ADDITION | **blocking** — check 2(c) |
| `O(n^2)` attributed to the whole per-prime test | ADDITION | **wrong** — it is stage A's cost only; the min-poly step is `Theta(n^4)` naively |
| "minimal polynomial ... of degree `(n-1)/6`" | ADDITION | assertion, not theorem — check 2(a) rider 4 |
| `e2(1) in (1/2)Z[zeta_n]` vs "algebraic integer" | ADDITION lines 103 / 107 | internal tension; measurement says `Z[zeta_n]` — check 2(a) rider 5 |
| boundary `v = 0` unresolved; D5 `ABSTAIN` left in | ADDITION + D5 | check 2(a) rider 3; check 9 G-BND |
| M2b mutation (iv) `v = +0.36` at the histogram level | F5 | **not constructible** — check 6 |
| adjudication clause (c) `p <= 61` | F5 | **vacuous over the frozen scope** — check 9 |
| `v = -0.72997` at p=13 | F2 | not reproducible; exact value `-19/26` — check 3 |
| `a = 2`, `\|u\| = 0.777645` at p=43 | F4 | class label misattributed — check 5 |
| the `∓(e2+2p)` sign error | ADDITION | **v2 caught and corrected it itself**, with the p=13 witness; I confirm the correction independently. **Not a defect of v2.** |
| no float carve-out declared | whole doc | check 9, EXACTNESS |

Everything else the seven fixes introduced reproduces exactly.

---

## ⚠ MANDATORY DISCLOSURE — this audit produced in-scope sweep numbers

Check 2(c) required timing "a real prime or two". Running the pipeline at a real prime **produces that
prime's answer**; there is no way to measure the cost without it. Disclosed in full rather than buried:

**p = 127, 163, 211 — the 1st, 2nd and 3rd primes of the frozen 40-list — are now IN-SAMPLE.**
Exact, cross-validated by two independent minimal-polynomial algorithms (coset product in
`Z[x]/Phi_n`; multi-modular Gaussian periods + CRT) and by Sturm and Descartes returning identical
counts:

| p | n | d = (n-1)/6 | stratum | `m_p` irreducible | totally real | **# classes with `v > 0`** | max `v` |
|---|---|---|---|---|---|---|---|
| 127 | 127 | 21 | SIN | yes | 21/21 | **1** | `+0.16585543` |
| 163 | 139 | 23 | SIN | yes | 23/23 | **1** | `+0.15519358` |
| 211 | 199 | 33 | SIN | yes | 33/33 | **3** | `+0.07765088` |

`m_p(-2p) != 0` at all three, so no boundary case arises. The p=127 offending class **passes M3a,
M3c and M3d exactly** (`4p-W`, `(4p-W)^2+16p*V1^2`, `2W+8p-V1^2`, `V1^2+16p` all totally
non-negative), i.e. it is not flagged as an instrument artefact by any check the spec carries.

I am **not** adjudicating this — that is the run's job under its own §4/§5, and v2 §4 outcome 2 already
pre-commits to what a `v > 0` cell means (*route dead, inequality NOT refuted*). What the audit must
record is procedural: **the out-of-sample status of the first three primes of stratum 1 is spent**, any
report of the sweep must say so, and v2's outcome-2 arm plus the adjudication gate whose zero
discriminating power check 9 documents are load-bearing immediately rather than hypothetically.

---

## 2. Blocking defects and the exact edit that fixes each

**B1 — the ADDITION's decision procedure does not finish (check 2c).**
> *edit:* replace *"test by **Sturm sequence on the integer polynomial `m_p(X ∓ 2p)`**"* with
> *"test by **integer Taylor shift** `g(X) = m_p(X ∓ 2p)` (`O(d^2)` integer operations) followed by a
> **Descartes sign count** on `g(-X)` — exact, not merely an upper bound, because `m_p` is totally
> real (forced: `h2[d]=h2[-d]` makes `V2` real and `h1[d]=±h1[-d]` makes `V1^2` real, so every
> `e2(a) in R`). The run self-certifies reality with the free identity `V(g) + V(g(-X)) = deg g`, and
> the sign count **returns the count of classes with `v > 0`**, which is F7's reporting unit. Sturm is
> retained only as a cross-check at `p <= 349`."*
> Measured: `4e-5 s` vs `53.7 s` at `d = 52`; Sturm reaches `>1,500 s` at `d = 100` and extrapolates
> to ~190 years at `d = 766`.

**B2 — no algorithm is named for `m_p`, and the obvious exact one is 167 days for the sweep (check 2c).**
> *edit:* add to the ADDITION — *"`m_p` is computed **multi-modularly**: for each of `~d*log2(6p)/61`
> primes `q = 1 mod n`, take `omega` a primitive `n`-th root mod `q`, form the `d` Gaussian periods
> `eta_j`, obtain the `d` conjugates as the cyclic correlation of the `mu6`-coset coefficient vector
> with `(eta_j)` (`O(d^2)` per modulus), multiply out the linear factors mod `q`, and CRT against the
> bound `|coeff| <= C(d,k)(6p)^k`. All integer arithmetic; **no floating-point root-finding**. The
> per-prime cost is `O(n^2)` for `e2(1)` plus `O(d^3 log p / 61)` for `m_p`, NOT `O(n^2)` overall."*
> Measured: `55.4 s` at the largest prime (p=6007, `n=6163`, `d=1027`) vs `19.9 days` naively.

**B3 — M2b mutation (iv) cannot be constructed (check 6).**
> *edit:* replace *"(iv) a `v=+0.36` tuple injected at the **histogram** level"* with
> *"(iv) a `mu6`-invariant integer perturbation of `h2` moving `e2` past the threshold at every class:
> at p=43, `delta h2[0] = -56` gives `e2 = -114 < -2p = -86`, i.e. `v = +7/43` exactly. (`v = +0.36`
> is unreachable from an integer histogram: it needs `e2 = -3698/25`, and a rational algebraic integer
> is a rational integer.)"*

**B4 — the F5 adjudication gate has zero discriminating power over the frozen scope (check 9).**
> *edit:* add p=61 (COS, `n=61`, `d=10`) — and optionally p=67, p=79 (SIN) — to **M1's reference set**,
> and state clause (c) as *"the `O(p^4)` instrument at the reference primes p=13, 43, 61 only; it is
> **not available anywhere in the frozen sweep scope**, whose smallest prime is 127."* This
> simultaneously fixes M1's COS arm being a single rational number at `d = 1`.

**B5 — the boundary and the degree assertion can abort or mis-file correct data (checks 2a, 9).**
> *edit:* (i) *"the test is **strict**: for SIN, a root **strictly below** `-2p`; `m_p(∓2p) = 0` is an
> exact integer evaluation and means `v = 0`, which **satisfies** `v <= 0` and is reported as
> confirming, never as ABSTAIN"*; delete D5's ABSTAIN branch. (ii) *"use the `mu6`-coset product
> `Q_p(Y) = prod_{cosets}(Y - e2(rep))`, always of degree `(n-1)/6`; `deg m_p < (n-1)/6` is a
> legitimate outcome (`Q_p = m_p^k`) and counts are taken with multiplicity."*

**B6 — declare the float carve-out (check 9).**
> *edit:* add an EXACTNESS line; make M2a exactly rational (`sin = 3/5`, `v = 9/25`) so the carve-out
> disappears entirely.

None of B1–B6 touches the mathematics, the strata, the reference values, or the criterion table.

## 3. Verified correct, stated plainly

- **F3's frozen reference values are exactly right.** `m_43(Y) = Y^5 - 60Y^4 - 2032Y^3 + 224768Y^2
  - 5515008Y + 42288128` reproduces coefficient-for-coefficient from an independent implementation;
  it is irreducible; its five roots lie in `(-62,-61), (16,17), (30,31), (33,34), (39,40)`, all
  `>= -2p = -86` by an exact Sturm count of 0; the maximising `v` is `-0.14526827783269782` to all 17
  quoted digits; p=13's `e2 = -12` and `v = -19/26` are exact. **This was the highest-value check and
  it passes.**
- **F1 is correct and mutually consistent.** `P_k = -V_k` with Newton gives `e2 = (V1^2+V2)/2`, and the
  forced identities `e3 = +p e1`, `e4 = p^2` (p=13, `k=1..4`) and `e3 = -p e1` (p=43, `k=1..3`) hold
  as exact integer-vector identities. The bug it fixes is real: `P2 := +V2` returns `e2 = -p` and
  `v = -1/4` at every class of p=43 — a silent false confirmation.
- **F2's thesis is correct and is now proved, not matched.** The criterion genuinely inverts between
  strata, witnessed by `e3 = +p e1` (COS, p=13) vs `e3 = -p e1` (SIN, p=43), computed directly.
- **F4's M3a–M3d are all computable from `(V1,V2)` alone and all hold on correct data**, and M3c does
  fire on the F1 bug.
- **F6's strata are exactly right**: `[127, 4513]`, all `p = 1 mod 3` (correctly identified as forced),
  26 SIN / 14 COS, v1's second stratum genuinely a 100% subset of the first, and the replacement ten
  `[4549, 4597, 4831, 5107, 5197, 5281, 5791, 5923, 5953, 6007]` is disjoint, is the smallest ten
  above 4513, and contains exactly 5 with `p = 3 mod 4`.
- **F7's counts reproduce exactly**: 14,168 = 9,888 + 4,280, raw cells 85,008; and the `mu6` collapse
  is exact arithmetic (`sigma_m(W) = W`), not an observation.
- **D5's power number is right** (`1e-13` double-precision sign threshold at p=4513).
- **The ADDITION's central idea is sound**: total non-negativity of one algebraic integer of the
  `mu6`-fixed subfield **is** equivalent to the per-cell claim, with the four riders in check 2(a).
  The `∓` error v2 found in its own ADDITION is real and its correction is right.
- **Stage A really is `O(n^2)`** and really does cost minutes for the whole sweep.
- The primary criterion is a deterministic universal claim, so v2 §5's refusal of multiple-comparison
  correction and of counts-as-significance is correct.

## 4. Artifacts

All in `/Users/trentpalelei/Desktop/Math Ex/btc_puzzle_investigation/`:
`audit_n1_vsign_v2_core.py` (independent instrument), `_minpoly.py` (exact `m_p` by coset product),
`_multimod.py` (exact `m_p` multi-modular), `_m3.py` (M3c/M3d as total non-negativity),
`_k4.py` (`V_1..V_4`, forced identities), `_mutations.py` (M2b battery), `_strata.py` (F6/F7),
`_timing.py`, `_stageAB.py`, `_multimod_timing.py`, `_sturmcost.py`, `_decide.py` (+ `.log` files).
