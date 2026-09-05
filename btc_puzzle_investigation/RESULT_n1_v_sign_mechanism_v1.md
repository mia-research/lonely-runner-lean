# N1: WHY `v ≤ 0` fails — an exact identity, and the conjecture restated as a sub-Weil bound

**Date:** 2026-07-25 · Scripts: `n1_vsign_mechanism_v1.py`, plus the exact integer-vector check inline
below. **Extends `RESULT_n1_v_sign_route_refuted_v1.md`** — that file's counterexamples stand
unchanged; **its §4 "characterization" is superseded by this one**, including its word *"generic"*,
which was wrong (see §5).

**No leakage, key-recovery or ECDLP content.**

---

## 1. The identity

> **`V₂ = V₁² + 2p` for `p ≡ 3 mod 4` (SIN);  `V₂ = V₁² − 2p` for `p ≡ 1 mod 4` (COS).**
> Exact integer-vector identity in `ℤ[x]/Φ_n`. **`[PROVED — exact, verified at 10 primes]`**

Verified at `p = 13, 43, 127, 163, 211, 349, 397, 433, 547, 577`: `V₂ − V₁²` has **every non-constant
component exactly zero** and constant term exactly `±2p`. No float.

**`V₂` is completely determined by `V₁`.** The `k=2` field enumeration the whole pipeline is built
around is redundant. Downstream, with `e₁ = −V₁` and `e₂ = (V₁²+V₂)/2`:

```
e2 = e1² + p   (SIN)          e2 = e1² − p   (COS)
```

## 2. What it says geometrically — the two angles are 120° apart

In the stratum's natural coordinates (`u` = sum, `v` = product of the two half-traces):

> **`v = u² − 3/4`, exactly.** Verified at **357/357** classes over 8 primes, max deviation `1.4×10⁻⁶⁰`.

Equivalently `s₁² + s₁s₂ + s₂² = 3/4` — the **Eisenstein norm form** at a fixed value, which is the
`μ₆` / CM structure of the `j=0` curve `y² = x³+7` appearing directly. Solving the ellipse:

> **`u = cos t`, `s₁ = cos(t − 60°)`, `s₂ = cos(t + 60°)`.**
> Verified at 357/357 classes, max deviation `9.5×10⁻⁴⁰`.

**The two Frobenius half-angles differ by exactly 120°.** That single fact generates everything else.

## 3. ★ The conjecture, restated: it was a sub-Weil bound all along

Because `v = u² − 3/4` and `u = V₁/(2√p)` (up to the stratum phase):

> **`v ≤ 0` at every class  ⟺  `|u| ≤ √3/2` at every class  ⟺  `|V₁(a)| ≤ √3·√p` for every `a ≠ 0`.**

Weil allows `|V₁| ≤ 2√p`. **The conjecture demanded that a character sum never exceed `√3/2 ≈ 86.6%`
of its own Weil bound, at any of the `(n−1)/6` classes.** That is what `v ≤ 0` *is*. It is not a
statement about signs of sines at all.

It is false, and now visibly so: the largest normalized sum observed is `|u| = 0.96612` at `p = 547`,
i.e. **`|V₁| = 1.932·√p`**, against the conjecture's `1.732·√p` ceiling and Weil's `2·√p`.

**Two bounds fall out immediately, and both are forced, not observed:**

| quantity | value | source |
|---|---|---|
| `v ≥ −3/4` | attained at `u = 0` | `v = u²−3/4`, `u² ≥ 0` |
| **`v ≤ +1/4`** | **unconditional** | `v = u²−3/4` with Weil `|u| ≤ 1` |

So **`v ∈ [−3/4, +1/4]`, both endpoints forced.** Measured over 357 classes: min `−0.749998`,
max `+0.183395`. The spec states neither bound; `M3c`/`M3d` are strictly weaker than `v = u²−3/4`.

**This is the positive residue of the refutation.** The route wanted `v ≤ 0` and cannot have it, but
`max_a v ≤ 1/4` is unconditional and provable. Whether `1/4` is useful for `S_y ≤ 2` is a separate,
untested question — stated as a bounded magnitude, not as a rescue.

## 4. Why the rate is ~5% and not ~50%

`u` is a normalized character sum: typical size `mean|u| = 0.4083`, hard ceiling `1` (Weil). The
threshold `√3/2 = 0.866` sits at **1.69 sd** of `u`'s own spread.

| | |
|---|---|
| Gaussian prediction `P(\|u\| > √3/2)` | `0.091` |
| **observed rate of `v > 0`** | **`0.048`** (17 of 357) |

Same order; the observed rate is lower because `u` is supported on `[−1,1]` and is lighter-tailed than
a Gaussian, as a Sato–Tate-type law should be. **`v > 0` is an ordinary moderate tail excursion of a
character sum, not an exotic event.**

And the diagnosis of the `|u|`-ranking is exact: at **every** prime the `v>0` classes are precisely
the top-`|u|` classes, ranks `1..k` with **no interleaving** — forced, since `v` is a strictly
increasing function of `|u|`. Pooled across all 8 primes the separation is global:
`max|u| among v≤0 = 0.86168 < √3/2 < 0.86882 = min|u| among v>0`.

## 5. ⚠ Correcting the predecessor

`RESULT_n1_v_sign_route_refuted_v1.md` §4 called `v>0` **"generic"**. **That was wrong and I am
retracting the word.** 4–6% is not generic — if the two angles were independent the rate would be
~50%, and if `t` were equidistributed it would be `1/3`. The observed 5% is a *suppressed* rate, and
the suppression (`v = u²−3/4` plus the typical size of a character sum) is the whole content. Calling
it "generic" named the frequency and buried the mechanism — the exact failure mode
`methodology_understand_exceptions_2026_05_28` warns about, committed in the file that reported the
exception.

The predecessor's **counterexamples, exact enclosures, counts, and adjudication (§1–§3) stand
unchanged** — and are now *explained* rather than merely certified: the `p=127` offending class is
simply the class where `|V₁|` is largest.

## 6. Consequences for the route — sharper than "dead"

- **The route could not have worked at scale, and this is now quantitative.** With ~5% of classes
  exceptional and `d = (n−1)/6` classes per prime, the chance that *some* class fails is
  `1 − 0.95^d`. At `p = 547` (`d=91`) that is `≈ 0.99`; at `p = 4513` (`d=766`) it is `1 − 10⁻¹⁷`.
  **Every large prime in the frozen sweep would have failed.** The 50-prime sweep would have returned
  counterexamples at essentially every prime — not a marginal verdict.
- **Why the references missed it is now exact, not statistical.** `p=13` has `d=1` and `p=43` has
  `d=5`; `1 − 0.95⁵ = 0.23`. The conjecture was frozen against the only two primes in the whole design
  small enough to be likely to pass.
- **What a repaired route needs is now a named object**: not "prove `v ≤ 0`" but either
  (i) a sub-Weil bound `|V₁(a)| ≤ √3√p` — **false**, so this door is shut, or
  (ii) control of the *number/measure* of `a` with `|V₁(a)| > √3√p` — untested, and a standard shape
  for character-sum questions, or
  (iii) an argument that tolerates `v ≤ 1/4` instead of `v ≤ 0`.
  **Nothing here is evidence for or against (ii) or (iii).**

## 7. Scope and grade

- `V₂ = V₁² ± 2p` and `v = u² − 3/4`: `[PROVED — exact integer identity]` at the 10 / 8 primes listed,
  `y² = x³+7`, `#E` prime. **A proof from the CM structure is not given here** — the 120° separation
  makes one look routine, but "looks routine" is not a proof and this is graded as verified, not
  derived. **Next step: derive it from the `μ₆` action.**
- `v ∈ [−3/4, 1/4]`: forced given the identity plus Weil.
- The ~5% rate and the Gaussian comparison: `[EMPIRICAL]`, 8 primes, `p ≤ 547`, 357 classes.
  No rate is extrapolated to the sweep's large primes except the `1 − 0.95^d` remark, which is
  explicitly a heuristic and is labelled as one.
- **Nothing transfers to `p = 2²⁵⁶−2³²−977`.** No ECDLP, leakage, or security claim.
