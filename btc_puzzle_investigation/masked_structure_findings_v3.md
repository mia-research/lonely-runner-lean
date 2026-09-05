# Masked-Structure — Findings v3: the IDEA, finally tested

**Date:** 2026-07-16 · supersedes v2 on one point (§R4) and adds the test that should
have been §G from the start. v2's retractions (R1–R3) all stand.
**Script:** `hybrid_char_sum_v1.py`

---

## Provoking question: *"did we test the ideas or only the methods?"*

Audit of the session, honestly:

| panel | idea or method? |
|---|---|
| F — `Σz³ = 0` anchor | plumbing: a fact about the **detector**, not the object |
| A @ N=82 | **method only** — zero power (v2 R3), tested nothing |
| A2 — `Σ_x χ₂(x³+7)z(x)³` | **IDEA** ✓ exactly answered (generic √-cancellation) |
| D / Cap Law | **IDEA** ✓ "does flap orientation carry θ?" → no: shape, rotates rigidly with θ |
| **G** | **METHOD ONLY** — see R4 |
| C1–C4 (the four candidates) | **argued, not tested.** C1 declared "subsumed"; C4 declared "a restatement of closure" (probably true — but an argument is not a test) |

---

## R4. CORRECTED — v2 said *"G: stands."* It does not. G tested a proxy.

The masking idea was formalised correctly in this session's first message:

> closure gives `|Cov(F(x_d), φ(d))| ≤ (max|T|/n)·‖F‖_A·‖φ‖_A`, and the bound is
> **vacuous exactly when `‖F‖_A ≳ √p`** — i.e. for multiplicative characters, since
> Gauss sums give `|χ̂(b)| = 1/√p ∀ b≠0` ⇒ `‖χ‖_A ≈ √p`, exactly cancelling the gain.

…and the right test was named **in writing**: `Cov(χ_k(x([d]G)), e_n(ad))`.

**Then G implemented `MI(χ_k(x_d), d mod k)` instead** — because it fitted the existing
`conditional`/`mi_bits` harness. That is not the same object:

- `d mod k` is not the additive structure the masking hypothesis is about;
- the LSB of `d` being unlearnable from the point is a **known theorem**
  (Boneh–Shparlinski: hardcore predicate for ECDLP) — so G ran a proxy already known to
  be null, and reported that null as if it addressed the blind corner.

**I posed the idea and substituted the method I had lying around.** That is the failure
mode the standing rule names, executed in the same session that quoted the rule.

---

## The idea, actually tested  [EXACT, full group enumeration]

```
    S_k(a) = Σ_{d=1..m}  χ_k( x([d]G) ) · e_m(a·d)          on  y² = x³+7 / F_p
```

pairs the closure-blind multiplicative readout against an additive character of the
scalar. **Whole cyclic subgroup ⟨G⟩ enumerated** — no sampling, no MI, no power question.

| p | m=\|⟨G⟩\| | k | a* | max\|S\| | /√(2m ln m) | **/√p** | /m (leak=1) |
|---|---|---|---|---|---|---|---|
| 523 | 489 | 2 | 31 | 43.00 | 0.553 | 1.880 | 0.088 |
| 523 | 489 | 6 | 235 | 56.26 | 0.723 | 2.460 | 0.115 |
| 2281 | 2203 | 3 | 1792 | 112.74 | 0.612 | 2.361 | 0.051 |
| 5323 | 906 | 3 | 231 | 109.69 | 0.987 | 1.503 | 0.121 |
| 12613 | 12637 | 3 | 115 | 301.60 | 0.617 | **2.685** | 0.024 |
| 59971 | 29822 | 2 | 3513 | 464.99 | 0.593 | **1.899** | 0.016 |
| 59971 | 29822 | 6 | 13940 | 602.74 | 0.769 | **2.461** | 0.020 |

**`max_a |S_k(a)| ≈ 2·√p`, stable across two orders of magnitude in p** (1.9–2.7, no
drift); `/√(2m ln m) ≈ 0.5–1.0` = the generic random scale; the leak ratio `/m` decays
(0.088 → 0.016). Square-root cancellation **at every additive frequency**, exactly.

### Why this COMPLETES the blind spot rather than confirming it  [the positive result]

Any additive feature expands as `φ(d) = Σ_a φ̂(a) e_n(ad)`, so

```
    |Cov(χ_k(x_d), φ(d))|  ≲  (max_a |S_k(a)| / n) · ‖φ‖_A  ≈  (2/√p) · ‖φ‖_A
```

The corner was blind **only because routing through `‖F‖_A` is lossy for characters**
(`‖χ‖_A ≈ √p` cancels the `O(p^{-1/2})` gain). Attacking the hybrid sum **directly**
recovers the bound anyway. So the closure theorem's one uncovered corner is covered — by
a different route, and the masking hypothesis is answered in its sharpest form.

**Scope:** full enumeration at p ≤ 59,971; not a proof at p ~ 2²⁵⁶. The `√p` scaling is
stable and is what Weil-type bounds on character sums with elliptic-curve points predict
(Kohel–Shparlinski / Lange–Shparlinski / Bourgain line) ⇒ this **VERIFIES known theory**
rather than discovering anything. Tag: VERIFIED (small p) + CITED (the bound).

---

## Where that leaves the masking hypothesis

Stated as: *"additive structure in d, invisible to multiplicative/geometric readouts of
x([d]G)."* After this session:

- **Geometric readouts (ε, norm band, frame operator): closed BY PROOF** — v2 R2 shows
  they are functions of the lift coefficients `(u,v)` only ⇒ shape-determined ⇒ they
  cannot carry arithmetic *at all*, for any CM curve.
- **Multiplicative readouts (χ_k): closed by the hybrid sum** — √p cancellation at every
  frequency, so `|Cov| ≲ (2/√p)‖φ‖_A` for **every** additive φ, including every
  "constructed d". And the sparser the construction, the smaller `‖φ‖_A`, the *more*
  invisible — the mask is the default, not a conspiracy.
- **Still genuinely open (closure bounds single sums only):** the **bilinear / joint**
  objects — B (difference set `{x([dᵢ−dⱼ]G)}`), E (amicable cross-moment `z_p` vs `z_n`).
  These are not touched by any of the above, and were the closure theorem's own named
  complement from the start.

**The idea-level redirect (v2 R2 + this):** every shape observable is inert and every
single-coordinate multiplicative one is √p-bounded, so the only live single-point object
is **the map `x ↦ (u,v)` itself** — the joint 2-D distribution of lift coefficients over
curve points. A2 tested one 1-D projection (`z³`) ⇒ generic. The joint distribution is
untouched.

---

## Method rule earned here (added to v2's list)

**Naming the right test does not mean running it.** When the harness you already have
fits a *proxy* of the test you posed, that is the moment the substitution happens — and
the null it returns will read exactly like the null you were looking for. Before running:
*is this object the one I named, or the one my code makes easy?*
