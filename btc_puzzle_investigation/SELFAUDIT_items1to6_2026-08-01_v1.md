# SELF-AUDIT — items 1–6, hunting closure-by-declaration, dismissed structure, and training-data defaults

**Date:** 2026-08-01. Every finding below was **tested, not reasoned** — the standing rule from this
session is that hedging is not rigor. Two of four findings required overturning something I wrote.

---

## A1 — SEVERE: the blindness theorem was OVER-CLOSED. A live instrument was declared dead.

**What I claimed:** *"the singular-value layer of **every** readout × phase object is
readout-independent"*, and in the synthesis, *"an **entire instrument class** is dead by theorem."*

**What is actually true.** The derivation runs
`G[k,k'] = Σ_a H(k,a)·conj(H(k',a)) = n·Σ_d |c(d)|²·φ_k(d)·conj(φ_{k'}(d))`
— and that middle step is `Σ_a e_n(a(d−d')) = n·δ`, which **requires the COMPLETE sum over `a`.**

**Measured, restricting `a` to a window:**

| p | frequency set | max rel. difference, curve vs random readout |
|---|---|---|
| 823 | full `a ∈ [0,n)` | 2.9e−15 — **blind** |
| 823 | `a ∈ [0, n/8)` | **0.617 — readout fully visible** |
| 823 | `a ∈ [0, n/32)` | **0.739 — readout fully visible** |
| 1051 | full | 2.9e−15 — blind |
| 1051 | `a ∈ [0, n/8)` | **0.629** |
| 1051 | `a ∈ [0, n/32)` | **0.688** |

**The readout is not marginally visible under windowing — it is fully visible.**

**Why this is the worst finding.** *Complete vs incomplete* is the exact distinction that makes the
`2^128` channel open at all: the 120° lock bounds the **complete** sum `|V| ≤ 2√p` and says nothing
about incomplete ones. I applied that reasoning correctly to the cap in the same session — and then
missed it inside my own theorem.

> **CORRECTION.** The theorem stands with the scope **"the Gram over the complete frequency range."**
> The closure *"an entire instrument class is dead"* is **RETRACTED**. The **windowed Gram of a
> readout × phase object is readout-sensitive, unrun, and is exactly the localised object the
> `2^128` regime calls for.** That is a positive vector I dismissed.

## A2 — MODERATE: one of four OOS kills was under-powered

A kill is only valid if the OOS mean is distinguishable from the **in-sample effect**, not merely
from zero.

| statistic | in-sample | OOS mean ± se | vs zero | **vs in-sample** | verdict |
|---|---|---|---|---|---|
| `C_a1` (`\|T\|²`, Parseval null) | −1.54 | −0.33 ± 0.48 | −0.68 sd | **2.50 sd** | **UNDER-POWERED** |
| A2 spectral inversion | +1.82 | −0.34 ± 0.42 | −0.81 sd | 5.15 sd | solid |
| boundary partial-sum difference | +2.66 | −0.36 ± 0.44 | −0.81 sd | 6.82 sd | solid |
| k=160 pointwise inversion | +2.95 | −0.03 ± 0.29 | −0.10 sd | 10.16 sd | solid |

> **CORRECTION.** `C_a1` is downgraded from **"dead"** to **"did not replicate at this power."**
> An effect of roughly **half** the in-sample magnitude is not excluded, and the "finite-size, gone by
> `n ≈ 400`" reading is a **hypothesis, not a finding.** Four OOS primes was too few.

## A3 — PROCESS: an equidistribution assumption used before it was measured

The pair-class floor computations used `multinomial([1/6]*6)` as the null — i.e. they **assumed** the
μ₆ classes of curve-point sums/differences are uniform. That is character-equidistribution reasoning
imported from training, exactly the default this project forbids.

**Measured under this audit:** sum object `[30166, 30055, 29720, 29856, 29906, 29997]`, χ² = 4.13;
group object χ² = 3.39 (5 df, threshold 11.07). **Uniform — the assumption was correct.**

> The numbers survive. **The order was wrong**: I relied on it, and only measured it when audited.
> An unmeasured equidistribution assumption sitting inside a null is a training-data default whether
> or not it happens to be true.

## A4 — VOCABULARY: a borrowed framework dressing an elementary fact

*"integrable, not chaotic"*, *"maximally degenerate"*, *"precludes Wigner–Dyson"* — RMT/physics
language applied to an object whose membership in that framework was never established.

The underlying fact needs none of it: **a spectrum with two distinct values has no spacing
distribution.** Stating it in RMT vocabulary makes the borrowed framework's *other* conclusions feel
licensed, which is the mechanism by which training-data defaults enter.

## A5 — MINOR: a control that cannot fire is not a control

`C-FIX` in item 5 excludes `d` with `d = ±d⁻¹`. At `2^128` with random sampling the expected count is
`~0`, and it reported **0** at every arm. It is a correct guard for a full-group sweep and **carries
no information in the sampled regime** — it should be labelled as a guard, not counted among the
controls that give the run its power.

---

## What the audit did NOT find — stated so this is not a defect-manufacturing exercise

My documented failure mode is generating plausible defects against work that is fine (three in item 1
alone). Checked and clean:

- **#26.** Proof stands; hypothesis correctly stated as `n` odd, not `j = 0`; 117/117 even-`n`
  controls fire; symbolic identities hold. No closure defect.
- **Items 3, 4, 5.** All correctly stated as **bounds with measured floors**, explicitly not nulls.
  The `M = 96` "NULL" was already retracted before this audit.
- **Item 6.** A3 correctly scoped to four primes with general-`p` flagged open; the `(D2)` label
  finding is documentary and verified.
- **Item 1 (final).** Correct; the three false defects were already retracted in-file.

## Net effect on the session's conclusions

- The **synthesis §8.2 claim "an entire instrument class is dead by theorem" is retracted**, and a new
  live object is added to the ledger: the **windowed Gram**.
- The **open-item ledger grows by two**: windowed Gram (unrun), and `C_a1` (unresolved rather than
  dead).
- **No proved result is affected.** #26, `M*M = p(I+J)`, μ₃-orbit annihilation and A3 are untouched;
  the blindness theorem is unaffected *as stated with its correct scope*.
- The direction of the error is the documented one: **over-closure**, three of five findings.
