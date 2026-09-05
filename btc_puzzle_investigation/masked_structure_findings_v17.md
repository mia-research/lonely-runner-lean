# Findings v17 — leak as REDUCTION, not revelation (user's reframe)

**Date:** 2026-07-16 · `reduction_invariance_spectrum_v1.py`. User: a leak needn't reveal D;
it can be *a reduction of what D could / could-not be, or a shadow of why D might be* — even a
few bits of search-space reduction is a real weakness. This reframes the metric from
*correlation* (which converts to only ~ε² bits of reduction) to *usable search reduction*.

## The right notion of usable reduction

A computable readout `F` reduces the d-search **usably** only if its level sets
`{d : F(x_d)=v}` are **cheaply enumerable** = have coset/subgroup structure. Formalized by
the **invariance group** `Inv(F) = { k ∈ (ℤ/nℤ)^* : F(x_[kd])=F(x_d) ∀d }` (level sets = unions
of `⟨Inv(F)⟩`-orbits ⇒ factor `|Inv(F)|` reduction). The soft ("shadow") version: the
near-invariance spectrum `A_F(k) = (1/n)#{d : F(x_[kd])=F(x_d)}`; an off-μ₆ `k` with
`A_F(k) ≫ chance` = d and kd *partially* indistinguishable = a statistical reduction.

## [VERIFIED] Hard reduction = the automorphism factor, nothing more

For every geometric readout, `Inv(F)` is exactly a subgroup of `μ₆ = ⟨λ,−1⟩` (from `Aut(E)`):

| readout | Inv(F) | why |
|---|---|---|
| ε (μ₃-orbit label) | full μ₆ (order 6) | even + μ₃-invariant |
| sextant | μ₂ = {±1} | even, but μ₃ *permutes* the phase |
| norm-band | μ₂ | μ₃-invariant only on the core (slippage `c≠0` breaks it on the flap) |
| y-parity | μ₃ (order 3) | β fixes y; −1 flips parity |

**No readout has `Inv(F)` larger than μ₆.** ⇒ **the only cheaply-usable reduction of "what D
could be" is the known automorphism factor `|Aut| ≤ 6`** (the `√6` Pollard-ρ speedup). This is
the |Aut| bound restated in the reduction framing — and it is what the framing was made to detect.

## [NO shadow — a null-mismatch artifact caught] the soft spectrum

First pass flagged ε, sextant, y-parity with off-μ₆ `max A_F(k)` at **6–7σ** above a *shuffle*
null (control clean). **Audited and retracted:** a full shuffle destroys the μ₆-orbit structure
that these readouts have *by definition* (ε lives on `n/6` orbits, not `n` points), so its
self-agreement max is intrinsically lower than the real readout's — the "σ" was the null being
wrong, not a signal. Against the **correct μ₆-invariant null** (random function constant on μ₆
orbits, matched marginal):

| p | ε realMaxA | μ₆-invariant-null mean | z |
|---|---|---|---|
| 547 | 0.7363 | 0.7379 | **−0.05** |
| 1051 | 0.7143 | 0.7250 | **−0.39** |

Real value **at or below** the correct null. **No soft/partial shadow beyond μ₆.**

**Even had it survived, it would not be a usable reduction:** `A_F(k)` is a self-similarity of
the readout under `d↦kd`, computable directly from the public key (`[k]P` then read) — it gives
no new information about `d`.

## Verdict + how it fits the reframe

- **Information-theoretically:** the full reduction exists (`P` determines `d`), and v16 showed
  the joint (x,y) *shadow* is real (the odd half x can't see). But that reduction needs `U` ⇒ the DLP.
- **Computably (the threat-relevant sense):** the only usable reduction of "what D could be" is
  the automorphism factor `≤6`. No sub-automorphism soft shadow survives a correct null.

**Method catch (recorded):** when testing a readout with an intrinsic symmetry, the null MUST
carry that symmetry. A shuffle that breaks μ₆-invariance manufactures a 6–7σ phantom. Same
wrong-baseline failure mode as earlier this session — the control-row/null must match the
structure of the object.

## Un-shut
- The **information-level** shadow (v16) is real; the open question is a *partial* computable
  version (a cheap readout capturing a fraction of the joint (x,y) alignment).
- Accumulation across many readouts is bounded here too: they all share `Inv ⊆ μ₆`, so their
  joint reduction saturates at the μ₆ factor — no coherent super-additive reduction found.
