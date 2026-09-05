# CORRECTION — v10's two-mechanism lever enumeration is not exhaustive

**Date:** 2026-07-30 · **Scope of this correction:** the *Framing* section of
`masked_structure_findings_v10.md` only. **v10's results are not corrected** — see §3.

---

## 1. What is corrected

`masked_structure_findings_v10.md:8-12`:

> "Our levers reduce to two mechanisms, each with a *provable* ceiling: **symmetry** (bounded by
> `|Aut(E)|=6`) and **single-object equidistribution** (`O(p^{-1/2})`, vanishing). So scaling, if it
> exists, must live where *neither* reaches."

Two defects, both at the `[PROVED]` bar that `feedback_closure_grade_2026_07_28` sets for this
vocabulary:

**D1 — an unproven exhaustive enumeration stated as a premise.** "Our levers reduce to two
mechanisms" is a completeness claim over an open space. Nothing establishes it. The phrase "each with
a *provable* ceiling" is true of the two named mechanisms and silently transfers its authority to the
enumeration itself, which has no proof.

**D2 — "must" inherits D1.** "scaling … must live where *neither* reaches" is a moved quantifier: it
converts "we found two bounded levers" into "all levers are bounded, therefore the residue is
located". `btc_puzzle_investigation/CLAUDE.md` names this as the subtlest false-closure case —
a true fact about the objects examined, read as a fact about the space.

---

## 2. A concrete reason the enumeration fails

Not a general objection — a measured one. `twist_channel_types_v1.py` shows the μ₃/GLV
twist acts on three readout channels by three **different types of operation**:

| channel | twist acts on | measured law | consequence on complete orbits |
|---|---|---|---|
| multiplicative (χ₃, χ₆) | the **value** | `χ₃(βx) = ω·χ₃(x)` — one ratio, 400/400 x | **exact annihilation** |
| additive (`e_p(bx)`) | the **dual variable** | `F̂(b) = F̂(ωb)`, 1008/1008; exact zeros **0/1008** | 3× redundancy, never zero |
| geometric (sextant/flap) | partially folded | shift +4: 77%, +0: 22% | no clean law — neither |

v10's framing counts "symmetry" as **one** mechanism with **one** ceiling, `|Aut(E)| = 6`. That
ceiling bounds an orbit-counting lever. It does not bound the *weight/isotypic* structure of a
readout, and its force differs per channel: in the multiplicative channel μ₃-covariance is strong
enough to annihilate a statistic identically, while in the additive channel the same symmetry only
replicates magnitudes. A single scalar ceiling cannot summarize three inequivalent group actions.

This is demonstrated rather than argued: the same symmetry that yields `E3 = 0` exactly on a
λ̂-closed set yields `0/1008` exact vanishings in the additive channel on a β-closed set. Same
symmetry, same object, opposite behaviour.

---

## 3. What is NOT corrected

- **Every measured result in v10 stands.** β-inv/random = 0.98–1.00 at the S₄ decomposition step;
  no core‖flap target-dependence (<2%); decomposition density = the `|F|³/|E|` heuristic for CM and
  non-CM alike; over-dispersion 8–19× Poisson, identical CM vs non-CM. All `VERIFIED` at
  p ≤ 10009 with a matched non-CM control, as v10 states.
- **v10's own scope discipline is sound and is not being criticized.** It states its scope and grade
  (line 48), names what is untested (`S₅⁺`, easy-target predictability, not secp's p), keeps the
  over-dispersion line explicitly "un-shut" (lines 39-44), and says outright that the finding is
  "a scoped, quantified negative … not a wall claim." Only the Framing paragraph overreaches.
- **The v9 → v10 contrast is real.** The β-invariant factor base gave 1.5× at the S₃
  relation-counting step and 0.98–1.00 at S₄. That is a genuine, quantified non-propagation. Note
  independently (`CORRECTION_v32_mu3_diffset_controls_v1.md` §5) that the v9 1.5× is *not* an
  artifact of the kind found in v32: its statistic is a relation **count**, which cannot
  self-annihilate under orbit closure.

## 4. Replacement wording

Delete the two-mechanism premise. What the evidence supports:

> Two lever mechanisms have been examined and each is bounded on the objects tested: symmetry
> (orbit-counting, bounded by `|Aut(E)| = 6`) and single-object equidistribution
> (`O(p^{−1/2})`). Both bounds are `VERIFIED` at p ≤ 10009 for the readouts tested. **This is
> not an enumeration of the space of levers**, and it locates nothing: the μ₃ symmetry alone
> acts by three inequivalent operations across the multiplicative, additive and geometric
> channels, and `|Aut| = 6` bounds only the orbit-counting one.

**Also minor, same file, line 26:** "This strengthens (does not merely re-null) the bounded-lever
picture." A scoped null at S₄ is a scoped null; it does not strengthen a picture whose premise (D1)
is unproven. Recommended: "This is a second, independent scoped null — at the step whose cost
governs ECDLP rather than at S₃."
