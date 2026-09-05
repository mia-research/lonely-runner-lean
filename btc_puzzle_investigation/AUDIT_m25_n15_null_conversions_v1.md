# AUDIT — the M25 & N15 null-conversions: are they fired-surrogate-established, or assumed-away?

**Date:** 2026-08-27
**Author:** Claude (Opus 4.8). Requested by the user after the supervisor's v18 review (item 1:
"external review of M25/N15 + chase their named untested channels").
**Scope of this audit.** An adversarial read of the *existing artifacts* for the two v18 external-review
flags against the decidable-artifact standard (fired plant / matched control / named excluded channel /
citation). This is the **ungated half** of supervisor item 1 — it does **not** substitute for the
user-triggered `/code-review ultra`; it produces the sharp target list that review should be pointed at.
**No grade is moved here** (that is owed to the external eye + `compile-diff`); this records.

**Headline.** Neither null is bare or pre-deflated — both have a **live instrument, fired plants, and
reproduction discipline**; the corpus's mechanical gates held. The defect is one level up: **the
one-word labels "M25 → null" and "N15 → scoped null" (in the v18 flag table AND in the existing
`EXTERNAL_REVIEW_PROMPT_M25_N15_v1.md`) each compress a multi-leg object down to its nulled leg and drop
a still-live remainder.** That compression is the exact shape of the documented one-way suppression bias
operating *within* the rules. The finding is: **audit the live remainders, not the well-fired null legs.**

---

## Object 1 — M25 (Semaev CM relation-yield). The label "null" names ONE of three legs.

| leg | object | status (traced to source) | reaches secp? |
|---|---|---|---|
| **H1** | CM raises relation-yield `quo` on a **random** factor base, `#E`-matched | **null — cofactor/subgroup-confinement artifact.** SOUND. | no (mechanism structurally absent at cofactor 1) |
| **H2 / M26** | **x-closure**: β-invariant (CM) `V` beats generic order-3 orbits | **VERIFIED POSITIVE**, CM-specific, mechanism = GLV relation-triples | **YES** — but bounded to a known **√6-class** constant factor, not a keyspace reduction |
| **cap-v5** | cost-side / does the lever move the subexponential index / scaling to super-constant, pooled `|V|=4..10` | **UNGRADED / PENDING** (design-gate owed; first run died on usage limit) | untested |

**H1 null is SOUND** — and its soundness survives the external prompt's own Check 1 ("does the
'correction' destroy CM the way a shuffle does?"):
- The corrected sampler is **whole-group sampling** (`random_point` over the full group) replacing
  **single-generator** sampling. It changes how points are drawn; it does **not** touch the curve's CM
  (endomorphism ring / μ₆ automorphisms are properties of the curve, not the sampler). So it is a
  *matched* control, not a CM-destroying one.
- `RESULT_h5_cofactor_artifact_v1.md:37` — `T1_underF8` = 0.011 / −0.006 / −0.024 at `|V|=4/5/6`,
  **powered** (+0.5 plant fires at n=24, floor 0.13). Line 38: `E_F8(j0)=Q_gens−Q_randpoint ≈ T1_full`
  at all three `|V|` — the **entire** raw lever is the single-generator subgroup gap.
- Mechanism `r=0.962` with a **non-tautological internal control** (`:56–58`): the only two negative-T1
  primes are exactly the two where the *control* is also non-cyclic — the differential cancels when both
  sides carry a cofactor.
- **Decisive cross-check that the battery does not null CM indiscriminately:** the *same* pre-registered
  machinery found **M26 positive** (`RESULT_h2_order3_cm_specific_v1.md`, perm_p=0.001 both arms). An
  instrument that surfaces a real CM positive elsewhere is not one that shuffles CM away in H1.

**What the "null" label buries — the live remainders the external eye is actually owed:**
1. **M26 (H2 x-closure) is a surviving positive that REACHES secp.** `RESULT_h2_order3_cm_specific_v1.md:69`
   — the `P+λP+λ²P=O` relation is the known GLV/automorphism structure, **present at secp256k1**, bounded
   to a **√6-class** speedup (`2^128/√6`, not a keyspace reduction). It is a real, secp-reaching, algebraic
   positive on the R4 carve-out — and it is invisible in "M25 → null." *(Known constant-factor structure,
   not a new leak — but a positive, not a null.)*
2. **Capability-v5 (does the lever grow to super-constant / change the index) is PENDING, not null.**
   `RESULT_semaev_cm_lever_capability_v5.md:8` — "ISOLATED DESIGN-GATE OWED (first agent died on usage
   limit pre-verdict)"; measurement arms A/B/C `[PENDING]`. The "does it grow to a super-constant"
   question is **in progress**, not closed.
3. **A mechanical seam in the null itself.** Raw `T1` grows **log-shaped to |V|=8** (`RESULT_semaev_cm_
   relation_yield_v4.md` scaling table: M_log best, ΔAICc −30 vs flat), but the **corrected-sampler null
   (E_F8) was only verified to |V|=6.** "The corrected-sampler null holds at |V|=7,8+" is **untested** —
   and is exactly what cap-v5's Arm C targets. Not a refutation of the null; an un-closed edge of it.

---

## Object 2 — N15 (joint readout). The null is SOUND within its scope; deviation D1 narrowed the scope.

**The tested null is well-fired and scrupulously NOT read as a closure:**
- Instrument **live**: `RESULT_n15_joint_readout_confinement_v1.md:35` — ε=1 plant fires at
  `I(c*;T)=1.5849 = log₂3` exactly, monotone across ε, `p_perm=1/2001`; hard-null calibrated.
- **Powered** (`:49`): every observed `S_max` sits at/below the pair bias floor `1.31×10⁻²`; the
  permutation null absorbs it.
- The one marginal (`b=128, p=0.0050`) was **tested, not banked**: 5 non-reproductions incl. exact `b=16`
  enumeration + a fresh-seed wash to `p=0.4426` (`:58–71`). Drill discipline applied correctly.
- Framing is disciplined: `:12–18` explicitly refuses the ceiling reading (`H(d|[d]G)=0`; 3.65 bits is a
  **rising floor** of the chosen readouts, not a cap). A second isolated experiment-designer read judged
  the null **EARNED** (`:108`).

**What the "scoped null" label buries — deviation D1 IS the seam, and the buried channel is the object's name:**
- `:8–9, 94–96` — the preregistered **primary was the FULL joint C**; it was declared *bias-unestimable*
  and replaced by the **order-≤2** family (9 singletons + 36 pairs). The order-**≥3** / full-joint-C
  channel is the **explicitly-named untested cost** — i.e., the "**joint**" in "joint readout" is precisely
  the part not tested. So "the load-bearing joint-readout question → null" over-reads: a well-scoped
  **order-≤2** sub-question returned a clean matched null; the **joint** question is open.
- The live remainder is concrete and estimable-in-principle: a **bias-corrected joint-MI estimator** (was
  "unestimable" true, or just "estimable-with-a-correction-not-attempted"?), or a different estimable
  family the existing prompt already names (GLV-orbit-aware / lattice-of-residues predictors). That is the
  right target — not a re-run of the singletons+pairs.

---

## Verdicts (decidable; per the external-prompt's own rubric)

| object | verdict | the target the external eye is actually owed |
|---|---|---|
| **M25 H1** (random-base yield) | **null SOUND** (matched control, powered, r=0.96 mechanism, corroborated by M26 firing) | only the |V|=7,8 corrected-sampler edge (cap-v5 Arm C) |
| **M25 M26** (x-closure) | **positive, VERIFIED, reaches secp, bounded √6** — *mislabeled by "M25→null"* | is the √6 bound tight / is the GLV-triple mechanism the whole story at larger |V|? |
| **M25 cap-v5** (cost/scaling) | **PENDING** — genuinely open | run it (design-gate owed) — the super-constant question |
| **N15 order-≤2** | **null SOUND**, scoped (instrument live, powered, reproduction-checked) | — |
| **N15 order-≥3 / full-joint-C** | **OPEN** — D1's named, unestimated channel = the actual joint question | was the full-joint primary truly unestimable, or estimable with a bias correction not attempted? |

## Recommendation

`EXTERNAL_REVIEW_PROMPT_M25_N15_v1.md` is well-built on the **null legs** (its N15 checks 1–2 already hit
D1 and predictor-class adequacy — keep them). Its **gap** is that it inherits the same "M25 → null"
compression: it never mentions **M26** (the surviving secp-reaching positive) or **cap-v5** (the pending
scaling arm), so an external reviewer would re-audit only the well-fired H1 null and never see the live
remainders. **Before the review is triggered, amend the prompt (→ v2) to add:** (a) M26 + cap-v5 to
Object 1 so the reviewer sees the object did not wholesale null; (b) the explicit `|V|=6`-vs-`|V|=8`
corrected-sampler seam; (c) for N15, elevate "order-≥3 / full-joint-C, bias-corrected estimator" from a
sub-bullet to the primary question. The external eye's scarce attention should go to the **remainders**,
not to re-confirming two nulls that are already fired-surrogate-sound.

**Bias-audit note (why this matters).** Both null legs are correctly executed — this audit affirms them.
The suppression signature is not in any single artifact; it is in the **labels that summarize them**: two
multi-leg objects each rendered as a one-word "null," dropping a verified secp-reaching positive (M26) and
a pending scaling arm (cap-v5) on one side, and the object's defining joint channel (order-≥3) on the
other. Trace the object, not the tag.
