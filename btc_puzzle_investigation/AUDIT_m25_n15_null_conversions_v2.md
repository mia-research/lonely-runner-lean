# AUDIT — the M25 & N15 null-conversions (v2): reconciled with the completed external review of M26

**Date:** 2026-08-27
**Supersedes:** `AUDIT_m25_n15_null_conversions_v1.md` (this session). v1's two null-leg verdicts are
**unchanged and carried forward**; v2 folds in one fact the user supplied — **M26 has already been
reviewed externally** — which moots v1's "route M26 to the external eye" recommendation and re-targets it.
**No grade is moved here** (owed to any further external eye + `compile-diff`); this records.

**What changed from v1.** v1 flagged that "M25 → null" buries M26 (the surviving x-closure positive) and
recommended adding M26 to the external-review prompt. The external review of M26 **already happened**:
`POSITIVE_FINDINGS_ADDENDUM_4_v1.md` A3 (audit of 20 external-agent reports) is an **independent external
reproduction** of M26's mechanism (β-orbit Semaev collinearity {P,λP,λ²P} satisfies S₃≡0 at 100% CM /
0% non-CM, = GLV relation-triples), explicitly "consistent with that [H2/M26] resolution." So M26 is not
awaiting an external eye — it **got one, and was corroborated.** v1's core finding stands and is
strengthened; only its recommendation is superseded.

---

## Object 1 — M25 (Semaev CM relation-yield). Three legs; the "null" names one.

| leg | object | status (traced to source) | external review? |
|---|---|---|---|
| **H1** | CM yield on a **random** base, `#E`-matched | **null — cofactor/subgroup-confinement artifact.** SOUND (matched control, powered, r=0.96 mechanism). | flanked same-direction by ADDENDUM_4 **D1–D3** (crypto-payoff extraction nulls on real keys) |
| **H2 / M26** | **x-closure**: β-invariant (CM) `V` beats generic order-3 orbits | **VERIFIED POSITIVE**, CM-specific, mechanism = GLV relation-triples; reaches secp, bounded to a known **√6** constant factor (not a keyspace reduction). | **YES — externally reproduced** (ADDENDUM_4 A3). |
| **cap-v5** | cost-side / does the lever move the index / scaling to super-constant, pooled `|V|=4..10` | **UNGRADED / PENDING** (`RESULT_semaev_cm_lever_capability_v5.md:8`, run died on usage limit). | **no** — un-reviewed remainder |

**H1 null remains SOUND** (v1 §Object-1 detail carried verbatim by reference): whole-group sampling is a
*matched* control, not a CM-destroyer (the same battery found **M26 positive**, so it does not null CM
indiscriminately); `T1_underF8`≈0 powered at `|V|=4,5,6`; r=0.96 mechanism with a non-tautological
internal control. The external batch's `D1` (d mod {2,3,6} extraction from a public key = **≤0.006 bits**,
ground-truth on real secp keys, `POSITIVE_FINDINGS_ADDENDUM_4_v1.md:133`) points the **same** direction on
a neighbouring channel — additional, independent, same-sign evidence, not a re-test of H1.

**Correction to v1's framing ("M26 is buried").** M26 is **not lost from the corpus**: v15 records it as
H2-RESOLVED and ADDENDUM_4 A3 adds external corroboration. The compression is confined to **two summary
surfaces** — v18's one-line flag row (`M25 | [A−] | [null …]`, accurate for the H1 leg it names) and
`EXTERNAL_REVIEW_PROMPT_M25_N15_v1.md` (frames "M25 … [null]" with no mention of M26). Read alone, either
would make M26 invisible; the underlying artifacts carry it. That is a narrower, truer statement than
"buried" — trace the items, not the tag.

**The one un-reviewed M25 remainder:** cap-v5 (does the lever grow to super-constant / change the index).
Raw `T1` grows log-shaped to `|V|=8` (`RESULT_semaev_cm_relation_yield_v4.md`, M_log best, ΔAICc −30 vs
flat), but the **corrected-sampler null (E_F8) was only verified to `|V|=6`.** cap-v5 Arm C targets exactly
this and is PENDING. This is the live M25 edge — not H1 (sound), not M26 (reproduced).

---

## Object 2 — N15 (joint readout). Null SOUND within order-≤2; the joint channel is the un-reviewed remainder.

**Unchanged from v1.** The tested null (9 singletons + 36 pairs) is fired-surrogate-sound: instrument live
(ε=1 plant fires at exactly `log₂3`, `RESULT_n15_joint_readout_confinement_v1.md:35`), powered (`:49`), the
`b=128` marginal tested-not-banked (5 non-reproductions + fresh-seed wash, `:58–71`), and scrupulously not
read as a closure (`:12–18`, "rising floor, not a ceiling"). A second isolated experiment-designer read
judged it EARNED (`:108`).

**The live remainder — deviation D1 (`:8–9, 94–96`).** The preregistered primary was the **full joint C**;
declared bias-unestimable and swapped for the **order-≤2** family. The order-**≥3 / full-joint-C** channel
— i.e. the "**joint**" in "joint readout" — is the named untested cost. The external batch did **not** close
this: ADDENDUM_4 `D1` tested the *reverse* direction (public-readout → d mod 6 extraction ≈ 0 bits), a
neighbouring channel, not "does an order-≥3 cheap function of `d` predict the joint readout." **N15's joint
channel is the un-reviewed remainder**, and the right target is a **bias-corrected joint-MI estimator** (was
"unestimable" true, or estimable-with-a-correction-not-attempted?), or the GLV-orbit-aware / lattice-of-
residues families the prompt already names.

---

## Verdicts (decidable) and re-targeted recommendation

| object | verdict | external eye still owed? |
|---|---|---|
| **M25 H1** | null SOUND (+ same-direction external nulls D1–D3) | no |
| **M25 M26** | positive, VERIFIED, **externally reproduced** (ADDENDUM_4 A3), bounded √6 | **no — done** |
| **M25 cap-v5** | PENDING (super-constant/index question) | run it (design-gate owed) |
| **N15 order-≤2** | null SOUND, scoped | no |
| **N15 order-≥3 / full-joint-C** | OPEN — D1's named, unestimated channel = the actual joint question | **yes** |

**Recommendation (revised from v1).** Do **not** spend a fresh external eye re-reviewing M26 (reproduced)
or re-confirming the two sound null legs. The external-review prompt should be **re-scoped**, not amended
to add M26: point it at the two genuinely un-reviewed remainders — **(1) N15's order-≥3 / full-joint-C
channel with a bias-corrected estimator, and (2) cap-v5's scaling arm** (does the corrected-sampler null
hold past `|V|=6`; does the lever reach super-constant). If `EXTERNAL_REVIEW_PROMPT_M25_N15_v1.md` is
reused, its Object-1 checks (built for the H1 null) are now the *least* informative part; its N15 checks
1–2 (D1 seam, predictor-class adequacy) are the ones that hit the live remainder — keep and sharpen those.

**Bias-audit note (net).** The suppression check comes back **clean at the artifact level and mostly clean
at the summary level**: both null legs are correctly fired; M26 (the positive that the null direction would
have wanted to lose) is corpus-carried *and* externally reproduced. The residual is only that two summary
surfaces (v18 flag row, external-prompt v1) compress M26 out of view — a labeling artifact, not a lost
finding. The genuine open work is not a re-audit; it is the two PENDING channels above.
