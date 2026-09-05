# RESULT — exposed-pubkey relations: the "found none" null was UNCONTROLLED; redone with a control

**Date:** 2026-07-18. Script `pubkey_relations_controlled_v1.py`. Prompted by the challenge that
systemic negative bias may have buried structure / a search reduction. This is the joint-SET-relation
avenue (the one thing that survives the ECDLP scramble), re-examined in-scope (points only).

## The gap found

`pubkey_relations.py` searched for small algebraic relations among the 7 exposed unsolved pubkeys
(`P_i=c·P_j`; `P_i−P_j` = solved pt or `small·G`; `P_i=a·P_j+b·G`; X-collisions) and printed "none".
**KNOWN_FACTS §(exposed points) recorded "The tested algebraic relations among the exposed points
found none" as a fact.** But `pubkey_relations.py` has **NO firing control** — no planted relation
confirming the search could detect one. By this project's binding Anomaly-Drill rule (*a null is
uninformative until a matched/planted control shows the test could have seen the thing*), that null
was **uninformative**, and elevating it to a fact was the documented negative-bias failure mode.

## Redone with controls

`pubkey_relations_controlled_v1.py` adds, per test: a PLANTED relation the test must detect, and a
MATCHED random-key control (7 independent keys in the same bit-ranges, #135–165 region). Result:

| test | PLANT control | RANDOM control (×3 seeds) | REAL exposed points |
|---|---|---|---|
| T1 `P_i=c·P_j`, `c≤4096` | **fires** (detects c=7) | 0 / 0 / 0 | **0** |
| T3 `P_i=a·P_j+b·G`, `a≤64,\|b\|≤2^20` | **fires** (detects a=5,b=12) | 0 / 0 / 0 | **0** |
| T2 `P_i−P_j` = solved or `small·G` | — | — | **0** |

**Informative scoped null:** the 7 exposed unsolved points carry no small-coefficient algebraic
relation, **identical to random independent keys, with the detector proven able to see a planted
relation.** This is now a controlled result, not an assumed one.

## Scope (the honest boundary — not "no relations")

`c≤4096`, `a≤64`, `|b|≤2^20`. A larger-coefficient relation `Σ aᵢ Pᵢ = O` is **not excluded**: for
`k≥3` independent 256-bit keys a genuine relation needs coefficients `~n^{1/k}` (e.g. `~2^43` for the
7 points), and finding one **from points alone is a hard problem** (you cannot LLL curve points
without the scalars — that is the DLP). So the tractable relation range is exhausted and null; the
intractable range is where a generator-left relation could hide, and it is inaccessible in-scope.

## What this does and does not change

- **Does:** converts an uncontrolled null (a bias artifact) into an informative one. The exposed
  points are relation-free at small coefficients, same as random — **consistent with independent
  keys, no curve-side joint structure at the tractable scale.**
- **Does not:** find a leak or a search reduction. And it does not exclude a large-coefficient /
  generation-left relation (out of tractable reach, and the generation side is out of scope per the
  standing `no-PRNG` directive).

## UPDATE — full data (36k) + the counting argument that CLOSES it analytically

`joint_relations_36k_v1.py` ran the same test on the **36k constructed (known-generator) set** —
30000 large keys, ~10⁵× more pairs than the 82. Plant `c=5` fired; **REAL 36k = RANDOM = 0** relations
(ALL and large≥100). This is not luck: the **counting bound** governs it.

> **Expected # of relations `d_i = c·d_j` (`|c|≤B`) among `M` independent keys `= M²·2B/n`.**
> For `M=30000`, `B=2^11`, `n≈2^256`: **`~3×10⁻⁶⁵`**. One expected relation needs `B ~ n/(2M²) ~ 2^225`.

So **pairwise small-coefficient relations are NULL BY COUNTING for independent keys** — the 7-, 82-,
and 36k-tests all go null for the *same analytical reason*, not for want of power. A hit would require
the generator to have **correlated** the keys; the 36k (our MT pipeline) shows none, behaving as
independent keys. This upgrades the avenue from an empirical null to an **analytical closure** (of
pairwise small-coeff relations). **Still open / out of reach:** large-coefficient relations (DLP-hard
to find from points); generation-side distributional structure (out of scope per `no-PRNG`).

## Correction to the record

- `KNOWN_FACTS_secp256k1_and_keys_v5.1.md` line ~214 "found none" → re-grade to **`[VERIFIED,
  controlled]` with the scope above** in the next KNOWN_FACTS version. The claim survives, but its
  prior grade overstated its evidentiary status (uncontrolled).
