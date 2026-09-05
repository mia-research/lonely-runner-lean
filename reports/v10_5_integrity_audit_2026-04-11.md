# v10.5 Integrity Audit

Date: 2026-04-11

## Purpose

This note records the main places in `lrc_proof_v10_5.md` where the manuscript still needs a full speed-versus-residue audit after the initial integrity-repair pass.

The broad distinction is:

- `E_{\rm non}` = actual retained non-divisible speeds,
- `R_{\rm non}` = residue classes represented by those speeds modulo \(n\).

Any statement about omitted classes, dropped units, or unit-complete configurations should be checked against that distinction.

## Already repaired in v10.5

The following items were handled directly in the manuscript:

- explicit introduction of residue support in §1.2 and §5.1,
- removal of the invalid floor-$0$ speed reduction in §5.3,
- conversion of Lemma 5.2 into an explicit repair target,
- marking of the prime and composite dropped-unit counting branches as templates under repair,
- addition of an integrity note around the dynamic floor-reset section.

## Still requiring audit

### 1. Static dropped-unit branch

These sections now depend on the repaired version of Lemma 5.2 and should be revisited once that bridge is rebuilt:

- §7 prime one-divisible branch
- §10 prime counting bridge
- §11.2--§11.3a composite one-divisible branch
- §12 multiple-divisible branch, especially any step that argues from absent residue classes directly

### 2. Dynamic branch terminology

The following statements still use representative-style language and need to be rewritten in actual-speed/residue-support form:

- Theorem 9.2b
- Theorem 9.2c
- Theorem 9.3
- Lemma 9.4
- Corollary 11.0 and the branch summaries that cite Unit-Complete

The arithmetic targeting mechanism in §9 may survive, but the quantifiers need to be checked carefully: "absent runner" and "absent non-unit" should likely become "missing residue class" plus an actual-speed bridge statement.

### 3. Prime quantitative branch

The floor-$0$ miss-set architecture in §10 still needs a valid chamber interpretation. In particular:

- `miss(0)` is currently residue-level data,
- the argument still owes a proof that an actual chamber realises the required retained-runner support pattern,
- the free-runner redesignation logic is still useful, but it belongs after the chamber bridge is repaired.

### 4. Composite late-window branch

Lemma 11.3a still contains the old representative-speed floor computation. The algebraic pattern may still be useful, but it must be rebuilt using:

- actual speeds \(e = nq_e + \rho_e\),
- explicit floor formulas on the proposed late window,
- and a proof that the relevant residue support omission produces a genuine uncovered residue.

## Most important next mathematical tasks

1. Prove a correct replacement for Lemma 5.2.
2. Decide whether the replacement is:
   - a static chamber lemma, or
   - a dynamic handoff lemma absorbing more of the dropped-unit branch.
3. Rebuild Lemma 11.3a only after the replacement for Lemma 5.2 is clear.
4. Re-audit Theorem 9.2c and Lemma 9.4 under the same notation split.

## Working status

`v10.5` is now a more honest integrity-repair draft:

- it no longer silently relies on the invalid `E_{\rm non} \subset \{1,\ldots,n-1\}` reduction in the static branch,
- but it is not yet a theorem-secure final manuscript.
