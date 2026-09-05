# AUDIT — the v4 R1 run: method, result, conclusion (incl. a direct suppression-bias check)

**Date 2026-08-07.** Adversarial pass on `semaev_cm_relation_yield_v4.py`, its m=3 run
(`..._v4_results.jsonl`, `semaev_v4_m3_run.log`), and my reported conclusion ("v3's +0.21 CM
relation-yield lever was an artifact; H1 null; H2 x-closure fires"). Audited in **both** directions —
did I over-conclude a null (suppression), and did I under-control a surviving positive (inflation).

## The load-bearing worry: did the fixes SUPPRESS a real effect?

Changing F1 (randomize twist) + F2 (#E-bracket) + F8 (random_point) at once, then watching a +0.21
signal vanish, is the exact shape of the project's one-way suppression failure. Tested three ways:

1. **Class-stratification (existing v4 data).** T1_j0 by sextic class of B0: class means −0.06…+0.04,
   all near zero; Pearson(T1_j0, a_p) = −0.06. **No sextic-class or trace dependence.** So F1
   (randomizing the twist) did not average away a class-specific effect — there is none at this
   magnitude.
2. **Class 0 = B=1's class specifically.** B=1 is a 6th power ⇒ sextic class 0. Class 0 in v4 is null
   (mean +0.029, n=4). v3's fixed twist is not a hidden carrier of +0.21.
3. **Decisive B=1 isolation** (`audit_isolation_B1.py`): v3's EXACT twist j0=(0,1) under v4's proper
   #E-bracketed matching → **T1 = −0.014 (n=5, 2/5 pos, perm_p=0.68), null.** And **7/12 primes DROPPED
   because B=1 is "not bracketable"** — its #E sits at the EDGE of the non-CM distribution. That edge
   position is the mechanism: v3's un-bracketed "nearest match" was necessarily **one-sided**, and with
   `quo ∝ 1/#E` (forced law A1) a one-sided gap manufactures a positive T1. The 5 central-#E primes give
   null.

**Verdict on the worry: the null is NOT a suppression.** The +0.21 was `#E`-leakage from one-sided
matching of B=1's edge-#E twist. Confirmed by three independent angles + the mechanism (C4 below shows
`quo` IS #E-sensitive, supplying the leak). The "artifact" conclusion stands.

## Method audit

- **F6 reproducibility CONFIRMED** — two independent smoke runs byte-identical (0 logQ mismatches).
- **F1 exonerated as a "killer"** — no class/trace dependence (above); randomization did not dilute a
  real effect.
- **The artifact mechanism is identified and consistent:** edge-#E twist + one-sided nearest-match +
  `quo∝1/#E`. C4 (high-#E-half vs low-#E-half non-CM, the strong control) shows the needed #E-sensitivity:
  mean −0.010 (|V|=4, p=0.13) / −0.018 (|V|=5, p=0.09) — high-#E ⇒ lower quo, sub-0.05 but present.
- **Residual method caveats (not blocking, but named):**
  - the bracket-via-twist-conditioning DROPS un-bracketable primes (2/24 main; 7/12 for B=1). This is a
    selection on #E position; it does not bias the CM-yield question (no #E-dependence) but the B=1
    isolation is consequently thin (n=5).
  - F8 (random_point) vs v3's gens()[0]-multiples was changed simultaneously; not independently isolated
    from F2. Both are corrections (random_point is the uniform sampler); neither points to v4 hiding a
    real effect, but "which fix removed the leak" is F2 by the mechanism above, not proven exclusive.

## Result audit

- **H1 null is robust and multi-angle:** v4 full run T1_j0 = −0.010 (|V|=4, p=0.77) / +0.012 (|V|=5,
  p=0.30), sign flips between cells, n=22; class-independent; trace-independent; B=1 isolation null.
  Power floor T1≈0.092 ⇒ v3's 0.21 is **excluded**. Scope: any residual effect **< 0.092 log-units is
  NOT excluded** — the null is "no CM relation-yield effect at v3's magnitude survives #E matching," not
  "exactly zero."
- **Scaling:** −0.010 → +0.012 over |V| = no growth; but there is no positive base effect for growth to
  act on, so Scaling is moot here (not evidence of a bounded-vs-growing lever — evidence of no lever).
- **H2 (x-closure) R2≈1.6, p=0.0011, reproducible** — real and stable. BUT the grade "novel CM x-closure
  effect" is **OVER-LABELED**: the control `randV` is 3k *independent* elements while `βinvV` is k
  β-orbits (fewer d.o.f., closed under β). R2>1 could be **generic order-3 orbit-closure**, not β/CM
  specificity. Correct control (owed): β-orbits vs **random order-3 orbits** of the same shape. As it
  stands: "a β-closed factor base raises single-target quo vs an unstructured one" — weaker than "CM".

## Conclusion audit

- **"v3's +0.21 was an artifact" — SUPPORTED** (checked against suppression bias from 3 angles;
  mechanism identified). Correct, disciplined conclusion.
- **"R1 CM relation-yield lever null at model scale" — SUPPORTED, scoped** (|T1|<0.092, m=3, |V|∈{4,5},
  22 model primes; m=4 untested; sub-floor effects untested). Not a closure of "CM index-calculus
  structure."
- **"H2 x-closure is a novel CM effect" — TEMPER** to "structured (β-closed) V raises quo vs unstructured
  V; β/CM specificity NOT isolated." Needs the order-3 structure-matched control before any CM claim.
- **Honest net:** the audit → rebuild → re-run caught a false-positive lever before it was graded. The
  one surviving positive (H2) is real but its CM interpretation is not yet earned.

## Owed next steps
1. H2 structure-matched control (β-orbits vs random order-3 orbits) — decides if x-closure is CM-specific.
2. (optional) widen the B=1 isolation (more primes, or don't require bracket — measure the leak directly
   by the #E-gap sign) to n≫5 for a fully powered confirmation of the mechanism.
3. m=4 remains spec-completeness only (no positive base effect to scale).
