# LRC `n=all` Forced Conclusion Memo (v1)
**Date:** 2026-03-07  
**Inputs:** canonical gap/status docs, theorem-track notes, `M1-M3` framework, Gap-2 note, NZ0 note, essentiality program, and the synthesis artifacts created in this review pass.

## 1) Candidate master structures adjudicated

### Candidate A: universal alternating-sum positivity
Form:
`x0 = N + sum_{k=1}^{n-1} (-1)^k S_k > 0`.

Strength:
- directly matches the rational-all-`n` reduction,
- naturally covers `S3-GENERAL`,
- could absorb multidiv and Xi residual if period-safe mass is translated into moment positivity.

Weakness:
- current pack does not yet show how local non-unit exit geometry forces this inequality directly.

Verdict:
- keep as the strongest **global** master theorem candidate,
- not enough evidence yet to treat it as the unique unifier.

### Candidate B: complementarity / component run-cap theorem
Form:
- obstruction cannot persist long enough on any `B_div` component to erase the required safe mass.

Strength:
- matches `G4B-COMP-CAP` exactly,
- already explains much of the composite branch anatomy,
- plausibly feeds period-safe mass after summation.

Weakness:
- by itself it does not yet explain Xi residual / outside-band prime safe mass or all multidiv occupancy.

Verdict:
- strongest **local geometric** theorem candidate.

### Candidate C: subgroup-opacity / coset-essentiality theorem
Form:
- non-unit runners cover only subgroup cosets; vacating a coset forces exposure unless forbidden coincidence occurs.

Strength:
- best local explanation of non-unit exits,
- aligns with `G4B-NONUNIT-Z0`, `COMPOSITE-N`, and the essentiality program.

Weakness:
- too local to close global occupancy branches by itself.

Verdict:
- best local engine inside Candidate B, not a full master theorem on its own.

### Candidate D: period-summed outside-band safe-mass theorem
Form:
- safe mass remains positive after summing across all interior `t_div` periods, not just canonical lower/top bands.

Strength:
- directly matches Xi residual / outside-band data,
- best fit for prime residual and multidiv affine routes.

Weakness:
- weak on pure local exit geometry and component cap arguments.

Verdict:
- strongest **global counting** theorem candidate short of full alternating-sum positivity.

## 2) Minimal-counterexample review
Any genuine counterexample surviving the current pack would have to satisfy all of the following:

1. It lies in rational Case-2 with `L > 2n`, outside already closed small-`L` branches.
2. It avoids the closed prime one-div near-complete route from `§17.20`.
3. It is not resolved by prime regular-`k` multidiv closure.
4. Every relevant obstruction component is long enough to defeat complementarity despite current unit/boundary/pure-exit partial theorems.
5. Every non-unit coset transition fails to expose a residue in a way not already ruled out by current NZ0 routing.
6. Safe mass outside canonical bands is still insufficient even though current data show it spread over the full interior `t_div` range.
7. The dangerous-set multiplicity profile concentrates enough mass in high overlaps to force `x0 < phi(n)` despite all low-order exact identities and certified small-`n` behavior.

This is already a very rigid profile. It suggests the remaining frontier is structural, not numerical.

## 3) Forced outcome
The review does **not** support Outcome C.

The evidence also does **not yet** justify Outcome A with theorem-grade confidence, because the pack still separates naturally into a local exposure problem and a global occupancy problem.

Therefore the correct forced conclusion at this stage is:

## Outcome B: two irreducible master problems remain

### Master Problem 1: local exposure / complementarity geometry
This problem governs:
- `G4B-COMP-CAP`
- the composite non-unit regime
- the essentiality bridge (`E2-E4`)

Working statement:

> In the unresolved composite/non-unit rational frontier, full obstruction is locally unstable because a unit or non-unit transition must expose an uncovered residue or coset, forcing a safe event and hence a component cap.

This is Candidate B powered by Candidate C.

### Master Problem 2: global occupancy / period-summed positivity
This problem governs:
- `MULTI-DIV`
- `S3-GENERAL`
- Xi residual / outside-band prime safe mass

Working statement:

> In the unresolved rational frontier, even when canonical bands show no safe mass, the full period-summed or lattice-occupancy count remains positive; equivalently, the dangerous-set union cannot saturate the full lattice.

This is Candidate D aiming toward Candidate A.

## 4) Why Outcome A is not yet justified
A single theorem may still subsume both master problems, but the current pack does not yet prove that the local exposure theorems and the global occupancy theorems are formally equivalent.

At present:
- the composite branch is driven by exit-local and coset-local geometry,
- the prime residual / multidiv branch is driven by outside-band accumulation and occupancy positivity.

The bridge between these two scales is plausible, but not yet canonical.

## 5) Why Outcome C is rejected
The current branch split is too redundant to be the final architecture:
- `G4B-COMP-CAP` and `COMPOSITE-N` are clearly the same local geometric family,
- Xi residual / outside-band safe mass is clearly not an isolated curiosity but the prime manifestation of the global occupancy problem,
- multiple open notes already point back to the same shared objects: alpha-state transitions, residue cosets, obstruction components, dangerous-set occupancy, and period sums.

So the frontier has already compressed below the original branch count.

## 6) Recommended priority order

1. Finish **Master Problem 1** first:
   - promote `G4B` from partial local theorems to full component-cap integration,
   - package composite non-unit exposure in theorem-grade form,
   - make E2/E3/E4 serve this branch directly.

2. Then attack **Master Problem 2** explicitly as a global theorem:
   - either period-summed outside-band positivity,
   - or direct alternating-sum / occupancy-deficit positivity.

3. Re-test for Outcome A only after both master problems are stated in the same shared-object language.

## 7) Practical implication for the program
Do not treat the next stage as “prove one more local lemma.”

Treat it as:
- one local theorem program about exposure and complementarity,
- one global theorem program about occupancy and period-summed safe mass.

If those two programs later collapse to one theorem, that will be a theorem-level synthesis, not an assumption made in advance.
