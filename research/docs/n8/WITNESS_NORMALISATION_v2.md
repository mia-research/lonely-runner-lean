# Witness normalisation — v2, with two corrections to v1

Supersedes `WITNESS_NORMALISATION_v1.md`. The theorem is unchanged and still `[PROVED]`.
**Two claims made in v1 are corrected, both against v1's own author.**

## Correction 1 — the novelty framing is withdrawn

v1 §1 said the result "sharpens the statement of the conjecture, and it holds at every order." The
**theorem** is unaffected: `ReachRule.witness_normalised` is proved, Lean, axiom-clean, and the
derivation here is independent — it falls out of the fold, not out of the classical geometry.

What is withdrawn is the implied novelty. A literature check (not done before v1 was committed)
shows witness-denominator normal forms are an actively worked area, and at least one established
normal form already exists: the maximum is attained where two sine curves cross, which forces the
optimal time to be rational **with denominator the sum or difference of two velocities**. There is
also a Fan–Sun conjecture of the shape `q = np + k`, and recent work specifically on denominators in
the six-speed spectrum.

**Status of `A/(n·s)` relative to that:** unknown. It is not obviously the same normal form — ours
is `n` times a single speed, theirs a sum or difference of two — but the question was never asked.
Until a proper citation check is done against the actual papers, this is:

> `[PROVED]` as a statement; **no novelty claim attached**; relationship to the sine-crossing normal
> form and to Fan–Sun **unchecked**.

The general rule this instance illustrates: an absence in my own information became an implied
claim about the field. That is the project's recorded deflationary failure mode running in reverse,
and it is the same fault.

## Correction 2 — the Hunter–Kounias lead is dead as stated

v1 §4 recorded it as "the live lead", with figures (`1.5` single measure, `0.375` generic pairwise
overlap, `4.5` needed) asserted from a density heuristic and **not computed**. Now computed, exactly,
over 400 random 7-reading profiles from `[2,200]`:

```
  mean single-reading bad measure :  1.4984      (asserted 1.5)     OK
  mean pairwise overlap           :  0.3702      (asserted 0.375)   OK
  max-spanning-tree overlap sum   :  2.1692 .. 3.1023
  needed to force a gap           :  > 4.5
  best Hunter-Kounias bound       :  |union| <= 10.5 - 3.1023 = 7.3977   vs the 6 needed
```

The asserted figures were right. **The lead is still dead:** the best observed spanning tree reaches
`3.10` against the `4.5` required, so the bound lands at `7.40` where `6` is needed — short by
`1.40`, and not close. Scope: 400 random profiles, readings `[2,200]`, `n = 8`. Not a proof that no
spanning tree ever reaches 4.5; a measurement that none came near it.

**Not a live lead. Do not pick it up again without a reason the measurement does not already cover.**

## Unchanged from v1

The theorem, the two refutations (`s = s*`: 18,809 counterexamples; largest reading: 794), what
stands (0 failures in 244,790 when any reading may supply the witness; at least two readings always
work; supplying reading never the smallest), and the counting wall (each reading kills ~1/4 of the
candidates, seven give `7/4 > 1`, matching the classical `10.5` against `6`). §2, §3 and the first
two paragraphs of §4 of v1 carry over verbatim.
