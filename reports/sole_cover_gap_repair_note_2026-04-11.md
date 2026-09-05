# Sole Cover Gap Repair Note

Date: 2026-04-11

## Status

The current issue in `v10.3`/`v10.4` is best understood as a **manuscript-integrity gap**, not as evidence that the overall structural route is false.

What has been exposed is:

- the present write-up does not cleanly distinguish **actual retained speeds** from **their residue classes modulo \(n\)**,
- some key arguments in the dropped-unit branch silently switch from the former to the latter,
- and that switch has not been justified.

So the gap is real, but it is localised in the write-up of the dropped-unit mechanism. It does **not** by itself produce a counterexample to the theorem, and it does **not** invalidate the broader structural picture already developed across the project.

## The exact issue

In the current manuscript, the Sole Cover route uses the interval
$$I_d = [L/n,\; L/(n-1))$$
and argues that every retained non-divisible runner is at floor state \(0\) there.

As written, that step depends on treating retained runners as though they lie in
$$\{1,\ldots,n-1\}.$$
This appears explicitly in:

- [lrc_proof_v10_3.md#L276](/Users/trentpalelei/Desktop/Math%20Ex/lrc_proof_v10_3.md#L276)
- [lrc_proof_v10_3.md#L282](/Users/trentpalelei/Desktop/Math%20Ex/lrc_proof_v10_3.md#L282)

and similarly in the late-window dropped-unit argument:

- [lrc_proof_v10_3.md#L630](/Users/trentpalelei/Desktop/Math%20Ex/lrc_proof_v10_3.md#L630)

But elsewhere `E_{\rm non}` is the set of actual retained non-divisible speeds, and
$$L_0 = \mathrm{lcm}(E_{\rm non})$$
is formed from those actual speeds:

- [lrc_proof_v10_3.md#L249](/Users/trentpalelei/Desktop/Math%20Ex/lrc_proof_v10_3.md#L249)

Those are not the same objects.

If
$$e = qn + r,\qquad 1 \le r \le n-1,$$
then on \(I_d\) one has
$$\frac{eb}{L} = q\frac{nb}{L} + r\frac{b}{L},$$
and since \(nb/L\) ranges over \([1,\; n/(n-1))\), the floor state is not determined by the residue \(r\) alone. In particular, it is not generally true that
$$\left\lfloor \frac{eb}{L} \right\rfloor = 0$$
throughout \(I_d\).

That is the real gap.

## What this does not show

This issue does **not** show:

- that the theorem is false,
- that the residue-coverage perspective was misguided,
- that the dynamic floor-reset mechanism is useless,
- or that the older searches and proofs were pointing in the wrong direction.

What it does show is that the manuscript still owes a valid bridge between:

1. actual speed data,
2. residue-class ownership phenomena,
3. and the floor-state arguments used to expose a gap.

So this is a repair problem, not a disproof.

## Parts of the manuscript affected

The most exposed components are the dropped-unit route:

- Lemma 5.2 (Sole Cover)
- Lemma 7.1 and the prime dropped-unit branch
- Proposition 11.3 and Remark 11.4
- Lemma 11.3a (Dual Sole Cover)
- any argument that uses `E_{\rm non} \subset \{1,\ldots,n-1\}` or `e \in \{1,\ldots,n-1\}` for retained runners

The broader audit should also include hypotheses that are currently phrased as omitted elements of `\{1,\ldots,n-1\}`:

- Theorem 9.2c
- Lemma 9.4
- the Unit-Complete statements in §9 and §11

This does **not** mean the dynamic mechanism fails. It means those statements also need to be rewritten so it is explicit whether they are about:

- omitted **residue classes**, or
- omitted **actual speeds**.

## Most likely repair direction

The right repair is to split the proof data into two layers.

### Layer A: actual speed data

For each retained non-divisible speed \(e\), write
$$e = q_e n + r_e,\qquad r_e \in \{1,\ldots,n-1\}.$$

The proof must keep track of:

- the residue \(r_e\),
- the quotient \(q_e\),
- and the induced floor function
$$t_e(b) = \left\lfloor \frac{eb}{L}\right\rfloor.$$

### Layer B: residue ownership data

The inversion map and the unit/non-unit dichotomy are residue-level mechanisms. These likely remain the correct conceptual objects, but they must be phrased as statements about the residue profile
$$\bar E_{\rm non} = \{r_e : e \in E_{\rm non}\} \subseteq \{1,\ldots,n-1\}.$$

Then one must prove a genuine bridge from Layer A to Layer B.

## Repair tracks

There are two plausible routes.

### Track 1: rebuild the dropped-unit branch with chamber control

Replace the current floor-0 Sole Cover window by a valid chamber statement:

- identify a nontrivial interval of fibres on which the floor patterns of retained runners are controlled,
- prove that on at least one such chamber the missing unit residue cannot be covered,
- then use counting or chamber width to recover \(x_0 \ge 1\) and the stronger quantitative bounds where needed.

This is probably the cleanest manuscript repair if the dropped-unit branch is to remain genuinely static.

### Track 2: re-route more of the dropped-unit branch through the dynamic mechanism

Instead of forcing a floor-0 or late-window uncovered residue, one might try to:

- encode the missing unit information as a residue-level omission,
- target a floor-reset event whose departing residue is that missing obligation or cannot be legally inherited,
- and absorb more of the dropped-unit branch into a unified handoff-failure framework.

This would make the paper more unified conceptually, but it may require more rebuilding.

## Immediate concrete tasks

The next repair pass should do the following, in order.

1. Introduce separate notation for actual retained speeds and residue representatives.
2. Audit every occurrence of `E_{\rm non}` to decide whether it refers to speeds or residues.
3. Mark every proof step that currently assumes retained runners lie in `\{1,\ldots,n-1\}`.
4. Rewrite the statement of the dropped-unit branch in residue-language plus an explicit bridge lemma.
5. Reassess Theorem 9.2c and Lemma 9.4 under the same speed/residue separation.
6. Only after that, decide whether the cleanest repaired version is still two-track (static + dynamic) or should become more dynamic.

## Working conclusion

The right stance is:

- the gap is real,
- it matters,
- but it is not a reason to abandon the proof programme.

The conceptual evidence gathered across the project still points to the same governing picture:

- unit obligations are rigid,
- non-units are subgroup-limited,
- and full obstruction should fail because coverage cannot be reassigned freely.

The repair task is to express that picture with the actual speed layer handled honestly.
