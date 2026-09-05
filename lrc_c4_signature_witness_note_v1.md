# `C_4` Signature-Level Witness Note v1

## Purpose

This note is the first exact follow-up after the active-core exactification pass.

The previous exact result showed:

- minimal active core is too coarse,
- but the remaining theorem should still be finite and exact.

This note refines that statement using the bounded exact calibration
`v_1=1`, speeds in `{2,...,17}`.

The new probe is
[lrc_c4_signature_witness_probe_v1.py](/Users/trentpalelei/Documents/Claude%20Library/lrc_c4_signature_witness_probe_v1.py).

---

## 1. Exact bounded signature data

Work with the exact induced `C_4` partition from the active-core certifier.

For a full-cover tuple, define its **ordered active signature** to be the exact
cell-by-cell list of active runner service states on that partition.

In the bounded exact window:

- full-cover subsets: `422`,
- distinct ordered active signatures: `226`.

Their multiplicities are exactly:

- `128` signatures of multiplicity `1`,
- `98` signatures of multiplicity `3`.

So every collision in the bounded window is a three-way collision.

---

## 2. Main bounded finding

Among the `226` exact ordered active signatures:

- `216` have a nonempty common bounded witness intersection,
- `10` do not.

Equivalently, the ordered active signature already determines a common bounded
witness family in the overwhelming majority of exact bounded cases.

So the exactification did not destroy the finite theorem program. It sharpened it:

> the real remaining obstruction is concentrated in `10` exceptional
> three-way signature collisions.

---

## 3. Shape of the exceptional collisions

Each bad class has multiplicity `3`.

In every bad class:

- the active `C_4` schedule is identical,
- the three tuples differ only in the inactive low-speed profile,
- the witness sets split according to that inactive profile.

Typical example:

- `(2,3,5,6,7,8,9,10,11)` has bounded witnesses `13/55, 42/55`,
- `(2,4,5,6,7,8,9,10,11)` has bounded witnesses `7/22, 15/22, 17/55, 38/55`,
- `(3,4,5,6,7,8,9,10,11)` has bounded witnesses `21/44, 23/44, 26/55, 29/55`.

So the failure of pure active signature is not chaotic. It is a controlled
inactive-profile ambiguity.

---

## 4. Corrected theorem target

The exact bounded data now points to a more precise next theorem object:

> **active signature plus inactive profile**,
> not minimal core alone.

In the bounded calibration, refining by the inactive low-speed set removes the
empty-intersection problem entirely.

That refinement is still bounded and empirical at this stage, but it strongly
suggests the right general theorem shape:

\[
\text{full-cover witness} = \text{active `C_4` signature} + \text{external inactive phase data}.
\]

So the next exact theorem target should be:

1. define the general external inactive data attached to a full-cover tuple,
2. show that active signature plus that inactive data determines a witness family,
3. prove that the bounded exceptional triples are exactly the model for the
   general ambiguity mechanism.

---

## 5. What to keep from the exactification pass

Still valid:

- the exact folded `C_4` finite object,
- the exact active threshold `40/9`,
- the exact 6-runner catalogue,
- the exact bounded `422 / 146 / q<=5` calibration.

Now refined:

- the remaining theorem is not “minimal core -> witness,”
- it is closer to “ordered active signature + inactive profile -> witness.”

That is the right next rigorous step.
