# CT.1 Large-Runner Low-Thin Release Note

Date: 2026-04-12
Status: new repair target

## 1. Purpose

This note records the current correction to the large-runner selected-HIGH
route in the prime dropped-unit branch.

The earlier target was:

> no challenger reaches the selected HIGH residue before `b_2`.

That target is false.
Rare large-runner depth-`1` cases do exist.

The first replacement candidate mechanism was:

> after the selected HIGH residue transfers at `b_2`, the transfer fibre
> already contains an earliest-dropping LOW-thin residue, and that LOW-thin
> drop creates the first safe fibre.

This looked much closer to the real transport-instability mechanism than the
old non-arrival idea, and it remains an important intermediate model even
after later counterexamples to its strongest form.

## 2. Shared setup

Assume:

- `n` is prime,
- `b_0 = L/n` is fully covered,
- the selected start is a HIGH thin residue
  `r^* = a_high(e^*)`,
- `e^* = n q^* + rho^*`,
- and `q^* >= 1`.

Write

`b_2 = ((q^*+2)L)/e^*`

for the second reset of `e^*`.

In the first traced depth-`1` large-runner cases, the following happens:

1. another retained runner already covers `r^*` before `b_2`,
2. at `b_2`, `e^*` drops `r^*` and the burden transfers,
3. the first safe fibre occurs shortly after `b_2`.

So the question is not whether transfer can happen.
It can.
The question is why transfer still cannot stabilize full obstruction.

## 3. Explicit traced large-runner examples

Here are four explicit large-runner depth-`1` examples now checked by hand.

### Example A (`n=11`)

`E = (7,35,49,77,85,111,164,178,184,214)`

Selected start:

- `e^* = 184 = 11*16 + 8`,
- `r^* = 2`,
- `b_2 = 35740515797910`.

Transfer:

- at `b_2`, `2` transfers from `184` to `178`.

At the transfer fibre, the thin residues ordered by next drop begin with:

- `(7, 214, low, 35851856968620)`,
- `(1, 111, low, 36205607595080)`,
- `(5, 164, low, 37871386658490)`,
- `(2, 178, high, 38997766301340)`.

The first safe fibre is exactly

- `35851856968620`,

and the missing residue is exactly

- `7`,

which is the earliest-dropping LOW-thin residue from the transfer fibre.

### Example B (`n=11`)

`E = (1,14,38,51,75,104,175,185,205,209)`

Selected start:

- `e^* = 175 = 11*15 + 10`,
- `r^* = 5`,
- `b_2 = 28588034904`.

Transfer:

- at `b_2`, `5` transfers from `175` to `205`.

At the transfer fibre, the first thin residues by next drop are:

- `(2, 205, low, 28711082400)`,
- `(1, 51, low, 28851823000)`,
- `(5, 205, high, 30146636520)`.

The first safe fibre is

- `28711082400`,

with missing residue

- `2`,

again the earliest-dropping LOW-thin residue.

### Example C (`n=13`)

`E = (71,101,104,134,153,171,207,222,225,229,238,244)`

Selected start:

- `e^* = 207 = 13*15 + 12`,
- `r^* = 3`,
- `b_2 = 24816721006151820200`.

Transfer:

- at `b_2`, `3` transfers from `207` to `101`.

At the transfer fibre, the first thin residues by next drop are:

- `(1, 229, low, 25071709149035476200)`,
- `(2, 225, low, 25517428422796106888)`,
- `(11, 244, low, 26007301401577136550)`,
- `(9, 229, high, 26391272788458396000)`,
- `(6, 171, low, 26507023984899003000)`,
- `(3, 101, high, 29918819151272142000)`.

The first safe fibre is

- `25071709149035476200`,

with missing residue

- `1`,

again the earliest-dropping LOW-thin residue.

### Example D (`n=13`)

`E = (9,20,39,48,60,79,84,87,110,129,194,230)`

Selected start:

- `e^* = 194 = 13*14 + 12`,
- `r^* = 2`,
- `b_2 = 13064053242240`.

Transfer:

- at `b_2`, `2` transfers from `194` to `87`.

At the transfer fibre, the first thin residues by next drop are:

- `(12, 84, low, 13200137130180)`,
- `(8, 230, high, 13774056135840)`,
- `(3, 194, low, 13880556569880)`,
- `(2, 87, high, 16386377127120)`.

The first safe fibre is

- `13200137130180`,

with missing residue

- `12`,

again the earliest-dropping LOW-thin residue.

## 4. Extremal `n=7` prototypes fit the same pattern

The same LOW-thin release mechanism also appears in the old depth-`1`
`n=7` prototypes.

For example, for

`E = (2,6,7,8,9,10)`

with selected start

- `e^* = 6`,
- `r^* = 1`,

the burden transfers at

- `840`,

from `6` to `10`,

and the thin residues at the transfer fibre begin with:

- `(6, 10, low, 1008)`,
- `(0, 2, low, 1260)`,
- `(1, 10, high, 1260)`,
- `(4, 8, high, 1260)`.

The first safe fibre is exactly

- `1008`,

with missing residue

- `6`,

again the earliest-dropping LOW-thin residue.

The other three `n=7` depth-`1` prototypes show the same shape.

So the old extremal family and the new large-runner failures may already be
two manifestations of one post-transfer release law.

## 5. New candidate theorem target

The corrected large-runner target is no longer a non-arrival theorem.
It is the following:

**Candidate theorem `LR-LT`.**
In the prime dropped-unit selected-HIGH branch, suppose transfer occurs at
`b_2`.
Then at the transfer fibre there exists a LOW-thin residue whose next drop
time is minimal among all thin residues, and the first safe fibre occurs
exactly at that LOW-thin drop.

This is stronger and cleaner than the old transport story:

- the HIGH selected residue creates a controlled transfer state,
- that state already contains a privileged thin release object,
- and the first safe fibre is governed by LOW-thin release, not by
  indefinite burden carrying of the transferred HIGH residue.

## 6. Why this is promising

This candidate has three advantages.

### It matches all explicitly traced depth-`1` examples

At present this includes:

- the four `n=7` prototypes,
- the two `n=11` large-runner examples above,
- and the two `n=13` large-runner examples above.

In each case:

- transfer occurs,
- the transfer residue itself is HIGH,
- but the first safe fibre is produced by the earliest-dropping LOW-thin
  residue from the transfer fibre.

### It unifies the extremal and large-runner stories

So far the extremal family no longer looks like a separate branch.
It looks like the same release law in a smaller window.

### It points to a more realistic proof strategy

To prove `LR-LT`, one would want to show:

1. the transfer fibre always contains a LOW-thin residue,
2. some LOW-thin residue is earliest by next-drop time,
3. no other runner can re-cover that LOW-thin residue before its drop,
4. hence that drop creates the first safe fibre.

This is much closer to the old owner-set / upper-zone machinery than the
failed non-arrival route was.

## 6.1 Addendum from broader rare-case scans

Later on 2026-04-12, larger targeted rare-case scans produced more
large-runner depth-`1` examples.
Those scans keep the overall picture promising, but they also show that
`LR-LT` in the literal form above is still too strong.

### What survived the broader scan

Across the additional rare cases checked:

- depth-`1` remains genuinely rare,
- the first safe fibre is still very close to the first transfer,
- and the safe fibre is usually created by a single reset event.

In one larger batch, for example:

- `n=11`: `12` large-runner depth-`1` examples were found after
  `27964` full-cover large-runner starts,
- `n=13`: `8` large-runner depth-`1` examples were found after
  `61519` full-cover large-runner starts.

In those same batches:

- `19/20` transfers matched `b_2`,
- `18/20` safe fibres were created by a single reset event,
- and the event-delay from transfer to first safe fibre was still small.

So the broad structural picture remains:

> depth-`1` is sparse, transfer is usually near the selected HIGH release,
> and the post-transfer system destabilizes quickly.

### What failed

The literal candidate

> “the earliest-dropping LOW-thin residue always creates the first safe fibre”

is false.

Two failure types now appear.

#### Failure type A: the transferred HIGH residue itself is earliest

For

`E = (26,35,49,89,104,124,130,143,182,190)` with `n=11`,

the selected HIGH start is

- `e^* = 130`,
- `r^* = 6`.

Transfer occurs at

- `1469255788`,

from `130` to `182`.

At that transfer fibre, the first thin residue by next-drop time is

- `(6, 182, high, 1614566800)`,

not a LOW-thin residue.

And the first safe fibre is exactly

- `1614566800`,

with missing residue

- `6`.

So sometimes the transferred HIGH residue itself is the first true release.

#### Failure type B: an earlier LOW-thin drop is repaired

For

`E = (2,58,68,86,92,93,110,117,181,188,240,243)` with `n=13`,

the selected HIGH start is

- `e^* = 181`,
- `r^* = 1`.

Transfer occurs at

- `29622814551673200`,

from `181` to `240`.

At the transfer fibre, the first thin residue by next-drop time is

- `(8, 58, low, 30814536976165800)`.

But when runner `58` drops `8`, runner `188` already covers `8`, so no
safe fibre appears there.

The first safe fibre occurs later, at

- `31276755030808287`,

when runner `240` drops the transferred HIGH residue `1`.

So the earliest LOW-thin object is important, but it is not automatically
unrepaired.

### Refined target after the addendum

The best current statement is therefore weaker and more realistic:

**Candidate theorem `LR-TR`.**
In the prime dropped-unit selected-HIGH branch, once the post-transfer
state is formed, there exists a thin release chain of length `O(1)`;
the first safe fibre is produced by an early drop of a thin residue
from that chain, and the chain cannot be repaired indefinitely.

This is less elegant than `LR-LT`, but it is still much sharper than the
old non-arrival theorem.
It says the real object is a short thin-release dynamic, not a static
one-step sole-cover witness.

## 7. Current status

What is now solid:

- Lemma `S-B`,
- the exact challenger formula,
- explicit large-runner counterexamples to the non-arrival theorem,
- and a coherent replacement direction based on short post-transfer
  thin-release dynamics.

What remains open:

- a theorem-grade version of the refined post-transfer thin-release
  statement,
- especially a non-repair theorem showing why the release chain cannot
  keep healing past a bounded number of steps.
