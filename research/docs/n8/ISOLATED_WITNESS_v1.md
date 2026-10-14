# Where the 2.7% comes from

Lean: `experiments/n8/IsolatingPair_v1.lean` (4 theorems, axiom-clean; the two substantive ones
need only `[propext, Quot.sound]`). Scripts: `isolated_u_v1.py`, `isolating_pairs_v1.py`,
`isolated_cause_v1.py`.

---

## 0. A correction to how I stated it

`ODD_SUBLATTICE_v1` §4 said "the remaining 2.7% is real", implying a gap in existence. It is not.
The 97.3% measured runs of **≥ 2** consecutive admissible `u`. What existence needs is a run of
**≥ 1**, and that was **100%**: across 2,000 profiles carrying `b = 2`, the admissible set was
empty **0** times. The 2.7% is a statement about the **shape** of the witness set, not about
whether one exists.

What it does mean is worth having: an isolated admissible `u` has **both** neighbours blocked — it
is a **doubly-tight** witness.

## 1. The mechanism: it is `b = 2` one level up

In `q`-space the singleton `{2}` isolates, because clearing at `b = 2` is "`q` odd" and the odd
integers contain no two consecutive members.

In `u`-space **no single modulus isolates**, and among all pairs `b < b' ≤ 60` there is exactly
**one**:

```
    b = 5   admits   u ≡ 0, 1, 3, 4       (mod 5)
    b = 10  admits   u ≡ 1, 2, 3, 6, 7, 8 (mod 10)
    together         u ≡ 1, 3, 6, 8       (mod 10),   cyclic gaps 2, 3, 2, 3
```

**[PROVED — `IsolatingPair.five_ten_residues`]** the pair pins `u` to those four residues.
**[PROVED — `five_ten_no_consecutive`]** so it admits no two consecutive indices.
**[PROVED — `five_alone_not_isolating`, `ten_alone_not_isolating`]** neither modulus does this on
its own: `b = 5` admits `u ≡ 3, 4`; `b = 10` admits `u ≡ 1, 2`. The isolation is a property of the
**pair**, and `10 = 2·5`.

## 2. The full accounting

**[VERIFIED — 2,000 profiles carrying `b = 2`, 59 isolated = 2.95%]**, by minimal isolating
configuration:

| configuration | share of the isolated | admissible points | min cyclic gap |
|---|---|---|---|
| the pair `(5, 10)` | **61.0%** (36) | 4 of 10 | 2 |
| the quadruple `(3, 12, 16, 48)` | 35.6% (21) | 8 of 48 | 5 |
| `(10, 12, 15, 60)` | 1.7% (1) | 8 of 60 | 3 |
| `(12, 15, 20, 60)` | 1.7% (1) | 12 of 60 | 3 |

**[VERIFIED]** all four are **minimal** — no proper subset of any of them isolates. So the 2.7% is
not diffuse: it is four explicit configurations, one pair and three quadruples, and a single pair
accounts for nearly two thirds of it.

## 3. What this tells us about the open step

Forcing the parity moved the obstruction **from a singleton to a pair**. That is a real gain, and
it is measurable: in `q`-space the isolating configuration `{2}` occurs in essentially every
profile of interest; in `u`-space the isolating configurations occur in 2.95%.

It also says the obstruction is **not scale-invariant noise** but a short, enumerable list. A
proof of the open step need not handle "the 2.7%" as a mass — it must handle `(5,10)` and three
quadruples, each of which pins `u` to an explicit residue set that is written down above.

Whether that helps depends on the next question, which is untouched: **does the order-6 margin
argument transfer to the `u`-problem?** Its windows have different widths (`2/3` at `b = 3`,
`6/8` at `b = 8`, `7/9` at `b = 9`, `4/10` for the `(5,10)` pair) and are not centred as the
`q`-windows are. That remains the gap.

Existence at order 8 remains open.
