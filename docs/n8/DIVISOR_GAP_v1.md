# The divisor-closed gap, measured in profiles — and a correction

Lean: `experiments/n8/SmallModuli_v1.lean` (6 theorems, 0 errors, all `[propext, Quot.sound]`
— no `Classical.choice`). Scripts: `global_centre_v1.py`, `divisor_gap_v1.py`,
`divisor_gain_v1.py`.

---

## 0. Correction to `DIVISOR_ORDER6_v1.md`

That document ended: *"The open middle band was `8 ≤ bᵢ ≤ 27`, twenty values. It is now
`bᵢ ∈ {8,9}`, two values."* That is true **about values of `b`** and misleading **about
profiles**, which is the thing that matters. Measured over 60,000 sampled divisor-closed
5-quotient profiles:

| class | share of profiles |
|---|---|
| every quotient `≥ 28` — the **old** proved threshold | **0.60%** |
| every quotient `≥ 10` — the **new** proved threshold | **7.33%** |
| every quotient `≤ 9` — `q = 1`, proved below | 0.77% |
| mixed, but spanning at most a ratio-7 window — proved below | 5.87% |
| **mixed, OPEN** | **86.0%** |

The `28 → 10` improvement is real and it is a twelve-fold increase in covered profiles
(`0.60% → 7.33%`, a gain of 6.73 points). It is **not** a near-closure of the category. The
bulk of divisor-closed profiles are **mixed** — some quotients small, some large — and neither
the old `b ≥ 28` route nor the new `b ≥ 10` route ever addressed them. A homogeneity hypothesis
is what both routes need, and most profiles are not homogeneous.

The open profiles do clear; the proofs simply do not reach them. Witnesses found immediately:
`[4,8,9,24,36] → q = 5`; `[2,15,28,35,70] → q = 9`; `[3,4,20,30,240] → q = 34`;
`[3,8,12,36,42] → q = 10`; `[2,4,6,9,18] → q = 3`.

## 1. The small end closes outright — **[PROVED]**

`L(b) = ⌈(b-1)/8⌉ = 1` for every `2 ≤ b ≤ 9`, so the single candidate `q = 1` sits in the clear
window of every modulus in that range.

* `SmallModuli.clear_one` — `2 ≤ b ≤ 9 ⟹ q = 1` clears `b`.
* `SmallModuli.clear_one_fails` — and it fails from `b = 10`, so `9` is exactly its reach.
* `SmallModuli.profile_clear_one` — a profile with every quotient `≤ 9` needs no search.

This closes the `{8,9}` residual of §0 **for homogeneous small profiles**, not in general.

## 2. The reach of one candidate is a ratio-7 window — **[PROVED]**

For `0 < q < b` the residue is `q` itself, so clearing is `b ≤ 8q+1 ≤ 7b`
(`SmallModuli.reach_window`), i.e.

```
    (8q+1)/7  ≤  b  ≤  8q+1 .
```

A single candidate therefore covers exactly a ratio-7 span of moduli
(`SmallModuli.profile_clear_of_window`). **[VERIFIED]** where it fires, on 11,200 profiles, it
always clears. This is the `n-1 = 7` constant appearing as the reach of one candidate, and it
says precisely why profiles spanning more than a factor of seven need a witness argument: one
candidate cannot see both ends.

## 3. Route closed: a global reflection centre — **[CLOSED, with the reason]**

The clear window `[L,U]` is preserved by `r ↦ c - r` exactly when `c = L + U`, and
**[VERIFIED for `b = 2..25`]**

```
    b % 8 ∈ [2,7]  ⟹  c = b      (centre  0 mod b)
    b % 8 ∈ {0,1}  ⟹  c = b - 1  (centre -1 mod b)
```

which is the two-centre law already on record. A **global** reflection `q ↦ C - q` therefore
needs `C ≡ 0 (mod bᵢ)` at good moduli and `C ≡ -1 (mod bⱼ)` at obstructed ones — solvable by
CRT **iff every good modulus is coprime to every obstructed one**.

That condition almost never holds here, because divisor-closed moduli share factors by
construction. **[VERIFIED]** a global CRT centre exists in **22.8%** of profiles against
**22.5%** for the all-good case already proved — a gain of 0.3 points.

So the reflection route to `|S| ≥ 2` is **exhausted at the all-good case**. Extending `|S| ≥ 2`
past it needs a different mechanism, not a better centre. Do not re-attempt the centre.

## 4. Where the divisor-closed category stands

| class | status |
|---|---|
| every quotient `≤ 9` | **[PROVED]** `q = 1` |
| every quotient `≥ 10` | **[PROVED]** order-6 rounding (`DivisorOrder6`) |
| moduli spanning at most a ratio-7 window | **[PROVED]** one candidate |
| every quotient `≤ 7`, via `210`-coprimality | [PROVED] but **narrow** — 240 profiles under `m = 6000` |
| **mixed, spanning more than a ratio-7 window** | **[OPEN]** — 86% of profiles |
| the whole category | **[VERIFIED — exhaustive]** 185,729 profiles, `m < 500`, 0 failures |

The honest summary is that three homogeneity-hypothesis theorems now cover about **14%** of
divisor-closed profiles, up from about **1.4%**, and the open 86% is a single named class:
mixed-scale profiles. That class, not the value of any threshold, is the frontier.
