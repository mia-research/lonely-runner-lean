# Two §2 items converted from verified to proved

`EXISTENCE_MAP_v4` §2 lists claims that were exhaustively verified but had no proof. Two are
now theorems. Lean: `experiments/n8/CoverCount_v1.lean` (4), `experiments/n8/DivisorOrder6_v1.lean`
(6). Zero errors, all axiom-clean. Scripts: `divisor_order6_v1.py`, `divisor_order6_check_v2.py`.

---

## 1. The covering count — **[PROVED]**, was verified on 9,323,468 movers

> Mover `d` covers exactly `c · gcd(d,e)` of the flank's `e` openings, `c` its blocked classes
> mod `q = e/gcd(d,e)`.

`CoverCount.cover_count_gcd`. It needs no arithmetic of `inWay`: the openings are `k ∈ [0,e)`,
the pattern depends only on `k mod q`, and `q ∣ e`, so each blocked class contributes exactly
`e/q = gcd(d,e)` openings. The counting lemma `card_filter_mod` is proved by induction on the
number of periods.

`CoverCount.shadow_needs_count` gives the consequence: if the movers' blocked sets cover every
opening then `Σ_j c_j · gcd(d_j,e) ≥ e`. **Necessary, not sufficient** — at the extremal set's
surviving flank it reads `24 ≥ 16` and the flank is clear anyway.

## 2. Divisor-closed large quotients — threshold **28 → 10**

`DIVISOR_CLOSED_v1.md` proves the reduction (`Rescale.divisor_reduces`): every constraint
collapses to a unit one, two of the seven readings are free (`sᵢ = m` gives `b = 1`, `sᵢ = 1`
gives `b = m`), and **five** moduli remain. A witness is an integer `q` with

```
    b ≤ 8*(q mod b) + 1 ≤ 7b      for each of the five moduli b.
```

Five constraints is an **order-6** question, and order 6 is proved in this tree — `intLRC_six`,
axiom-clean, in-house. That document recorded the real→integer conversion as **untried**, with
the slack named: `1/6` available against `1/8` needed. This does the conversion.

Order 6 supplies a real `t` with `dist(t/b, ℤ) ≥ 1/6`, i.e. `t ∈ [bm + b/6, bm + 5b/6]` for
some integer `m`. Round to the nearest integer `q`; then `r = q - b*m` satisfies

```
    b - 3 ≤ 6r        and        6r ≤ 5b + 3 .
```

Both ends then follow by integer linear arithmetic, and the threshold is **`b ≥ 10`**
(`DivisorOrder6.clear_of_order6`).

**[VERIFIED]** 361,500 band points across `b = 10..259` and six values of `m`: all clear.

**Tight.** At `b = 9` the band point `t = 15/2` rounds to `q = 8`, which is blocked; `b = 8`
fails likewise. So `10` is exactly the threshold of this argument, not a convenient bound.

### The correction that mattered

A first pass derived `b ≥ 15`, from the **real** bound `r ≤ 5b/6 + 1/2`. That is lossy: `r` is
an integer, so the true constraint is `6r ≤ 5b + 3`. Keeping integrality moves the threshold
from 15 to 10 — five extra values of `b`. The gap is visible directly:

| `b` | max integer `r` with `6r ≤ 5b+3` | `8r+1` | `7b` | |
|---|---|---|---|---|
| 8 | 7 | 57 | 56 | fails |
| 9 | 8 | 65 | 63 | fails |
| 10 | 8 | 65 | 70 | ok |
| 14 | 12 | 97 | 98 | ok |
| 15 | 13 | 105 | 105 | ok |

The rational relaxation only closes from `b = 15`; `10 ≤ b ≤ 14` is exactly where integrality
does the work, which is why the Lean proof splits there rather than calling `omega` once.

### What this closes and what it does not

The previous large-quotient threshold was `b ≥ 28`, obtained from an order-**7** route whose
margin is `1/7 − 1/8 = 1/56`. Using order 6 the margin is `1/6 − 1/8 = 1/24`, and it is the
**count of surviving constraints** — five, not six — that licenses order 6.

| class | status |
|---|---|
| every quotient `bᵢ ≥ 10` | **[PROVED]** here |
| every quotient `bᵢ ≤ 7` | [PROVED] but **narrow** — needs `m` divisible by five of `{2..7}`, 240 profiles under `m = 6000` |
| any quotient in `{8, 9}` | **[OPEN]** |
| mixed small (`≤ 7`) and large quotients | **[OPEN]** — Frontier 1B, untouched |

The open middle band was `8 ≤ bᵢ ≤ 27`, twenty values. It is now `bᵢ ∈ {8, 9}`, two values.

### Scope of the Lean statement

`DivisorOrder6.clear_of_order6` takes the order-6 band as a **hypothesis** and proves the
conversion. Wiring that hypothesis to `intLRC_six` — which is stated for integer speeds, so the
speeds `1/bᵢ` need scaling by `lcm(bᵢ)` — is **not formalised**. The conversion is the part that
was owed and is now proved; the plumbing is not done and should not be counted as done.

`EXISTENCE_MAP_v4` §2 and §3 need a v5 to absorb both results, and that promotion is gated by
`compile-diff`.
