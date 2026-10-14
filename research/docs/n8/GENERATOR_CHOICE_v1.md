# Seven generators, and how far the proved mechanisms reach

One more attempt at the single line item before the manuscript update. It did not close, but it
measured the gap sharply and produced one new theorem.

Lean: `experiments/n8/CardSix_v1.lean` (2 theorems, axiom-clean, built on `intLRC_seven`).
Scripts: `generator_choice_v1.py`, `union_of_mechanisms_v1.py`, `union_v3.py`, `card_six_v2.py`,
`blocker_five_v1.py`.

---

## 1. A correction, made before reporting

An earlier version of this run reported **100.00% certified**. It was wrong. The mechanism
labelled `M3` searched `q` from `L(s_k)` to `L(s_k)+8` and checked each candidate directly —
a bounded exhaustive check, not a theorem. That is `finite_check` restricted to nine points, and
it is the circular-rule failure mode already on this project's record (*"a scan reported 100%
because its endpoint rule was the whole candidate set"*). Dropped, and the honest figures are
below. The max-steps measurement in §4 shows a nine-point window is not universally enough
anyway.

## 2. New theorem: six constraints are covered — **[PROVED]**

`intLRC_seven` is ours and axiom-clean, and gives six distinct positive speeds a real `t` with
`circDist ≥ 1/7`. Since `1/7 > 1/8`:

* `CardSix.lonely_at_eight_of_six` — a subject whose differences collapse to ≤ 6 distinct values
  is lonely at order 8;
* `CardSix.margin_to_spare` — with `1/7 − 1/8 = 1/56` to spare at every speed.

The collapse happens exactly when the subject is the **midpoint** of two other runners, since
`circDist(d·t) = circDist(−d·t)`. **[VERIFIED]** 600/600 distinct sets of size ≤ 6 reach margin
≥ 1/7. (A first test reported 19 failures; its sweep was capped and never covered a full period.)

## 3. The generator is a free choice, and it moves the moduli

At generator `s_k` the modulus for blocker `s_i` is `s_k / gcd(s_i, s_k)` — it **changes with
`k`**. `DivisorOrder6` needs all moduli `≥ 10`; `SmallModuli.clear_one` needs all `≤ 9`. We do
not need that of every generator, only of **one**.

**[VERIFIED — 6,000 profiles each]** coverage by proved mechanisms, taken across all seven
generators:

| class | certified | breakdown |
|---|---|---|
| divisor-closed | **88.50%** | `M2` (all moduli ≤ 9) 5,031 · `M1` (all ≥ 10) 279 |
| general integer | **99.60%** | `M2` 3,586 · `M1` 2,383 · `M5` (the `-7` opening) 7 |

`M4` (`CardSix`) fires on 0 of these samples, since they were drawn with seven distinct readings.

## 4. The residual, measured

Every uncertified profile has a witness. **[VERIFIED]** over the seven generators, the fewest
steps above `L(s_k)` at which a clear candidate appears:

| class | min | median | mean | **max** | within 8 steps |
|---|---|---|---|---|---|
| divisor-closed | 0 | 0 | 0.33 | **30** | 99.70% |
| general integer | 0 | 0 | 0.09 | **3** | 100% |

Median **0** — for most profiles some generator's very first admissible candidate clears. But the
max is 30, so *"a witness lies within a fixed window above `L(s_k)`"* is **false** as a universal
rule, and cannot be the theorem. This is a lead with a measured shape, not a mechanism.

## 5. The line item, unchanged and now confirmed as the only gap

Everything around it is proved (`SYNTHESIS_v1` §4): reduction to candidates; at most `n−3 = 5`
active blockers per candidate (**[VERIFIED]** on 8,337,943 band-0 candidates, the generating and
unit readings block **0** times and the maximum is exactly 5); a real witness at margin `1/6`
from `intLRC_six`; and that rounding preserves clearing at every modulus `≥ 10`.

> **Owed:** show the order-6 rounding can be chosen to also satisfy the non-divisibility
> conditions at the moduli `≤ 9` — `b ∤ q`, and `b ∤ (q+1)` for `b ∈ {8,9}`.

**[VERIFIED — 8,000 profiles]** that condition is satisfiable in **100.00%**, and clears wherever
it fires. So the gap is a proof of satisfiability, not a search for what to prove.

Two routes were tried and neither closes it: forcing `q ≡ 1 (mod lcm of the small moduli)` clears
them all at once but costs 18.38 points of profiles; and choosing a homogeneous generator covers
88.69% but not the mixed-at-every-generator remainder.

Existence at order 8 remains open. One line item, with everything around it proved.
