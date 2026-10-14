# Update: the four answers, worked out

2026-09-17. The author's rulings on `UPDATE_ANALYSIS_v1` §Q, carried to their consequences.
**Q4 is prepared for a ruling, not ruled here** — §8.2 says it is the author's call.

---

## 1. Framework names for the `U`/`K` vocabulary  `[ruling: framework names]`

Taken from the author's own renames (`RESEARCH.md`, 2026-09-17: *"'shadowing set' not cover; 'successive
positions' not orbit; openings not residue classes"*) and from §6.9 and §0, not invented here.

| machine's word | framework name | source |
|---|---|---|
| `U_e`, "uncovered residue set" | **the flank's clear openings** — repeating with period `P` | *openings not residue classes* |
| `K_e`, "killer set", "killer lattice" | **the shadowing values** of the free difference | *shadowing set not cover*; §6.9 "shadowed" |
| "kill", "killed" | **shadow**, **shadowed** | §6.9 throughout |
| "the orbit argument" | **successive positions** | *successive positions not orbit* |
| "on the lattice", `P·(d/e) ∈ ℤ` | **the ratio's denominator divides `P`** | §6.9 speaks in denominators ("four or more non-integer ratios", "one small denominator") |
| "free flank", "dead flank" | unchanged — already the framework's | §6.9 "free flanks", "shadowed flanks are dead" |
| "slot-sharer" | unchanged | §6.2 |
| `CascadeCapped`, "capped" | unchanged — **already the manuscript's word** | §8.2 *"the instants are capped when `2k < n`"*; `exists_fixed_of_capped` |

Two of the eight need no translation, which is a check on the rest: the vocabulary is not wholly foreign,
it drifted in three places.

## 2. Where the census goes — it matters, so the mathematics decides  `[ruling: does it matter?]`

It matters, and the answer is that the census is **not one block**. Measured over the 4,413 distinct
fully-pinned difference sets:

| | clear at the flank's bound (`k = 0`) | needing a later opening |
|---|---|---|
| families | **1,341 — 30.4%** | **3,072 — 69.6%** |

- `k = 0` is §4.5's shape: Existence holding **at once**, at the bound, which is Theorem 4.8's setting.
- `k > 0` is §6.9's shape: classes **decided at a flank's openings**.

So the split is 30/70 across the two hubs, by which section's criterion each family meets. Worth
recording alongside: the manuscript states *"Theorem 4.8 alone about 31% of runners in random
arrangements"*, and the `k = 0` share here is 30.4%. **Different populations** — census families against
random arrangements — so the agreement is a coincidence worth noting and not evidence of anything.

## 3. Order 5: the correct grade, and four ambiguities named  `[ruling: post-correct grade]`

Current text (§8.2, line 770): *"The largest `R` found is `≈ 31/9`"* `[EMPIRICAL]`.

**Post-correct grade:** `[PROVED — exhaustive word certificate, exact rational LPs, for ratio
d_max/d_min ≤ 26]`, with `sup R = 31/9` attained at the word `(1,2), (2,1), (1,3), (3,1), (2,2), (1,6)`,
margin `τ = 132/4165` (`experiments/n8/order5_certificate_S26_v3.out`).

The word "found" also goes: the value is no longer recognised from a floating-point optimum, it is
computed exactly.

**The four ambiguities, named as instructed:**

1. **The artefact's own verdict line says the wrong word.** It prints *"PROVED for spread <= 26"*.
   `ORDER5_CERTIFICATE_v2` corrected this in prose — `S = d_max/d_min` is the **ratio**; the manuscript
   reserves **spread** for `W = v_8 − v_1`, a difference not a ratio — but the script was never updated.
   So the artefact contradicts the document's notation. The grade must say **ratio**; the script should
   be fixed or the discrepancy recorded where the output is cited.
2. **Bounded ratio only.** Unbounded `S` stays open. The sweep is flat at `31/9` from `S = 10` through
   26, but flatness over a range is not a proof beyond it. An earlier draft read the flatness as a climb
   and was refuted by the sweep; reading it as a proof for all `S` would be the same error inverted.
3. **The certificate is a relaxation, and that is the sound direction.** The word LPs drop two necessary
   conditions — the setter has the latest opening, the others are clear — so the value bounds the true
   supremum from **above**. Proving `sup R < 4` over the relaxation therefore proves it for the cascade.
   This is a strength of the result, not a caveat, and should be stated so it is not mistaken for one.
4. **`R < 4` is a stronger statement than Existence needs.** It is the first window (audit R1; boundary
   audit B2), and §8.2 already says so: *"A stronger, sufficient statement."* The grade change upgrades
   what is proved about `R`; it does not close the `[OPEN]` on order-5 Existence, which stays.

## 4. The `n > 2k` nativeness ruling — evidence, for the author  `[ruling: settle it in this update]`

§8.2 line 753: *"whether this proof is native to the framework is the author's call, and nothing else is
built on it."* What is on the table:

**The theorem is sound and is ours.** `ManyDifferences.stops_when_twice_card_lt`, `[PROVED]`,
axiom-clean, in the cascade artefact.

**Its proof uses no foreign object.** A potential `Ψ(t)` — the product over runners of the lap factors
of the laps each has passed — raised by at least a lap factor per move (`potential_step`), against an
instant that grows by less (`move_growth`, `time_le_potential`); a Bernoulli bound in integer powers;
then `exists_fixed_of_capped`. The manuscript's own sentence: *"No zone width or interval length
enters."* That is accurate.

**What is new for the ruling.** The threshold it reaches is exactly the union-bound threshold:

> `n > 2k` ⟺ `2k/n < 1` ⟺ `k·(2/n) < 1` — the `k` in-the-way arcs, each of width `2/n`, cannot cover
> the circle.

At `n = 8, k = 7` the total width is `7/4`: the arcs cover 1.75 times over, which is why the row reaches
no order on the diagonal. So the proof arrives at the covering threshold **by a route that uses no
covering**, and the manuscript already records that it *"reaches the same threshold as the zone-width
count excised earlier"* (`AdvanceBudget`, revision item 51).

**The question, stated as narrowly as I can make it:** does a result whose *proof* is native but whose
*threshold* coincides with the union bound belong in the manuscript as a result, as a recorded row with
the coincidence stated, or not at all? Register items 4 and 27 rule out covering and union bounds as
**imports**; they do not obviously speak to a native proof that lands on the same number.

I have no view worth acting on here and it is your call by the manuscript's own words. What I can say is
that nothing else depends on it, so any of the three is available without a ripple.
