# Does the n=11 architecture translate to n=8 — and which axiom fails

2026-09-07. Applying the project's own default tool (`lrc_v11_6_n11_lens_retrospective`
Lesson 2: *the n=11 → general-n translation lens is the default reusable tool; apply it
BEFORE drafting analytical attacks*). Rosenfeld gives ground truth — LRC(8) is **true** —
but no analytic route. This asks what our own machinery gives.

**Read for this file:** the two n=11 memory topic files and the general-`n` SR-H record.
**Not yet read:** `eleven_lonely_runners_v33.md` and `lrc_n11_algebraic_lemma_v1.md`
themselves. The assessment below therefore rests on the recorded architecture, and the
axiom-failure in §2 is checked directly, not taken from the summaries.

## 1. The n=11 architecture, as recorded

A reusable triple (`lrc_v11_9_srh_n11_template`):

1. **Complementary Pairs Theorem.** Each runner blocks exactly **2** of the `n−1` AP
   witnesses `t_m = m/n` — the pair `{m, n−m}`.
2. **Coupling Principle.** All bad intervals move together as the free parameter varies.
3. **Baton-Pass Certificate.** An explicit witness (`t* = 69/275` at n=11).

The pigeonhole runs on witnesses versus runners. `v33` replaced the "9 slots / 8 runners"
count with the complementary-pair algebra: *pairs own labels `{2..9} = I₁..I₈`, `I₉`
unclaimed.*

## 2. The axiom that fails at n=8  `[PROVED — a count, not an opinion]`

The triple's step 1 is a **counting identity between witnesses and speeds.** That count is
tight at a prime and broken at `n = 8`:

| | AP witnesses `r/n`, `gcd(r,n)=1` | speeds | ratio |
|---|---|---|---|
| `n = 11` | `φ(11) = 10` | `10` | **1.00 — exactly tight** |
| `n = 8` | `φ(8) = 4` | `7` | **1.75 — overloaded** |

At prime `n` every witness can be assigned to a speed. At `n = 8` there are only four
unit witnesses `1/8, 3/8, 5/8, 7/8`, forming **two** complementary pairs `{1,7}` and
`{3,5}`, against seven speeds. **The complementary-pair pigeonhole cannot run on the unit
witnesses at `n = 8`** — not because the argument is wrong, but because the witness set is
too small by a factor of `1.75`.

*(Numerical aside, not a claim of identity: `1.75` is also the covering slack
`f(8,163)/⌈163/41⌉ = 7/4`. The two ratios are `(n−1)/φ(n)` and `2(n−1)/n`, which coincide
at `n = 8` only because `φ(8) = 8/2`. Different quantities; do not merge them.)*

## 3. The repair our own machinery supplies: the `q`-witness ladder

At composite `n` the witnesses are not just the units. Today's `RIGID_CLASS_v2` Lemmas A
and B, restated as an LRC reduction:

**Theorem (witness ladder).** *Let `T` be `n−1` positive integers and `q ∈ {2,…,n}` with
`gcd(a,q) = 1`. If `q` divides no element of `T`, then for every `v ∈ T`*

    ‖v·(a/q)‖ = |va mod q| / q ≥ 1/q ≥ 1/n,

*so `a/q` is a lonely time and LRC(`n`) holds for `T`. For `q < n` the inequality is strict,
so `a/q` sits in a lonely interval. Hence a counterexample to LRC(`n`) must have, for every
`q ∈ {2,…,n}`, some speed divisible by `q`.* `[PROVED]`

`gcd(a,q)=1` and `q ∤ v` give `va ≢ 0 (mod q)`, which is the whole proof.

**This is exactly Rosenfeld's Lemma 4** (`lcm(2,…,k+1) ∣ ∏vᵢ` for any non-LR set) — his
lemma is the divisibility shadow of our witness ladder. Arriving at it independently from
our own machinery is the anchor that the translation is on the right object.

**And it restores the count.** Witnesses available at level `q` number `φ(q)`:

    Σ_{q=2}^{8} φ(q) = 1+2+2+4+2+6+4 = 21   witnesses against 7 speeds.

So the room the prime case gets from `φ(n) = n−1` is recovered at `n = 8` from the
**ladder of divisors**, not from the units.

**Verified.** Over 3 124 random 7-tuples having at least one uncovered level, the witness
`a/q` was lonely in every case (0 failures) and `L(T,8)` was non-empty in every case. Both
known obstruction tuples cover the whole ladder, as they must:
`T₆ = {1,6,7,8,9,15}` and `T₇ = {1,4,12,13,14,16,20}` leave **no** level uncovered.

## 4. What translates, and what has to be built

| n=11 component | status at n=8 |
|---|---|
| Complementary Pairs (each runner blocks a `±` pair of unit witnesses) | **fails as stated** — 4 witnesses, 7 speeds. Replaced by the ladder: speed `v` kills level `q` iff `q ∣ v`. |
| Coupling Principle (bad intervals move together under the free parameter) | **not translated.** At n=11 the free parameter is a real speed `a₂`; at n=8 with integer speeds there is no continuous parameter. `lrc_v11_9_srh_n11_template` records the same problem for SR-H and its fix — the free parameter became `c ∈ {1,…,n−1}`. The n=8 analogue is unidentified. **This is the gap.** |
| Baton-Pass Certificate (explicit `t*`) | **not translated.** Needs the coupling analogue first. |

The blocking relation also changes character: at n=11 a runner blocks a `±` **pair**; on
the ladder a speed `v` kills **every** level `q ≤ n` dividing it — so one speed can kill
several levels (`16` kills `q = 2,4,8`), and the structure is a covering problem on the
divisor lattice rather than a matching on pairs.

## 5. Where this points

Killing all seven levels `{2,…,8}` takes only **four** speeds — e.g. `{8, 6, 5, 7}` covers
`2,4,8 / 2,3,6 / 5 / 7`. A counterexample has seven speeds, so **at most four are pinned by
the ladder and at least three are free.** The ladder is therefore a genuine constraint but
not a decisive one on its own, and the next object is what the free speeds must do — which
is the same shape as the sector decomposition (`x = #{v : 8 ∣ v}`) reached from the
Rosenfeld side, and the two should be checked against each other before either is pushed.

## 6. Ledger

Nothing here decides a cell or proves `n = 8`. What it establishes: the n=11 counting step
**provably** cannot run at `n = 8` on the unit witnesses; the ladder restores the witness
budget and independently re-derives Rosenfeld's Lemma 4; and the **Coupling Principle is
the untranslated component**, which is the thing to attack next. Decided cells **2 of 135**.
