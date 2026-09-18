# Does the BS frame help with witnesses?

**Yes, measurably — and it is the first thing in this line that pays.** But the bound I first
thought I saw is not there.

---

## 1. Why the question is the right one

BS's Lemma 2 is a pigeonhole: it certifies that a search over the multiplier group `U(ℤ_N)`
*succeeds* without running it. So it is a witness-production method, not only an existence proof.
That makes it directly comparable to the cascade, which is also a witness generator.

Common currency: both produce a rational instant, so compare the **denominator**.

```
  CASCADE    t = (8k+1)/(8d)        for some disparity d
  MULTIPLIER t = λ/(8M)             the BS form; minimal M is the witness complexity
```

---

## 2. Multiplier witnesses are an order of magnitude simpler

3200 subjects, speeds drawn from `1..89` (`witness_complexity_v1.py`):

```
                                   min   median    p90    max
  cascade witness denominator        8      104     448    696
  multiplier witness denom (8M)      8       16      32     56
  minimal M                          1        2       4      7
  cascade depth (moves)              0        0       3      8

  multiplier denominator STRICTLY LOWER than cascade's : 2881/3200  (0.9003)
  equal                                                :  319/3200  (0.0997)
  higher                                               :    0
```

**Never higher, lower in 90%, median 6.5× smaller.** `[EMPIRICAL]` on this sampler. This is a real
advantage of the multiplier frame over the cascade *for the specific job of exhibiting a witness*,
and it does not depend on the firewall question — it is a comparison of two instant-producing
procedures, with no covering argument involved.

---

## 3. The bound I thought I saw is not there

`M ≤ 7` across 3200 random subjects invited a bound. Tested rather than reported:

```
  hard arrangements on file        : max M = 5   (incl. (27,70,…,393), (1,31,…,225))
  speeds 1..20 … 1..5000           : max M = 4, 5, 7, 7, 8, 7   — no growth with range
  adversarial hill-climb (weak)    : M = 13   at [33,65,83,89,97,133,149,153]
  adversarial hill-climb (harder)  : M = 20   at [5,213,229,245,261,285,293,413]
```

The harder search was still climbing — per-restart bests spread across 7…20 with no plateau. **No
bound on `M` is established, and the `≤ 7` impression was an artifact of random sampling.**
`[EMPIRICAL — conditional negative]`: this says my searches found no bound, not that none exists.

The obvious driver is also dead. Hypothesis: `M` is large when the witness set is thin, i.e. when
`margin = max_t min_d ‖d·t‖` barely exceeds `1/8`. Measured, mean margin by `M`:

```
  M      1        2        3        4        5        6        7
  mean 0.3016   0.2916   0.2964   0.2960   0.2916   0.3557   0.2897
```

Flat. And the counter-datum was already in hand before the measurement: the AP `(1,…,8)` has margin
exactly `0.125` — the thinnest possible, tight at the threshold — and `M = 1`.

---

## 4. What this does and does not give

**Does.** A measured, firewall-independent advantage: for producing a witness, the multiplier frame
beats the cascade on complexity in 90% of cases and never loses. If the goal is a *certificate* for
a given arrangement, search `λ/(8M)` rather than run the cascade.

**Does not.** `M` is unbounded as far as these searches go, so this is not a bounded finite search
and not a route to Existence. It also does not improve the cascade — the two are different
procedures, and nothing here transfers a bound from one to the other. And a lower-complexity
witness for each arrangement separately says nothing about a uniform construction.

```bash
python3 experiments/n8/witness_complexity_v1.py   # the comparison
python3 experiments/n8/witness_complexity_v2.py   # hard cases, ranges, first hill-climb
python3 experiments/n8/witness_complexity_v3.py   # harder climb (M=20), margin correlation
```
