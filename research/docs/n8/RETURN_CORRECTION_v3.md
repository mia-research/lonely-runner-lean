# Lemma C at order 8, corrected: the cap is crossed, not approached

2026-09-17. Supersedes `RETURN_CORRECTION_v2.md`, which is kept as the record. **v2's central
characterisation is wrong** and is corrected in §1. v1 and v2 were written before
`framework_cases_v1.py` existed; the named cases the manuscript already carried refute them.

Artefacts: `experiments/n8/framework_cases_v1.py` / `.out`; v2's own artefacts unchanged and still valid
for what they measure.

---

## 1. The correction

v2 §0 concluded: *"the cascade terminates lonely at every witness, and the word admits no extension, so
the cap is approached as a terminal value and not crossed."* v2 §2 tabulated *pointwise `R < n−1`:
**true** at order 8, `S ≤ 8`*.

**Both are false.** Two arrangements the manuscript names have `R` well above the cap, and both lie
inside the ratio bound `S ≤ 8` where v2 made its claim:

| case | `S` | `t` | moves | `u` (laps) | `R` |
|---|---|---|---|---|---|
| §6.7 climb, `(27,70,107,137,159,188,344,393)`, subject 393 | 7.469 | `49/1872` | 28 | `2401/1872` | **`2401/234` = 10.26** |
| §6.9 row, `(1,31,75,97,128,160,176,225)`, subject 1 | 7.467 | `11/256` | 23 | `165/128` | **`165/16` = 10.31** |

§6.7 further records the largest found as `≈ 11.96` at `S ≈ 7.44`. So `R < n − 1` is false at order 8
**pointwise**, not merely in the supremum, and the correct table is:

| statement | order 5 | order 8, `S ≤ 8` |
|---|---|---|
| pointwise `R < n − 1` | true | **false** (`R = 10.31` at `S = 7.467`) |
| uniform `sup R < n − 1` | true | **false** |

## 2. Why the word enumeration could not see it  `[the reconciliation]`

The two results are not in conflict; the word space cannot express these cascades.

`order_n_certificate_v1.py` builds words from the alphabet `x ∈ {1, …, NV}` with `NV = n − 2 = 6` — the
**non-nearest** runners only. The nearest runner, reading 1, never appears as a setter. That exclusion is
sound *for the question the certificate asks*: before `R` first reaches the cap the nearest cannot have
set, since its setting gives `R ≥ n + 1`. It is fatal for any statement about what happens **after**.

In both named cases the nearest runner sets — at step 24 and at step 19 respectively — and the cascade
continues past the cap to a lonely instant in the second lap. So:

> `sup R = 7` over the word space is not a fact about cascades. It is the value at which the word
> language runs out of alphabet.

v2 §3's "the word is terminal" is correct about that word and carries no consequence for the cascade;
v2 §5's open question — *"does any realisable word strictly exceed the cap"* — was the wrong question,
and the beam launched to answer it was stopped.

## 3. What survives from v1 and v2

- **§1's word table** — the 14-move word, its prefix values, `max τ = 71/2207`. Correct as computed.
- **The replay and the Lean cross-check** — the word is a real cascade at four configurations. Correct.
  The instrument was later validated against the manuscript's named cases, 4 of 4 exact.
- **Lemma A's closed form** reproducing at rungs 1–6. Correct.
- **The `τ = 0` corner degenerating** (0 steps, lonely at `t = 1/8`). Correct.
- **The conclusion that Lemma C as posed asks for a false statement.** Correct, and now for a stronger
  reason: v2 argued the supremum equals the cap, so no margin exists. In fact the cap is exceeded
  outright. Either way `∏λ_j < n − 1` is not available.

## 4. What replaces it

`EXISTENCE_ARITHMETIC_v1.md`. Existence needs `R < ∞`, not `R < n − 1`; the refutation above touches the
first not at all. The cap was never the target — §1.3: *"there is no window here"*.
