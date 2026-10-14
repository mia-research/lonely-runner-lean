# `Σα < 1`: a sharp criterion whose equality case is exactly the three tight instances

2026-09-11. Script `experiments/n8/ok_sigma_alpha_v1.py`. Exact `Fraction`, no float on any
decision path.

---

## 1. The criterion  `[PROVED]`

For `H ⊆ E` and `O = E \ H`, with `α_x = |A_x ∩ G(H)| / |G(H)|`:

    |G(E)|  ≥  |G(H)| · (1 − Σ_{x∈O} α_x),

> **`Σ_{x∈O} α_x < 1` ⟹ a witness exists.**

`|O| = 1` is **excluded**: there `α_x < 1` merely restates `|G| > 0` and is circular. For
`|O| ≥ 2` the converse fails in principle (overlaps can save a tuple whose `α`s sum above 1),
so the implication is one-way.

## 2. The equality case is exact  `[PROVED — the control]`

The three tight instances have `|G| = 0`, so a sound criterion **must** fail on them. It
does, and not marginally:

| | `\|G\|` | `min_O Σα` over all 91 subsets |
|---|---|---|
| `T₁ = {1,…,7}` | `0` | **exactly `1`** |
| `T₂ = {1,2,3,4,5,7,12}` | `0` | **exactly `1`** |
| `T₃ = {1,4,5,6,7,11,13}` | `0` | **exactly `1`** |

Not `0.999`, not `1.001` — **`1`**. The criterion's boundary is precisely the zero set of
`|G|`. (Consistent with `ALPHA_v1` §3: at a tight instance `|G| = |G_H|(1 − Σα)` holds with
equality because the concentrations are disjoint.)

## 3. On Case 2 it fires, with the extremum tightest  `[EMPIRICAL — two boxes]`

| box | tuples | fires | tightest `min_O Σα` |
|---|---|---|---|
| `[1..18]` | 407 | **407 (100%)** | `973/1066 = 0.9128` at `E*` |
| `[1..22]` | 251 | **251 (100%)** | `0.7765` |

`E*` remains the extreme case, via `O = {7, 13}` — the same pair that carries the
`248/1599` factor — with margin `93/1066`.

## 4. Honest limitation: this may be a reformulation, not a reduction

Tested on **570 non-tight Case-1 tuples** (`|G| > 0`, no multiple of 8), looking for one
where the criterion fails: **none found.** So `min_O Σα < 1 ⟺ |G| > 0` is **not ruled out**.
If they are equivalent, proving the criterion *is* proving LRC(8) — no easier — and it must
not be presented as a reduction in difficulty. What it is, is a **reformulation with a sharp
equality case**, which is the shape a provable inequality usually has.

## 5. What the reformulation buys: an explicit inequality

By `ALPHA_CLOSED_FORM_v1` §1, `α_x = 1/4 + S_x/(x·|G_H|)` with
`S_x = Σ_i[ψ({x v_i}) − ψ({x u_i})]`. So for `|O| = 2` the criterion is exactly

> **`S_x/x + S_y/y < |G_H| / 2`.**

No measures of good sets on the left — only the sawtooth sums, which are **periodic mod
`8·lcm(H)`**, **mean zero** (`∫ψ = 3/512 + 0 − 3/512 = 0`), and bounded by `3N/16`. The
target becomes: *for every Case-2 tuple there is a pair `{x,y}` whose sawtooth sums are
jointly below `|G_H|/2`.* Since `S` is mean zero, roughly half of all speeds have `S_x < 0`;
the content is that some **pair** always works.

## 6. Ledger

`[PROVED]` §1 the criterion and the exclusion of `|O| = 1`; §5 the closed-form restatement
and the mean-zero property of `ψ`.
`[PROVED — exact]` §2: `min_O Σα = 1` exactly on all three tight instances.
`[EMPIRICAL — two boxes]` §3: 407/407 and 251/251, tightest `973/1066`.
`[NEGATIVE — no loss found]` §4: 0 failures in 570 non-tight Case-1 tuples, so equivalence
to `|G| > 0` stands unrefuted; the criterion is **not** demonstrated to be a reduction.

`n = 8` is **not proved.**
