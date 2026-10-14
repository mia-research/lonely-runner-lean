# The permutation map for individual isolation

2026-09-12. Scripts `experiments/n8/ok_permutation_map_v1.py`. Exact integer arithmetic.
Per-runner, nothing adjoined. Complements `WHICH_GRIDS_ISOLATE_v1`, which settled the same
question for *global* isolation.

---

## 1. The group that acts  `[PROVED + VERIFIED exact]`

At `t = a/m` the assignment runner → site is `j ↦ v_j·a mod m`, so the permutation is
**multiplication by `a ∈ (ℤ/m)*`** — the dilation action, order `φ(m)`. Runner `i` is lonely
iff that permutation carries its whole difference set `D_i` into the band
`[⌈m/8⌉, m − ⌈m/8⌉]`. Write

> `A(D, m) = { a ∈ (ℤ/m)* : min(da mod m, m − da mod m) ≥ m/8 for every d ∈ D }`.

Since `‖−x‖ = ‖x‖`, `a` and `−a` always agree, so **the action factors through
`(ℤ/m)*/{±1}`, of order `φ(m)/2`**, and `|A|` is always even. Verified: **1590** nonempty
`A` sets, closure under `a ↦ −a` fails in **0**.

## 2. Easy runners: the whole group works  `[PROVED + VERIFIED]`

If some `m ≤ 8` divides no element of `D`, then **every** unit works: `|A| = φ(m)`. Verified
over **6659** `(D, m ≤ 8)` pairs with `m` dividing no difference — `|A| ≠ φ(m)` in **0**.

That is the small-denominator lemma of `TIGHT_INSTANCES_v1` §1 restated as a statement about
the group: for an easy runner the permutation is not a constraint at all, because the whole
orbit lands in the band.

## 3. Residual runners: a single orbit  `[VERIFIED — sampled]`

For a **residual** runner — `D` containing a multiple of every `d ∈ {2,…,8}`, so no small `m`
works — take the first modulus that does work. Over 3000 sampled residual runners from
`[1..60]`:

| orbits working at the first successful `m` | share |
|---|---|
| **1** | **72.97%** |
| 2 | 23.60% |
| 3 | 3.27% |
| 4 | 0.17% |

First successful modulus: `m = 11` (969), `9` (551), `13` (548), `10` (476), `12` (226),
`15` (89), `14` (88), `16` (33).

> **The dichotomy is sharp: for an easy runner *every* permutation works; for a residual
> runner, typically exactly *one* does, up to sign.** There is no gradual middle.

## 4. The count follows independence  `[VERIFIED — sampled]`

`|A| ≈ φ(m)·ρ(m)^{|D|}`, with `ρ(m) = (m − 2⌈m/8⌉ + 1)/m` from `PRIME_BOUND_NULL_v1` §2.
Over 2000 random 7-element `D` per modulus:

| `m` | 9 | 11 | 13 | 15 | 16 | 17 | 24 | 31 |
|---|---|---|---|---|---|---|---|---|
| predicted `φρ⁷` | 0.35 | 1.08 | 1.91 | 1.68 | 1.87 | 1.40 | 1.56 | 5.00 |
| observed mean | 0.33 | 1.00 | 1.82 | 1.71 | 1.80 | 1.23 | 1.44 | 5.03 |

So the expected **orbit** count is `φ(m)·ρ(m)^{|D|}/2`, and a residual runner succeeds where
that first exceeds the knife-edge.

## 5. Worked case — `E*` runner 0  `[VERIFIED — exact]`

`D = (2,6,7,8,10,13,14)`. No `m ≤ 14` works at all. Then:

| `m` | `φ(m)` | `\|A\|` | orbits | working `a` |
|---|---|---|---|---|
| 15 | 8 | 2 | **1** | `{4, 11}` |
| 16 | 8 | 4 | 2 | `{1,3,13,15}` |
| 23 | 22 | 2 | **1** | `{2, 21}` |

One permutation up to sign at `m = 15`, `t = 4/15` — the witness already recorded in
`FRAME_FREE_RESTATEMENT_v1`.

## 6. What this says about the residual

The permutation is a constraint *only* for residual runners, and for them it is nearly a
unique constraint. So the residual difficulty is not "find a good `m`" — the moduli that work
cluster at `9 ≤ m ≤ 13` — it is that **at that `m` the witness is essentially unique**, which
is why the certificate has no slack there and why `K` must occasionally reach 2
(`CERT_K_NO_STATIONARY_v1` §3).

## 7. Ledger

`[PROVED]` §1 the group and the `±` factoring; §2's statement is `TIGHT_INSTANCES_v1` §1
restated.
`[VERIFIED — exact]` §1's closure, 1590 cases, 0 failures; §2's 6659 pairs, 0 exceptions;
§5's table.
`[VERIFIED — sampled]` §3's orbit distribution, 3000 residual runners from `[1..60]`;
§4's counts, 2000 `D` per modulus.
`[SCOPE]` §3 and §4 are sampled from a stated box; §1 and §2 are unconditional.

`n = 8` is **not proved.**
