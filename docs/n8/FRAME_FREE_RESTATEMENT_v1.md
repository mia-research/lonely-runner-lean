# Frame-free restatement: the grid, the permutation, and why it cannot help the hard runners

2026-09-11. Script `experiments/n8/ok_frame_free_v1.py` (inline). Exact `Fraction`.
Owner's correction, after reading `discovery_03_phi_law.md` and `phi_law_paper_v2.md`
§2.1–3.1: the stationary runner is a convention, and once you have the grid the only freedom
is a permutation from one grid speed to another.

---

## 1. What the φ(n) papers actually say  `[source]`

`phi_law_paper_v2.md` §2.1: `vᵢ = v₀ + (i−1)δ`, `i = 1..n` — **all `n` runners move**, and `v₀`
is free. §3.1 / `discovery_03`: at `t = r/(nδ)`,

    pᵢ(t) = v₀·r/(nδ) + (i−1)r/n  (mod 1).

The `v₀` term is common to every runner: it **rotates the whole configuration** and cancels
from every pairwise gap. So `v₀ = 0` is a convention, `{1,2,3,4}` is as much an AP as
`{0,1,2,3}`, and what survives is `(i−1)r mod n`.

> **The grid is fixed; `r` permutes which runner occupies which site.** The φ(n) isolation
> times are the φ(n) elements of `(ℤ/nℤ)^×` acting on the `n` sites.

## 2. Three exact consequences  `[PROVED — 0 disagreements]`

Let `V = {v_1,…,v_n}` be the speeds (no reference chosen), `a` a unit mod `n`.

> **A. Runner `i` is lonely at `t = a/n` ⟺ `v_i`'s residue mod `n` is unique among the `n`
> runners.**
> Because `‖(v_j−v_i)a/n‖ ≥ 1/n ⟺ (v_j−v_i)a ≢ 0 (mod n) ⟺ v_j ≢ v_i (mod n)`, `a` a unit.
> Checked: **91 528** (config, `a`, runner) triples, 0 disagreements.

> **B. The collision structure is invariant across every grid time.**
> `v_i a ≡ v_j a (mod n) ⟺ v_i ≡ v_j (mod n)` for every unit `a`. The permutation moves all
> the runners but preserves the partition into residue classes.
> Checked: **10 574** (config, `a`) pairs, partition unchanged in all.
> **So a runner that shares its residue is never lonely at *any* grid time.** Permuting
> cannot help it — this is the sharp form of "only the permutation from one grid speed to
> another".

> **C. Case 1 / Case 2 is frame-free: it is exactly "is my residue unique".**
> For reference runner `i` with differences `E = {v_j − v_i}`, "no `e ∈ E` is divisible by
> `n`" ⟺ `v_i`'s residue mod `n` is unique.
> Checked at `n = 8`: **32 000** (config, runner) pairs, 0 disagreements.

## 3. The picture this gives

- **Global isolation** = all `n` residues distinct = a bijection onto `ℤ/n` = every runner
  lonely at the *same* time. That is strictly stronger than LRC asks.
- **LRC** asks only that each runner be lonely at *some* time. The grid times settle, in one
  stroke, **exactly the runners with unique residues** — and settle **none** of the others,
  at any grid time, ever (B).
- With `n` runners and `n` classes, a collision forces an empty class: the vacancy of
  `CROWDING_DICHOTOMY_v1` Claim 2, now with no modulus-8 anywhere in it.

**So the whole difficulty of LRC sits on the colliding runners, and it recurses.** If runner
`i` shares its class `C`, its class-mates have `v_j − v_i = n·w_j`, so at `t = a/n + ε` they
contribute `‖n w_j ε‖ ≥ 1/n`; with `η = nε` that is `‖w_j η‖ ≥ 1/n` — the same problem one
scale down, on `|C| − 1` speeds. The non-class-mates are automatically safe at `ε = 0` and
constrain how far `ε` may move: that coupling is precisely the `L(a) ≤ U(a)` certificate of
`GRID_CERTIFICATE_v1`, now derived rather than posited.

A union bound on the recursed part closes it when `|C| − 1 < n/2`, i.e. classes of size
`≤ 4` at `n = 8`. It is the **coupling to the non-class-mates**, not the recursion, that is
open.

## 4. What this changes, and what it does not

**Changes.** "Case 1 / Case 2" stops being a case split and becomes a property of a runner:
*is my residue unique*. The `8` disappears from the statement of the obstruction. And the
grid's limits become sharp — the φ(n) times are not a partial tool for the hard runners, they
are **exactly useless** for them (B).

**Does not change.** Nothing here is a coverage theorem, and no grade moves. The open item is
the same one: the coupling between the recursed class constraints and the non-class-mates,
i.e. a bound on how far `ε` may travel. `K_STATISTIC_RETRACTION_v1` records that wrap depth is
not the right measure of that.

## 5. Ledger

`[source]` §1, quoted from `phi_law_paper_v2.md` §2.1/3.1 and `discovery_03_phi_law.md`.
`[PROVED — exact]` §2 A, B, C, with 91 528 / 10 574 / 32 000 checks, 0 disagreements each.
`[DERIVED]` §3's recursion and its identification with the `L ≤ U` certificate.
`[CORRECTED]` my earlier framing that the stationary runner is a fixed feature of the problem;
it is a choice, and the choice is what selects a hard instance from an easy configuration.

`n = 8` is **not proved.**
