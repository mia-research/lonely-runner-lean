# The n=8 Unit-Complete safe fibre — theorem, and the bridge gap it exposes

2026-09-07. Framework: `lrc_proof_v10_21.md` §5.1. Verified adversarially by an
independent agent; its report is `reports/n8_agent_verify_theorem.md`, scripts in
`experiments/n8/`. Corrections from that review are folded in below and marked.

## 1. Theorem  `[PROVED]`

Setting: `n = 8`, Case 2 (`E_div ≠ ∅`), Unit-Complete, **representative speeds**
(`e = ρ_e` for every `e ∈ E_non`), so `E_non = {1,3,5,7} ∪ {ρ₀}` with `ρ₀ ∈ {2,4,6}`
and `|E_div| = 2`.

> On `x = b/L ∈ [3/5, 5/7)` the floors are `t₁ = 0`, `t₃ ∈ {1,2}`, `t₅ = 3`, `t₇ = 4`,
> the four unit bad sets are `{0,7}`, `{2,5}` or `{2,7}`, `{1,4}`, `{4,5}`, whose union
> is `{0,1,2,4,5,7}`. Residues **3 and 6** are blocked by no unit runner. The single
> non-unit runner blocks within one parity class, so it cannot block both. Hence every
> integer `b` with `3L/5 ≤ b < 5L/7` is a **safe fibre**.

Endpoints are tight and the interval must be half-open: `5·(3/5) = 3` exactly (so `t₅ = 3`
needs the left endpoint closed) and `7·(5/7) = 5` exactly (so `t₇ = 4` needs the right
endpoint open). Integer existence: the window has length `4L/35`, so `L ≥ 9` suffices;
the hypotheses in fact force `840 | L`, and the minimum number of integers in the window
over all admissible `L` is **3**, never 0.

Not vacuous. Certificate: `E = {1,2,3,5,7,8,16}`, `L = 1680`, `N = 13440`, fibre
`b = 1008`, uncovered residue `r = 6`, witness `k = 11088` — all seven runners verified
in `[L, 7L]` — and `x₀(E) = 702`.

A second window `x ∈ [2/7, 2/5)` behaves identically with uncovered pair `{1,4}`.

**Correction to an earlier statement of mine.** I said these were "the only two cells" of
the thirteen. That is wrong at cell granularity: there are **four** mixed-parity cells —
`[2/7,1/3)`, `[1/3,2/5)`, `[3/5,2/3)`, `[2/3,5/7)` — which merge into exactly **two
maximal windows** with constant uncovered sets. The substance stands; the count of cells
did not. Also worth recording, since a careless version of the argument would use it:
`t₆` is *not* constant on either window (it jumps at `x = 2/3`, resp. `1/3`), although
`bad(6,·)` happens to be constant across the jump. Nothing above depends on it.

## 2. The gap this exposes, and it is in the framework, not in §1  `[PROVED]`

The framework's value rests on **safe fibre ⟹ `x₀(E) ≥ 1`**. Writing `k = L·r + b`, the
identity is

    e·k mod N  =  L·( ((e·r) + t_e) mod n )  +  u_e.

For `e ∈ E_non` the obstruction in `r` is exactly `bad(e, t_e, n)` — which is what
safety controls. But for `e ∈ E_div` we have `n | e`, so `e·r ≡ 0 (mod n)` and the
expression **does not involve `r` at all**: a divisible runner constrains `b` alone.
Concretely, for `e = n·m` the condition `e·k mod N ∈ [L,(n−1)L]` reduces to

    m·b mod L  ∈  B_div,

and `B_div = [L/n, (n−1)L/n]` is exactly that condition **for `m = 1` and for no other
member of `E_div`**.

Under the hypotheses of §1, `|E_non| = 5` and `|E| = 7`, so `|E_div| = 2` always: there
is always a proper multiple of 8 whose condition is unencoded. This is generic, not a
corner case.

Measured, exactly: for `E = {1,2,3,5,7,24,40}` with `L = 840`, all **96** integers of the
window are safe but only **6** carry a witness; for `{1,2,3,5,7,8,24}`, 96 safe and 27
usable. Across 828 tuples swept, the usable count never reached zero — **so no
counterexample to the conclusion appeared** — but the implication as stated is not
established, and the gap is one step wide.

**Scope.** When `|E_div| = 1` the bridge is fine, since `B_div` then encodes the only
divisible condition. So the gap bites exactly the representative-speed configuration of
§1, and the actual-speed configuration (twin in `E_non`, `|E_div| = 1`) is unaffected.
The two cases trade off, which is why neither alone settles the leaf.

## 3. What §1 therefore does and does not give

- It gives: an explicit, unconditional window of safe fibres for the Unit-Complete leaf
  at `n = 8`, representative speeds, for all three `ρ₀`. That leaf is one of the two the
  branch inventory (`reports/n8_agent_branch_inventory.md`) found uncovered.
- It does not yet give `x₀(E) ≥ 1` for that leaf, because of §2.
- To close it: exhibit `b` in the window with `m·b mod L ∈ B_div` for the second
  divisible runner `n·m`. `B_div` has density `(n−2)/n = 3/4` and the window holds
  `≈ 4L/35` integers; a density heuristic is not a proof, and the honest statement is
  that this needs the same rate/equidistribution input as the other open step.

## 4. Grades

Parity Lemma (both halves), the floor values and bad sets on the window, endpoint
tightness, integer existence, non-vacuity: **PROVED**, independently re-derived.
The `m ≥ 2` divisible-runner gap in the bridge: **PROVED to exist** (identity above plus
the two measured tuples). Whether every admissible `E` still has a usable fibre in the
window: **OPEN**.
