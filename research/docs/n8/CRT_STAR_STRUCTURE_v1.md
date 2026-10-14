# The CRT star structure of `S_x` — the odd primes never couple to each other

2026-09-11. Script `experiments/n8/ok_crt_anova_v1.py`, output `ok_crt_anova_v1.out`.
Exact `Fraction` throughout; ANOVA variances are exact rationals, no float on any decision
path.

Provenance: prompted by `~/Desktop/number_thermodynamics.md` §5, which asserts a free energy
"additive over the CRT factorisation … with no cross terms" (the Euler-product /
no-interaction axiom). This document is the **verification demand** applied to that transfer,
in the sense of `~/.claude/CLAUDE.md` §0: which state space, which constraints, is the
quantity additive. The asserted axiom **fails**. What holds in its place is sharper and is
stated as a theorem in §2.

---

## 1. The object, and why a CRT question is the right one to ask

`SIGMA_ALPHA_v1` §5 reduces the `Σα < 1` criterion at `|O| = 2` to

    S_x /x  +  S_y /y   <   |G_H| / 2 ,       S_x = Σ_i [ψ({x v_i}) − ψ({x u_i})]

over the endpoints `(u_i, v_i)` of `G(H)`. `ENDPOINT_RESONANCE_v1` §1 proves `S` is periodic
with period dividing `M = 8·lcm(H)` and mean zero. So `S : ℤ/M → ℚ` is a mean-zero function
on a finite abelian group, and `ℤ/M ≅ ∏_j ℤ/p_j^{a_j}` by CRT. Whether `S` is **additive over
that product** is exactly decidable by the Hoeffding (ANOVA) decomposition, which splits `S`
orthogonally into components indexed by subsets of the factors, with
`Var(S) = Σ_{T≠∅} Var(S_T)`. "No cross terms" means every `|T| ≥ 2` component vanishes.

## 2. The support theorem  `[PROVED]`

> **Theorem.** Write `H_eff ⊆ H` for the speeds owning at least one endpoint that survives the
> merge into `G(H)`. Every non-vanishing ANOVA component of `S` over `CRT(ℤ/M)` is indexed by
> a set of the form `{2} ∪ P` with `P ⊆ primes(e)` for some `e ∈ H_eff`.
>
> **Consequences.** (i) Every interaction contains the 2-adic coordinate: **the odd primes
> never couple to each other directly.** (ii) The interaction order is at most
> `1 + max_{e ∈ H_eff} ω_odd(e)`. (iii) A prime `p` is **inert** — `S` does not depend on
> `x mod p^a` at all — whenever `p ∤ e` for every `e ∈ H_eff`.

**Proof.** `S = Σ_{e ∈ H_eff} S_e`, where `S_e` collects the endpoint terms owned by `e`.
Each endpoint owned by `e` is `(8k±1)/(8e)`, so `ψ({x·(8k±1)/(8e)})` depends on `x` only
through `x mod 8e`; hence the ANOVA support of `S_e` is contained in
`primes(8e) = {2} ∪ primes(e)`. ANOVA is linear and components of distinct index sets are
orthogonal, so the support of a sum is contained in the union of the supports. ∎

The theorem is an **upper** bound on the support. §3 measures how tight it is.

## 3. Measurement  `[VERIFIED — exact, five grids]`

Share of `Var(S)` by interaction order. `M` factorisation given; `H_eff` from the
endpoint-ownership computation.

| `H` | `M` | `H_eff` | order 1 | order 2 | order ≥ 3 | inert |
|---|---|---|---|---|---|---|
| `{2,6,8,10,14}` (the `E*` grid) | `64·3·5·7` | `{8,10,14}` | 0.249844 | 0.750156 | **0** | `3` |
| `{1,3,4,5,7}` (its base) | `32·3·5·7` | `{4,5,7}` | 0.248656 | 0.751344 | **0** | `3` |
| `{1,2,3,4,5}` | `32·3·5` | `{1,2,3,4,5}` | 0.597974 | 0.402026 | **0** | — |
| `{1,2,3,4,5,7}` | `32·3·5·7` | `{5,7}` | 0.001846 | 0.998154 | **0** | `3` |
| `{1,4,5,6,7}` | `32·3·5·7` | `{4,5,6,7}` | 0.475061 | 0.524939 | **0** | `5` |

The order-2 components are, in the same order: `{64,5}+{64,7}`; `{32,5}+{32,7}`;
`{32,3}+{32,5}`; `{32,5}+{32,7}`; `{32,3}+{32,7}`. **No component omits the 2-adic factor in
any of the five.**

**Two readings, kept apart.**

- **The asserted axiom fails.** Main effects carry `0.25, 0.25, 0.60, 0.002, 0.48` of the
  variance. `S` is *not* a sum of independent local terms, and the naive free-energy transfer
  of `number_thermodynamics.md` §5 does not apply here. Named, with the number.
- **Inertness is derived, in three of four cases.** `ENDPOINT_RESONANCE_v1` §1 recorded
  `8L/period = 3` for the `E*` grid and its base as an unexplained observation. It follows
  from §2(iii): at `H = {2,6,8,10,14}` the speeds `2` and `6` own **no** surviving endpoint
  (their arcs are swallowed by the merge), so `H_eff = {8,10,14}` and `3` divides no member.
  Same at `{1,3,4,5,7}` → `H_eff = {4,5,7}`, and at `{1,2,3,4,5,7}` → `H_eff = {5,7}`.
  The bound is **tight** in those three and in `{1,2,3,4,5}`.
  **Not tight at `{1,4,5,6,7}`**: `5 ∈ H_eff` so `{2,5}` is permitted, and it is nonetheless
  exactly zero. That is an additional cancellation the theorem does not explain. Recorded as
  open, not glossed.

## 4. Control — the vanishing is not an artefact of the test set  `[PROVED — prediction fired]`

All five grids above consist of speeds `e = 2^a p^b` (at most one odd prime), for which §2(ii)
**forces** order ≤ 2. A test set of that shape cannot show order 3, so the `0`s above are
uninformative on their own. Prediction made before running, at component level:
max order `= 1 + max_e ω_odd(e)`, and the components that appear are exactly `{2} ∪ P`,
`P ⊆ primes(e)`.

| `H` | `M` | predicted max order | observed | the order-≥3 components observed |
|---|---|---|---|---|
| `{1,2,4,8,15}` | `64·3·5` | 3 | **3** | `{64,3,5}` = 0.3355 |
| `{1,2,3,5,21}` | `16·3·5·7` | 3 | **3** | `{16,3,7}` = 0.4575 — **and only that one**; order 4 = 0 |
| `{2,4,8,16,15}` | `128·3·5` | 3 | **3** | `{128,3,5}` = 0.1928 |
| `{1,2,4,8,105}` | `64·3·5·7` | 4 | **4** | all three `{64,·,·}` triples, and `{64,3,5,7}` = 0.3938 |
| `{1,2,4,8,9}` | `64·9` | 2 | **2** | none (null control) |

`{1,2,3,5,21}` is the discriminating case: four CRT factors are available, so an order-4 term
*could* appear and does not, and of the four possible order-3 index sets exactly one fires —
`{2,3,7} = {2} ∪ primes(21)` — not `{2,3,5}` and not `{2,5,7}`. The prediction is
component-level, and it hit.

## 5. Where the hard instances sit  `[VERIFIED — exhaustive in box]`

The only integers in `[1..30]` with two or more odd prime factors are **15 and 21**. So every
speed in `[1..14]` is of the form `2^a p^b`, and

- all three tight instances `T₁ = {1,…,7}`, `T₂ = {1,2,3,4,5,7,12}`, `T₃ = {1,4,5,6,7,11,13}`,
- and the Case-2 extremum `E* = (2,6,7,8,10,13,14)`,

lie entirely in the class where §2(ii) forces order ≤ 2. On these tuples the structure is
exactly

    S(x)  =  T(q)  +  Σ_{p odd}  C_p(q, x mod p^{b_p}),      q = x mod 2^a,

a **star**: the 2-adic coordinate is a common field, and **conditional on `q` the odd-prime
contributions are independent**.

## 6. What this does and does not buy — stated before it is asked

**Does not.** The conditional independence of §5 invites a Chernoff/large-deviation bound on
`S_x` for *uniform* `x ∈ ℤ/M`, fibrewise in `q` with a union over at most `2^a` fibres. That
does **not** close the frontier, and the reason is structural, not a matter of constants: at
`E*` we have `O = E \ H = {7, 13}`, so `|O| = 2` exactly and there is **no choice of pair**.
The criterion is an assertion about `S_7` and `S_13` — two specific small `x` — and a
statement about uniform `x` says nothing about them. The `1/x` envelope of
`ENDPOINT_RESONANCE_v1` §3 means the criterion always lives at small `x`, where a
large-deviation estimate has no purchase. **The LDP route is not the payoff and should not be
presented as one.**

**Does.** `S_x` is determined by a bounded set of local coordinates with small exact tables —
one 2-adic table plus one table per odd prime dividing `lcm(H_eff)`, with no odd-odd coupling
and no triple coupling on the hard class. `S_7/7 + S_13/13 < |G_H|/2` becomes a finite
statement in local data, and the same holds tuple-by-tuple across Case 2. That is the shape a
case analysis needs, and it is the first decomposition of `S` that is exact rather than
bounded.

## 7. The next measurement, pre-registered

**Statistic.** For each Case-2 tuple in `[1..18]` with `|O| = 2`, compute the star
decomposition of `S_x` and `S_y` and record, per fibre `q`, the per-prime contributions
`C_p(q, ·)`. **Question:** is the criterion's margin `|G_H|/2 − (S_x/x + S_y/y)` a sum of
per-prime margins that are individually signed, or does it require the cross terms?
**Falsification:** if the margin at `E*` (`93/1066`) cannot be written as a sum of local
contributions each bounded away from the wrong sign, the decomposition explains the structure
but not the inequality, and this line is descriptive only.
**Control:** the three tight instances must produce margin exactly `0` under the same
decomposition — `SIGMA_ALPHA_v1` §2 gives `min_O Σα = 1` exactly there, so a decomposition
that does not reproduce `0` is wrong. **Not yet run.**

## 8. Ledger

`[PROVED]` §2 the support theorem and its three consequences; §5's star form on tuples whose
speeds are all `2^a p^b`.
`[VERIFIED — exact]` §3 the five ANOVA tables; §4 the five control tables, with a
component-level prediction stated before the run and met in all five; §5's fact that `15` and
`21` are the only breakers in `[1..30]`.
`[DERIVED]` the inertness of `3` at the `E*` grid, its base, and `{1,2,3,4,5,7}` — previously
recorded as an unexplained period ratio.
`[OPEN]` the vanishing of the `{2,5}` component at `{1,4,5,6,7}`, which §2 permits.
`[NEGATIVE — named]` the "no cross terms" axiom of `number_thermodynamics.md` §5 does **not**
hold for `S`; main effects carry `0.002`–`0.60` of the variance.

`n = 8` is **not proved**, and nothing here moves any grade.
