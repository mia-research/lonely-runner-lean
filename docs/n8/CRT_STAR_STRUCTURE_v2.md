# The CRT star structure of `S_x` — v2, correcting v1's reading of the axiom check

2026-09-11. **v2 supersedes `CRT_STAR_STRUCTURE_v1.md`.** The theorem of v1 §2 and every
measurement in v1 §3–§5 stand unchanged. What changes is (a) an overstated gloss on the
theorem, and (b) the ledger's reading of the result, which was backwards. §6's limitation is
unchanged and still governs. Script `experiments/n8/ok_crt_anova_v1.py`.

---

## 0. The two corrections

**C1 — the gloss was wrong, the theorem was not.** v1 §2(i) glossed the theorem as "the odd
primes never couple to each other", and the commit title dropped even the qualifier. The
theorem says every non-vanishing ANOVA component contains the **2-adic coordinate**; it does
**not** say each component has at most one odd prime. v1's own control refutes the gloss:
`{1,2,4,8,15}` shows the component `{64,3,5}` at 0.3355, with 3 and 5 jointly present. Correct
statement:

> **No component of `S` is indexed by odd primes alone. Every component contains the 2-adic
> coordinate.** Two odd primes co-occur in a component exactly when a single `e ∈ H_eff`
> carries both — the first case being `e = 15`.

v1 §5's corollary (at most one odd prime per component, hence conditional independence) was
stated correctly, because it is restricted to `e = 2^a p^b`. That restriction is load-bearing
and v1 §2(i) dropped it.

**C2 — the axiom check passed, and v1 logged it as a failure.** v1 tested
`number_thermodynamics.md` §5 against "no cross terms at all", found main effects at
0.002–0.60, and recorded `[NEGATIVE — named]`. That is not what the framework claims. Its
§12 states the opposite in advance:

> `F_r(n) → +∞` as `r → p_min(n)⁻`; the pole sits on the smallest prime factor; critical
> exponent 1, for every `n`.

For `n = 8`, `p_min = 2`. A framework that puts its singularity on `p_min` **predicts** that
the 2-adic factor is the one that fails to decouple. §1 says the same from the algebra side:
`exp(G) = 2` exactly when `n | 24`, so `(ℤ/8)^×` is in the ℤ₂-graded class. What the ten runs
measured is:

| observed, 10/10 runs | reading |
|---|---|
| every non-vanishing component contains the 2-part | the critical factor couples — §12's pole |
| no component is indexed by odd primes alone | **CRT additivity holds across the odd sector** |

So §5's additivity **holds over the odd primes, and fails only at `p_min`, where the framework
says it must.** v1 compared against a strawman version of the claim and graded the result
negative. The corrected grade is `[CONFIRMED — in the framework's own stated form]`.

## 1. What is proved, restated

> **Theorem.** With `H_eff ⊆ H` the speeds owning a surviving endpoint of `G(H)`, every
> non-vanishing ANOVA component of `S` over `CRT(ℤ/8·lcm(H))` is indexed by `{2} ∪ P` with
> `P ⊆ primes(e)` for some `e ∈ H_eff`.
>
> (i) No component is indexed by odd primes alone.
> (ii) Interaction order ≤ `1 + max_{e∈H_eff} ω_odd(e)`.
> (iii) `p` is inert whenever `p ∤ e` for every `e ∈ H_eff`.
> (iv) **If every `e ∈ H_eff` is `2^a p^b`**, each component has at most one odd prime, so
> conditional on `q = x mod 2^a` the odd-prime contributions are independent.

Proof, tables, control and the derivation of the `E*` inertness: unchanged from v1 §2–§5.
`15` and `21` are the only integers in `[1..30]` with two odd primes, so all three tight
instances and `E*` satisfy (iv).

## 2. A restatement of the standing `n = 2^k` obstruction  `[VERIFIED — and it is a restatement]`

`number_thermodynamics.md` §5 gives, exactly and not asymptotically,

    F_r(n) = ln( n / Φ_r(n) ) = Σ_{p|n} I(r/p),      I(a) = −ln(1−a).

At `r = 1`, `Φ₁ = φ`, so `F₁(n) = ln(n/φ(n)) = Σ_{p|n} I(1/p)`. Checked exactly over
`n ∈ {2,4,8,16,32,6,9,12,15,24,7}`: identity holds in all 11. And `I(1/p) = −ln(1−1/p)` is
strictly decreasing in `p`, so `max_p I(1/p) = I(1/2) = ln 2`. Therefore

> `2φ(n)/n = 1  ⟺  F₁(n) = ln 2  ⟺  n` has one prime factor and it is the costliest one.

The project's standing obstruction — `2φ(n)/n = 1` iff `n` is a power of 2, the reason the
general-`n` Corollary 11.0 branch stalls at `n = 2^k` — is the statement that **all of the
`r = 1` free energy sits in a single local factor, the maximal one.**

**Grade discipline.** This is a **restatement**, not a lead. Both sides are elementary and the
equivalence is immediate; it buys a vocabulary in which the obstruction and the `p_min` pole
of §12 are the same phenomenon, and it buys no proof step. It is recorded because v1 omitted
it while reaching for a negative, not because it moves anything.

## 3. Unchanged: what this does not buy

v1 §6 stands verbatim and is not softened by C2. At `E*`, `O = E \ H = {7,13}`, so `|O| = 2`
exactly, there is no pair to choose, and the criterion is an assertion about two specific
small `x`. The `1/x` envelope keeps it there. A large-deviation estimate over uniform
`x ∈ ℤ/M` — which is what conditional independence invites — says nothing about `x = 7`.
**The LDP is not the payoff.** What the decomposition buys is that `S_x` is exact finite local
data with no odd-only coupling, which is the shape a case analysis needs.

## 4. Ledger

`[PROVED]` §1, the theorem and (i)–(iv), with the proof of v1 §2.
`[VERIFIED — exact]` the five ANOVA tables and five controls of v1 §3–§4, unchanged; §2's
free-energy identity, 11/11.
`[CORRECTED]` v1 §2(i)'s gloss and the v1 commit title — they dropped the `2^a p^b`
restriction that (iv) requires.
`[CORRECTED — grade reversed]` v1's `[NEGATIVE — named]` on `number_thermodynamics.md` §5.
The framework's §12 predicts the `p_min` coupling in advance; measured against the claim as
actually made, CRT additivity **holds across the odd sector, 10/10 runs**.
`[RESTATEMENT — no leverage]` §2's reading of `2φ(n)/n = 1`.
`[OPEN]` the `{2,5}` component vanishing at `{1,4,5,6,7}`, which §1 permits.

`n = 8` is **not proved**, and nothing here moves any grade.
