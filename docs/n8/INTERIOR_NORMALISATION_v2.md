# Interior witness normalisation — now proved

Supersedes `INTERIOR_NORMALISATION_v1.md`, which recorded the result as `[VERIFIED]` over ~242,000
profiles. **It is now `[PROVED]`**, Lean, axiom-clean — and the measurement is what showed where to
look.

## The measurement pointed at a walk, not a count

Two figures from v1 were doing more work than they appeared to:

- the position of `q mod b` inside `I(b)` is **U-shaped and symmetric** (17.63% / 17.98% in the
  outer deciles) — witnesses hug the **edges**;
- the number of supplying `(modulus, end)` pairs is **never fewer than two**, with `L` and `U`
  splitting `49.8 / 50.2`.

A count cannot produce "never fewer than two, one of each kind". A **walk** can: step down and you
land on a lower edge, step up and you land on an upper edge. That is what the distribution was
saying.

## The proof

Let `Sat q` mean `q` satisfies every constraint `L ≤ q mod b ≤ U`.

**`EdgeWitness.tight_of_step`** — if `Sat q` and `¬ Sat (q−1)`, then some constraint has
`q mod b = L` exactly. *Why:* the failing constraint separates `q` from `q−1`. If `q mod b > L` then
`(q−1) mod b = q mod b − 1` still lies in `[L,U]`, so nothing separates them. Hence `q mod b = L`.

**`EdgeWitness.edge_witness`** — if `Sat` holds at some `q` and fails at some `q₀ ≤ q`, then a
satisfying point exists with one constraint exactly at its lower edge. *Why:* take the least `k` with
`Sat (q₀+k)`. It exists (`Sat q`), and `k ≠ 0` (`¬ Sat q₀`), so `Sat (q₀+k)` and `¬ Sat (q₀+k−1)` —
apply the step lemma. **The walk must stop, because `Sat` fails below.**

**`EdgeWitness.tight_of_step_up`** and **`edge_witness_both`** — the mirror. Stepping up lands on the
upper edge, so when `Sat` fails both below and above there is a lower-edge witness **and** an
upper-edge witness. **That is the proof of "never fewer than two", which was only a measurement.**

All four axiom-clean: `[propext, Classical.choice, Quot.sound]`, zero `sorry`. Witness deposited in
`experiments/n8/v12_new_axioms_v1.out` (43 declarations).

Hypotheses are mild and hold in our setting: lower bounds non-negative (`L(b) = ⌈(b−1)/8⌉ ≥ 0`) and
upper bounds below the modulus (`U(b) = ⌊(7b−1)/8⌋ < b`).

## What is now proved, and what is not

**Proved:** if a witness exists at all, one exists at which some constraint is **tight** — and in
fact two, one at each end. The search space for the open cases is `12` residue classes (6 moduli × 2
ends), not `ℤ/m`, and that is a theorem rather than an observation.

**Not proved:** that a witness exists. This is a *normalisation*, exactly like
`ReachRule.witness_normalised` — it says where to look, not that there is something to find. No
frontier is closed by it.

## Why this one works where the others did not

The three refuted families all tried to produce a witness from nothing:

- counting — foreclosed, the joint density sits below the product of conditionals;
- extremal candidates — exhausted at 38.83%, gated by `8 ∣ m` or `8 ∣ b`;
- bounded centre offset — the offset grows with `m`.

This argument produces a witness **from another witness**, by moving it until a constraint becomes
tight. It is conditional by construction, which is why it can be proved at all — and it is the first
tool here that locates an **interior** object, which is what the remaining cases admit.
