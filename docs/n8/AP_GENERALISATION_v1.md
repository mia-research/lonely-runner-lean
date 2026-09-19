# Does the AP's coincidence generalise? Two refutations, and what actually does

Applying the two-patterns mechanism to the open cases. **Two candidate generalisations are refuted**,
and the one that survives turns out to be a theorem we already had.

## What the AP has that a general profile might not

At the AP, each of the four isolation events is **doubly special**: `x = u` sits on the `+1` pattern
through reading `u` and on the `−1` pattern through reading `8 − u`, simultaneously
(`TwoPatterns.unit_on_both`). Two natural generalisations suggest themselves. Both fail.

## Refuted 1 — a doubly-tight witness

*Claim:* every profile has a witness at which **two** constraints are tight.

**False: 321 of 19,880 profiles (1.615%) have none.** Smallest: `m = 60`, `b = [2,5,10,12,30]`, whose
only witnesses are `17` and `43`, each tight at `b = 2` alone.

**Why the natural proof fails, exactly.** The walk argument would iterate: having reached a residue
class mod `b`, walk *within* it until a second constraint goes tight. But `EdgeWitness.tight_of_step`
needs **unit steps** — its whole content is that `(q−1) mod b = q mod b − 1` still lies in `[L,U]`
unless `q mod b = L`. Inside a class mod `b` the step size is `b`, so a constraint can be **leapt
over** rather than landed on. Concretely, stepping `17 → 19` in that profile jumps `b = 10` from
residue `7` straight past the edge `8` to `9`.

**The walk is a unit-step argument and does not iterate.** That is worth knowing before attempting it
again.

## Refuted 2 — one witness on both patterns

*Claim:* every profile has a single witness lying on the `+1` pattern and the `−1` pattern.

**False: 595 of 19,880 (2.993%)**, and 321 (1.615%) even allowing a single modulus with `L = U` to
count as both. Smallest: `m = 84`, `b = [4,12,14,21,28]`.

## What does generalise — and it is already proved

> **Each pattern supplies a witness — but in general they are two different points.**

Verified: 0 of 19,880 profiles lack a `+1`-pattern witness, and 0 lack a `−1`-pattern witness. This
is exactly **`EdgeWitness.edge_witness_both`**, proved and axiom-clean: walking down lands on a lower
edge, walking up lands on an upper edge.

**So the AP is the degenerate case where the two witnesses merge into one point.** That merging
happens in **97.01%** of profiles — common, and not a theorem. The AP's specialness is real: its
coincidence is forced by `u² ≡ 1 (mod 8)`, which has no analogue for a general profile.

## The shape of the answer

| | AP | general profile |
|---|---|---|
| `+1` pattern supplies a witness | yes | **yes — proved** |
| `−1` pattern supplies a witness | yes | **yes — proved** |
| the two coincide at one point | **yes, forced by `u² ≡ 1`** | 97.01%, **not** a theorem |
| two constraints tight at that point | yes | 98.4%, **not** a theorem |

The two lower rows are where the AP is genuinely exceptional. Any argument that assumes a general
profile inherits them is assuming something false about 1.6–3.0% of cases — which is precisely the
band where every attempt in this project has failed.

## Status

Nothing new is proved here; two routes are closed with reasons, and the correct generalisation is
identified as an existing theorem. Existence at order 8 is unchanged.
