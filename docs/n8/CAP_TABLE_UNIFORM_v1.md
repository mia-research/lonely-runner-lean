# The 2-adic cap table is a derivation, uniform in `p` — not a `p = 163` check

2026-09-07. Target: an **analytic** proof of `n = 8`. This file removes one item from the
`p = 163`-specific ledger by proving it for every odd prime `p`.

`project_n8_rosenfeld_2026_09_07` §2 grades the 2-adic cap table and the adjacent/opposite
pair classification **PROVED by exhaustive check over 648 admissible speeds × 163 classes**.
That is a fact about `p = 163`. Below they are derived from the block identity alone, for
every odd prime `p`, in half a page. Nothing about `163` enters.

Script: `experiments/n8/cap_table_uniform_v1.py` — checks the derivation against brute force
at `p ∈ {31,37,43,47,53,59,61,67,71,163}`, all admissible speeds, all classes:
**0 mismatches**, and it reproduces the cap and pair-type rows at every one of those primes.

## 1. Setting

`p` an odd prime, `n = 8`, `N = 8p`, `H = N/2 = 4p`. Speeds `v` with `1 ≤ v ≤ H`, `p ∤ v`.
Targets `j = r + pt`, `r ∈ {1,…,p}`, `t ∈ {0,1,2,3}`. `v` **covers** `j` iff
`jv mod N < p` or `jv mod N > N − p`.

For a class `r` write

    r v mod N = p·q + s,     0 ≤ s < p,   q ∈ {0,…,7}.

## 2. The two lemmas

**Lemma 1 (block identity).** `jv mod N = p·((q + tv) mod 8) + s`.

*Proof.* `jv = rv + p t v`, and `rv ≡ pq + s (mod N)`, so `jv ≡ p(q + tv) + s (mod 8p)`.
Since `0 ≤ s < p`, reducing `q + tv` mod 8 is the whole reduction; no carry crosses into the
`s` block. ∎

**Lemma 2 (covering criterion).** *Target `t` is covered ⟺ `(q + tv) mod 8 = 0`, or
`(q + tv) mod 8 = 7` **and** `s > 0`.*

*Proof.* By Lemma 1 the residue is `pm + s` with `m = (q+tv) mod 8`. Then `pm + s < p ⟺ m = 0`,
and `pm + s > 7p ⟺ m = 7 and s > 0`. ∎

Everything below is Lemma 2 plus the orbit `O_v = { tv mod 8 : t = 0,1,2,3 }`. The target set
`{0,7}` has **two** elements, one even and one odd, and that single observation carries the
whole table.

## 3. The cap table  `[PROVED, all odd p]`

**`8 | v`.** `O_v = {0}`, so `q + tv ≡ q` for every `t`: all four targets share one residue.
Covered set is all four or none. **Cap `{0,4}`, all-or-nothing.**

**`v ≡ 4 (mod 8)`.** `tv mod 8` is `0,4,0,4` for `t = 0,1,2,3`, so `t ↦ q+tv` takes the value
`q` on `{0,2}` and `q+4` on `{1,3}`. At most one of `q, q+4` lies in `{0,7}` (they differ by 4).
Covered set is `{0,2}`, `{1,3}`, or empty — an **opposite** pair. **Cap `{0,2}`.**

**`v ≡ 2 (mod 4)`.** `v mod 8 ∈ {2,6}`, so `t ↦ tv mod 8` hits all four even residues, and
`q + tv` runs over every residue of the parity of `q`. `{0,7}` holds exactly one even and one
odd, so exactly one `t` qualifies — provided the `m=7` branch is not voided by `s = 0`. And
`s = 0` forces `p | rv`, hence `r = p`, hence `q = v mod 8`, which is **even** here; so `q` odd
never coincides with `s = 0`. **Cap exactly `1`.**

**`v` odd.** `v` is a unit mod 8, so `t ↦ tv mod 8` is injective on `{0,1,2,3}` and so is
`t ↦ q+tv`. Hence at most `|{0,7}| = 2` targets are covered. If exactly two, say `q+t₁v ≡ 0`
and `q+t₂v ≡ 7`, then `(t₁−t₂)v ≡ −7 ≡ 1 (mod 8)`, so `t₁ − t₂ ≡ v⁻¹ (mod 8)`, which is **odd**.
An odd difference in `Z/4` is `±1`: the pair is **cyclically adjacent**. **Cap `{0,1,2}`, and a
2-element covered set is always an adjacent pair.**

## 4. Two corollaries the search argument runs on  `[PROVED, all odd p]`

**Corollary 1 (`x ≥ 1` forced).** *The target `j = p` is covered only by a speed with `8 | v`.*
Take `r = p`: then `rv = pv`, so `s = 0` and `q = v mod 8`. Lemma 2's `m = 7` branch is dead,
so `t` is covered iff `v(1+t) ≡ 0 (mod 8)`. For `v` odd this needs `8 | 1+t`, impossible for
`t ≤ 3`; for `v ≡ 2 (4)` and `v ≡ 4 (8)` it needs `1+t ≡ 0 (mod 4)` or `(mod 2)` with the
matching valuation, and `t = 0` — the target `j = p` itself — is covered only when `8 | v`. ∎

**Corollary 2 (adjacent ∪ opposite ≠ all four).** An opposite pair is `{0,2}` or `{1,3}` — both
elements of one parity. An adjacent pair holds one of each parity. So the two always intersect,
and their union has at most 3 elements. *Hence a class completed by two speeds each contributing
2 needs both speeds odd, or both `≡ 4 (mod 8)` — never one of each.* ∎

## 5. What this changes, and what it does not

**Changes.** Three entries of the `n = 8` ledger — the cap table, the pair-type classification,
and the `x ≥ 1` forcing — were **`p = 163` exhaustive verifications** and are now theorems for
every odd prime. In a programme whose object is `27 primes × 5 sectors = 135 cells`, these are
the parts of the sector argument that no longer have to be re-established per prime.

**Does not change.** The sector *decisions* (`x = 5`, `x = 4`) rest on `U_min(x)` and on exact
dilate-coverability, and both remain `p`-specific. This file supplies no bound on `U_min`, and
it decides no cell. `n = 8` is not proved analytically; the count of decided cells is unchanged
at **2 of 135**.
