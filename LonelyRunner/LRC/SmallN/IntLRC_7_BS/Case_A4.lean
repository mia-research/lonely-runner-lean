/-!
# n = 7 (Barajas–Serra) — §5, the case `|A| = 4`

Source: `sources_barajas_serra_2008.txt`, lines 267–363.

`A = {d₁,…,d₄} ⊂ D₇(0)`, `d₅ ∈ D₇(i₀)`. Build `λ ∈ Λ₀`, `λ' ∈ Λ` with
`q(λλ'·A) ∩ {0,6} = ∅`. Three subcases on `|A_s|` (most popular class):
- **Case 1 `|A_s| = 4`** (L287): show `ℓ(λ'·A) ≤ 5` for some `λ' ∈ Λ`.
- **Case 2 `|A_s| = 3`** (L299): `ℓ(λ'·A_s) ≤ 4` argument.
- **Case 3 `|A_s| = 2`** (L319): `ℓ(λ'·A_s) ≤ 2` argument + routine check.

Finite residue chase mod 7 via eqns (7)–(12); strong candidates for
`interval_cases` / `decide` / `omega`.

Status: not started. See `docs/n7_bs/ROADMAP.md`.

Planned imports: `IntLRC_7_BS.Reduction`, `IntLRC_7_BS.Lemmas`.
-/
