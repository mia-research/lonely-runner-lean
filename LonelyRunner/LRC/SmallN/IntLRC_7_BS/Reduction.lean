/-!
# n = 7 (Barajas–Serra) — §4 reduction to `|A| ∈ {4,5}`

Source: `sources_barajas_serra_2008.txt`, lines 237–264.

`m = max ν₇(D)`, `N = 7^(m+1)`. With `gcd(D) = 1` we have `D₇(0), D₇(m) ≠ ∅`.
- If `|D₇(i)| ≤ 3` for all `0 ≤ i < m`: done by Corollary 3.
- Else `|D₇(i)| ≥ 4` for some `i`; Cor 3 reduces to `|D₇(0)| ∈ {4,5}`.
- Replacing `d ↦ −d`, assume `(A)₇ ⊂ {1,2,4}`, `A_s = {d ∈ A : (d)₇ = s}`.
- Key identity (7): `q(λ_k · A_s) = q(A_s) + k·s` for `λ_k = 1 + k·7^m ∈ Λ₀`.

Dispatches to `Case_A4` (|A|=4) and `Case_A5` (|A|=5).

Status: not started. See `docs/n7_bs/ROADMAP.md`.

Planned imports: `IntLRC_7_BS.Defs`, `IntLRC_7_BS.PrimeFiltering`.
-/
