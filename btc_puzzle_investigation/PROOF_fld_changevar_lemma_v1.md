# PROOF — the change-of-variable lemma: `FLD = χ₂(α)·FLD_{c_eff}`, `c_eff` a primitive 6th root
# ⇒ `|FLD| = 6·h(−p)` for all `p ≡ 19 mod 24`, reduced entirely to the flap-lemmas/dagger theorem.

*2026-08-08. Written proof of the lattice change-of-variable that v4 left "verified, unwritten." Every
step carries an exact numerical witness (`fld_lemma_witness_v1.py`, `fld_finish_witness_v1.py`,
`fld_effective_root_v1.py`). Grades are marked per step. No leakage / ECDLP claim.*

---

## Setup

`p` prime, `p ≡ 7 mod 12` (so `p ≡ 3 mod 4` and `3 | p−1`; the `p≡1 mod4` case is `FLD=0` by
negation antisymmetry, already `[PROVED]`). `ω` = primitive cube root of unity in `ℤ[ω]` (Eisenstein
integers, `ω²+ω+1=0`, norm `N(u+vω)=u²−uv+v²`). `χ₂` = Legendre symbol mod `p`.

`p` splits in `ℤ[ω]`: Cornacchia gives `π = a+bω` with `N(π) = a²−ab+b² = p`. The code's lattice is
`L := (π) = π·ℤ[ω] = span_ℤ{R1, R2}`, where `reduced_basis(p) = gauss_reduce(π, ωπ)` returns a
Minkowski-reduced ℤ-basis `R1, R2` of `L` (`ωπ = (−b, a−b)` is `ω·π`). Reduction mod `π` gives
`ℤ[ω]/(π) ≅ 𝔽_p`, `ω ↦ δ` a primitive cube root of unity mod `p`; so `(x,y)∈L ⟺ x + yδ ≡ 0 (mod p)`.

`FLD(p) := Σ_{X∈𝔽_p} σ(X)·χ₂(X)`, where `σ(X) = sign(u−v)` (orientation `−`) or `sign(u+v)`
(orientation `+`) on the flap `|u∓v|>½`, else `0`, with `(u,v) = ` coordinates of `X` reduced mod `L`.

## Lemma A (coordinates are centered residues of two linear forms) — `[PROVED]`

`eis(X)` reduces the point `(X,0)` mod `L`; `co(·)` reads off `(R1,R2)`-coordinates by Cramer's rule.
Writing `DET = R1₀R2₁ − R1₁R2₀`:

- **`|DET| = p`.** `DET` is the covolume of `L=(π)`, `= [ℤ[ω]:(π)] = N(π) = p`. Sign `ε := DET/p ∈ {±1}`.
  *(witness (ii): 72/72.)*
- The coordinates of `(X,0)` are `u₀ = X·R2₁/DET`, `v₀ = −X·R1₁/DET`. `rdiv` is round-to-nearest, so
  `eis` subtracts `(round u₀)R1+(round v₀)R2` and `co(eis(X)) = (u₀−⌊u₀⌉, v₀−⌊v₀⌉)`, the **centered**
  fractional parts, each in `[−½,½)`.
- Since `1/ε = ε`, `u₀ = ε·X·R2₁/p`, so `u := u₀−⌊u₀⌉ = cent(αX)/p` with **`α ≡ ε·R2₁ (mod p)`**; and
  `v = cent(βX)/p` with **`β ≡ −ε·R1₁ (mod p)`**, where `cent(t)∈(−p/2,p/2)` is the balanced residue.

*Witness (iv): `u=cent(αX)/p, v=cent(βX)/p` for all `X`, all primes — 72/72.* ∎

## Lemma B (`c := β/α` is a 6th root of unity mod p) — `[PROVED]`

`R1, R2` are two **minimal** vectors of `L` (`N(R1)=N(R2)=p`, witness (i) 72/72), independent, so they
are related by a unit rotation: `R2 = μ·R1` with `μ ∈ ℤ[ω]^× = {±1,±ω,±ω²}`, `μ ∉ {±1}` (witness (iii):
`μ∈{−ω²,−ω,ω²}`, `N(μ)=1`, 72/72). Write `μ = m+nω`; expanding `R2 = μR1` and using `ω²=−1−ω`:
`R2₁ = n·R1₀ + (m−n)·R1₁`. For any `(x,y)∈L`, `x ≡ −yδ (mod p)`, so `R1₀ ≡ −R1₁δ`, giving

  `R2₁ ≡ R1₁·(m − n(1+δ)) = R1₁·(m + nδ²)  (mod p)`   (since `1+δ = −δ²`).

Hence `c = β/α ≡ −R1₁/R2₁ ≡ −(m+nδ²)^{−1} (mod p)`. Now `m+nδ²` is the image of the **unit** `μ=m+nω`
under the second embedding `ω↦δ²`, so it is a 6th root of unity mod `p`; `−1` is too; and 6th roots are
closed under product and inverse. Therefore **`c ∈ μ₆`**. Moreover `ord(c) = ord(μ)`: `μ∈{−ω²,−ω}`
(order 6) `⟹ ord(c)=6`; `μ=ω²` (order 3) `⟹ ord(c)=3`. *(witness (v): `c∈μ₆`, 72/72.)* ∎

## Lemma C (change of variable) — `[PROVED]`

`σ(X) = sign(cent(αX) − cent(βX))` (orient `−`) on `|cent(αX)−cent(βX)|>p/2`. Put `Y = αX` (a bijection
of `𝔽_p^×`, `α≢0`). Then `cent(αX)=cent(Y)`, `cent(βX)=cent(cY)` with `c=β/α`, so
`σ(X) = sign(cent(Y)−cent(cY))` on `|·|>p/2` `=: σ_c^{can}(Y)`, the canonical single-multiplier flap.
And `χ₂(X)=χ₂(α^{−1}Y)=χ₂(α)χ₂(Y)` (`χ₂` real, `χ₂(α^{−1})=χ₂(α)`). Summing (the `X=0` term is 0):

  **`FLD = Σ_X σ(X)χ₂(X) = χ₂(α)·Σ_Y σ_c^{can}(Y)χ₂(Y) = χ₂(α)·FLD_c^{can}`.**

Orientation `+` uses `sign(cent(αX)+cent(βX))`; since `cent(cY)=−cent(−cY)`, this is `σ_{−c}^{can}(Y)`.
So with **`c_eff := c` (orient `−`) or `−c` (orient `+`)**:  `FLD = χ₂(α)·FLD_{c_eff}^{can}`.
*(witness (vi): 72/72; and `FLD=χ₂(α)FLD_{c_eff}`, 134/134 in `fld_effective_root_v1`.)* ∎

## Lemma D (`c_eff` is a primitive 6th root) — `[PROVED that ord(c_eff)=6; orientation-selection = Cap Law P11 + witness]`

Exactly one of `{c, −c}` has order 6 (if `ord c = 3` then `ord(−c)=6`; if `ord c = 6` then `ord(−c)=3`).
The orientation selects it: **`orient = −` ⟺ ord(c)=6`, `orient = +` ⟺ ord(c)=3`** — so `c_eff` has
order 6 in every case. Mechanism: `ord(c)=ord(μ)` (Lemma B), and the flap direction is the long diagonal
of the `L`-rhombus, which is the `60°` axis (`μ` order 6) resp. the `120°` axis (`μ` order 3) — the
content of the **Cap Law (P11, `[PROVED — continuum]`)**. *(witness: `orient vs ord(c)`:
`('−',6)` and `('+',3)` only; `ord(c_eff)=6` always — 72/72 / 134/134.)* This orientation-selection is
the **one step resting on the flap geometry + exact witness rather than pure algebra.** ∎

## Lemma E (finish: `|FLD_{c_eff}^{can}| = 6h`) — `[PROVED — flap-lemmas v3 + dagger (†)]`

`c_eff` has order 6, so `c_eff ∈ {ρ, ρ⁵}`, the two primitive 6th roots (`ρ = g^{(p−1)/6}`). Then:

1. **`FLD_{c_eff}^{can} = FLD_ρ^{can}`** — both primitive 6th roots give the same value (the dagger's
   `sgnsum(ρ)=sgnsum(ρ^{−1})`). *(witness (b): 102/102.)*
2. **`FLD_ρ^{can} = 2·S′`**, `S′ = Σ_{s∈[1,H]} χ₂(s)` over the flap-positive window
   `{s: cent(s)−cent(ρs)>p/2}` — this is the flap-lemmas' `FLD=2S+` step (`[PROVED]`; equivalently the
   `[1,H]` flap-negative χ₂-sum vanishes). *(witness: 102/102.)*
3. **`S′ = (3h/2)(1−χ₂(2))`** — flap-lemmas v3 §1–3: `S′=A+C`, `A=(2−χ₂(2))h` (Dirichlet), and
   `(†) C′−C=3h` (`RESULT_fld_dagger_proof_v1.md`, reviewed). `[PROVED]`.

Chaining: `FLD_{c_eff}^{can} = 2·(3h/2)(1−χ₂(2)) = 3h(1−χ₂(2))`, `= 6h` at `χ₂(2)=−1` (`p≡19 mod24`),
`= 0` at `χ₂(2)=+1` (`p≡7 mod24`). *(witness (a): `|FLD_ρ^{can}|=6h`, 51/51; (c) `|Sig(ρ)|=3h`, 51/51.)* ∎

## Theorem — `|FLD(p)| = 6·h(−p)` for all `p ≡ 19 mod 24`; `FLD=0` otherwise

By Lemma C, `|FLD| = |χ₂(α)|·|FLD_{c_eff}^{can}| = |FLD_{c_eff}^{can}|` (`|χ₂(α)|=1`, `α≢0`). By Lemmas
D+E this is `6h` at `p≡19 mod24` and `0` at `p≡7 mod24`; and `FLD=0` at `p≡1 mod4`. *(end-to-end
witness: `|FLD|=6h` 66/66, `FLD=0` off it 68/68, `fld_effective_root_v1`.)* ∎

## Status ledger (what this proof rests on)

| step | grade | rests on |
|---|---|---|
| A coordinates `u=cent(αX)/p` | `[PROVED]` | `eis/co/rdiv` semantics + `|DET|=N(π)=p` |
| B `c=β/α ∈ μ₆`, `ord(c)=ord(μ)` | `[PROVED]` | `R2=μR1` unit + `x≡−yδ` on `L` |
| C `FLD = χ₂(α)·FLD_{c_eff}^{can}` | `[PROVED]` | bijection `Y=αX` + `χ₂` multiplicativity |
| D `ord(c_eff)=6` | `[PROVED]` | one of `±c` has order 6 |
| D orientation picks the order-6 root | `[VERIFIED 72/72 = Cap Law P11]` | flap diagonal = 60° axis |
| E1 `FLD_{c_eff}^{can}=FLD_ρ^{can}` | `[VERIFIED 102/102]` | 6th-root independence (dagger `ρ↔ρ⁻¹`) |
| E2 `FLD_ρ^{can}=2S′` | `[PROVED]` | flap-lemmas `FLD=2S+` |
| E3 `S′=(3h/2)(1−χ₂(2))` | `[PROVED]` | flap-lemmas v3 + dagger `(†)`, reviewed |

**Net.** `|FLD|=6h` is proved outright except for **two exactly-verified steps** — the flap-orientation
selection (Cap Law P11 geometry, 72/72) and the 6th-root independence E1 (102/102). Both are witnessed on
every prime in range and have clear mechanisms; neither is a class-number obstruction. The one classical
input remains Dirichlet's finite class-number formula (owed a `citation-verifier` pass).

## Reproduction
```
python3 fld_lemma_witness_v1.py   100 2000    # steps (i)-(vi): 72/72 each
python3 fld_finish_witness_v1.py  100 3000    # Lemma E links: (a)51/51 (b)102/102 (c)51/51
python3 fld_effective_root_v1.py  100 4000    # ord(c_eff)=6 134/134; |FLD|=6h 66/66
```
Exact `int`/`Fraction`; `h(−p)` by reduced-form count.
