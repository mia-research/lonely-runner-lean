# RESULT — plays #1 and #4 are REFUTED PRE-DATA by algebra; what survives, and its spec (v1, 2026-07-23)

**Status: DERIVATION + exact verification.** No statistic, no null, no p-value on either posed
hypothesis — because neither is testable as posed. Specs designed context-isolated by
`experiment-designer`, then verified independently here.
**Artifacts:** `PREREG_mu3_orthogonal_projection_v1.md`, `PREREG_amicable_log_bridge_v1.md`.

---

## 1. Play #1 (orthogonal spectral projection onto the μ₃-complement) — **the literal form is a forced zero**

**The proposal:** project `H¹` eigenspaces onto the orthogonal complement of the coherent μ₃-residue
modes and check whether the remaining subspace forces a 50% spectral dilution on `χ₂`.

**Why it cannot fire.** GLV is `φ(x,y) = (βx, y)` with `β³ = 1` — **it fixes the `y`-coordinate
identically**. So `y_{λd} = y_d` exactly, hence `χ₂(y_{λd}) = χ₂(y_d)`, and reindexing `d ↦ λd`:

```
V(a) = Σ_d χ₂(y_{λd}) e_n(aλd) = Σ_d χ₂(y_d) e_n((λa)d) = V(λa)        exactly, all a, all p.
```

And `β` has odd order 3, so `β = (β²)²` is a square ⇒ `χ₂(β) = 1` ⇒ the same holds for `χ₂(x)`.

> **Both χ₂ readouts lie entirely in the μ₃-invariant subspace `I`. Their projection onto `I^⊥` is
> identically zero — every prime, every frequency.** The "dilution factor" such a projection would
> report is an artifact of the automorphism, not a measurement: feature and target share construction.

**Verified exactly** (`p = 211, 907, 2089`): `y_{λd} ≠ y_d` in **0 of n−1** cases; `χ₂(x)` mismatches
**0**; `max|V(λa) − V(a)| ≈ 10⁻¹⁴` (float FFT noise) for both readouts.

**A second, independent payoff — the correct independent-frequency count.** `V(λa) = V(a)` together
with `|V(−a)| = |V(a)|` (from `V(−a) = χ₂(−1)V(a)`) makes `|V|` constant on **μ₆-orbits**. Verified:
exactly **`(n−1)/6` classes, all of size 6**, `Q` constant on each to `10⁻¹⁵` (`n = 967` → 161 classes;
`n = 2143` → 357).

> **`m_eff = (n−1)/6`, not `n−1` and not `n/2`.** Any max- or tail-statistic null that assumes `n/2`
> independent frequencies is **mis-specified** — including the obvious null for the withdrawn N1
> measurement. This is a concrete correction that outlives the refuted play.

**What is registered instead** (`PREREG_mu3_orthogonal_projection_v1.md`): at **fixed** `#R` (fixed
ceiling, fixed `dim H¹`), does μ₃-isotype content control the *extremal* magnitude? The spec builds a
3×2 design — rows `#R = 2, 4, 6`, columns μ₃-invariant vs not — using readouts whose ramification
count is held equal within a row (`χ₂(y)` vs `χ₂((x−x₁)(x−x₂))`, both `#R = 4`), so no comparison
crosses a ceiling. Primary is a **top-16 mean of `Q` over the frozen `(n−1)/6` index set** — an order
statistic of fixed depth, which is why it escapes the §A2.6 disqualification that killed the pooled
4th moment (every sub-tail frequency gets weight exactly zero, rather than being averaged in).

A second arm computes the twisted Frobenius eigenvalues directly, with the `a = 0` case checked
against an independently counted polynomial as a known-value firing control. It also records
**pre-data** that the strict pairing hypothesis is refutable by inspection — an even `L(a,T)` would
force `Σα_i = 0`, i.e. `V(a) = 0`, which is false generically — so "strict pairing is false" may not
later be sold as a finding.

---

## 2. Play #4 (φ(n)-averaging / log-coordinate bridge) — **not decidable as posed**, for three separate reasons

**(a) On prime `n`, the full φ(n)-average is the trivial operator.** `(Z/n)*` acts *transitively* on
`Z/n ∖ {0}`, so `A f(d) = (1/φ(n))Σ_{t∈(Z/n)*} f(td)` is a **constant function**. Only averages over a
proper subgroup are non-degenerate — and in the log coordinate those are exactly the isotypic
projectors onto characters of a fixed order. "The φ(n)-averaging operator" is not a new object.

**(b) The log coordinate cannot appear in a feature path.** `ind_g : (Z/n)* → Z/(n−1)` needs `d`; to get
`d` from a point you need `dlog_G(P)` — and the project's own T1 records that the CM coordinate map
`E(F_p) → Z[ω]/(π_p−1) ≅ F_n` **is** that discrete logarithm. So the bridge, realized as an evaluable
map from points to partner-side objects, **contains the ECDLP in its own construction**. It is legal
only on the measurement side ⇒ no map, no attack shape, no bit.

**(c) `Hom = 0` is a theorem on disk**, so "non-homomorphic transfer" needs a decidable rendering.
`|E(F_p)| = n`, `|Ẽ(F_n)| = p`, `gcd(n,p) = 1` ⇒ every group homomorphism is trivial.

**What is registered instead** (`PREREG_amicable_log_bridge_v1.md`): the smallest decidable
sub-question — is the field-side cubic-residue class `χ₃^{(p)}(y(P))` (built from public coordinates
only) dependent on the partner-curve class `χ₃^{(n)}(d³+7)`, after μ₆-averaging, **beyond what matched
non-amicable curves show**? The trace duality enters decidably: `π_n = π_p − 1` makes the scalar side a
residue ring of the *same* `Z[ω]`, so both sides carry a cubic character valued in `μ₃ ⊂ Z[ω]` — the
one legitimate sense in which the two data are the same kind of object. The μ₆-orbit average **is** the
φ(n)-average over `Aut(E)`, in the log coordinate.

Tautology hazard handled by disjoint construction (`F` reads only `(y mod p)`, `g` only `(d mod n)`, no
shared intermediate), by an exactly double-centred `Z[ω]` statistic, and by an **across-arm** amicable
vs matched-control contrast — because the repo's recorded `r = v − w` failure is one a shuffle control
does *not* expose, while an artifact of the `d ↔ P` bijection appears in both arms and cancels.

**Recorded trap:** the natural variant `χ₃^{(p)}(x(P))` is **forced to zero** whenever `9 ∤ p−1` — so a
future run cannot present a forced zero as a null.

---

## 3. Net

| play | posed form | status |
|---|---|---|
| #1 μ₃-orthogonal projection | project χ₂ onto μ₃-complement | **REFUTED pre-data** — projection ≡ 0 by GLV fixing `y` |
| #1 (surviving) | isotype content at **fixed `#R`**; twisted eigenvalue multiset | **SPECIFIED**, not yet run |
| #4 φ(n)-averaging bridge | transfer map `F_p → F_n` | **NOT DECIDABLE** — (a) trivial operator, (b) contains ECDLP, (c) `Hom = 0` |
| #4 (surviving) | μ₆-averaged cubic pairing, amicable vs matched control | **SPECIFIED**, not yet run |

**Both refutations are algebra, not measurement** — they hold at every prime including `2²⁵⁶`, and no
power or scope caveat attaches. That is the strongest form a negative result takes on this project, and
it is why neither play needed data to settle.

**Carried forward as the reusable correction:** `m_eff = (n−1)/6`.

**No ECDLP content.** Play #4's analysis in fact shows the posed bridge *presupposes* an ECDLP oracle.

*Grade legend: PROVED · DERIVED · VERIFIED (exact) · SPECIFIED (frozen prereg, unrun).*
