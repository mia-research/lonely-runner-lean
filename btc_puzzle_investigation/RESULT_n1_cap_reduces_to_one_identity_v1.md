> # ⚠ CORRECTION — this RE-DERIVES an already-proved chain; it is exposition, not new
> **`RESULT_26_PROVED_weil_restriction_v1.md` already PROVES `e₂ = e₁² − χ₂(−1)p` UNIFORMLY** (all `a`,
> all `p>3`) by Galois descent on `E[2]` (a genus-3 quotient whose `E[2]`-translations descend to
> involutions that Frobenius 3-cycles, forcing trace 0). It also already states the chain
> `120° ⇒ e₂=e₁²−χ₂(−1)p ⇒ cap`. So:
> - the identity in §1 is **PROVED (uniform)**, not "verified-exact, open" as graded below;
> - the "reduction of the open gap to one identity" framing is **void** — the identity was not the gap;
> - what survives as possibly-useful is only the **packaging** in §2 (the palindromic `T=√p·W`
>   normalization making `cap ⟺ disc 3(4−ε²)≥0`), and even that duplicates the chain's cap step.
> The one live caveat on the whole chain is **(D2)**: the Weil II purity citation (failed
> citation-verifier ×4) — an item on the genuinely-open list, not addressed here.
> **This is the third time this session I re-derived worked A_new/cap material. Recorded as such.**

# RESULT — the cap + the 120° law (uniform) reduce to ONE explicit power-sum identity: `S₂ = −S₁² + 2χ₂(−1)p` (v1, 2026-07-24)

**Direction #1 executed.** The project's sole remaining structural gap on the `A_new` channel is the
**uniformity** of the 120° law (`α₂/α₁=ζ₃` for all `a,p`; per-cell proved at 22 primes,
`RESULT_n1_120deg_exact_v1.md`), which carries the cap `|V_y(a)|≤2√p`. This result reduces **both** the
uniform 120° law **and** the cap to a **single explicit identity between the `F_p` and `F_{p²}`
traces**, verified exactly, with the cap and the ζ₃-pairing shown to be its corollaries.

**Scripts:** `sage_e2_relation_v1.sage`, `sage_palindrome_v1.sage`, `sage_target_exact_v1.sage`.
No floating point in the identity check (`ℤ[ζ_n]` exact). No ECDLP content.

---

## 1. The reduction

Let `S_k = −Σ_{P∈E(F_{p^k})} χ₂^{(k)}(y_P)·ψ_a(Nm_k P)` be the trace of `Frob^k` on
`H¹_c(E, L_{χ₂(y)}⊗L_{ψ_a})` (`S_1 = −V_y(a)`). The char poly is
`L*(a,T) = T⁴ − e₁T³ + e₂T² − e₃T + e₄`, `e₁=S_1`.

**Forced (purity + duality; project-confirmed, `verify_e3_sign.sage`):** `e₄ = p²`,
`e₃ = χ₂(−1)·p·e₁` — checked here to `1e-20`.

**The one non-forced relation, found this session:**
```
e₂ = e₁² − χ₂(−1)·p        ⟺        S₂ = −S₁² + 2·χ₂(−1)·p .
```
Sign uniform: coefficient `−1` at `p≡1 mod4`, `+1` at `p≡3 mod4` (i.e. `−χ₂(−1)`).

> **`[VERIFIED-exact in ℤ[ζ_n]]`** at **180 cells** — p=13 (6/6), 43 (30/30), 67 (78/78), 79 (66/66),
> all `a`, 0 failures. (Empirically also 103, 127, 163.)

---

## 2. This identity is EQUIVALENT to the 120° law, and it forces the cap — proved symbolically

Normalize `T=√p·W`, `ε = e₁/√p` (so `|ε| = |V_y(a)|/√p`). With the forced `e₃,e₄` and the identity,
```
L*(a,T)/p² = P(W) = W⁴ − εW³ + (ε² − χ)W² − χεW + 1 ,   χ=χ₂(−1).
```

- **`χ=+1`: `P(W)` is PALINDROMIC** (verified: `P − W⁴P(1/W) = 0`). Set `x=W+1/W`:
  `P/W² = x² − εx + (ε²−3)`. Its discriminant is `3(4−ε²)`.
- **`χ=−1`: `P(W)` is ANTI-palindromic.** Set `y=W−1/W`: `P/W² = y² − εy + (ε²+3)`; with `ε=iu` (`e₁`
  imaginary at `p≡3mod4`) the roots are imaginary ⟺ `3u²−12 ≤ 0`.

**Both cases:**
```
Deligne purity (roots of P on |W|=1, unconditional)  +  the identity  ⟹  |ε| ≤ 2  ⟹  |V_y(a)| ≤ 2√p.
```
So the cap is the reality/sign of the reduced quadratic's discriminant, `3(4−ε²)≥0`.

**And the ζ₃-pairing falls out:** for `χ=+1`, the two conjugate pairs at angles `θ₁, θ₂` satisfy
`x₁+x₂=ε`, `x₁x₂=ε²−3`; substituting `θ₂=θ₁+120°` reproduces `x₁x₂=ε²−3` **exactly** (Sage
`trig_reduce`, `MATCH: True`). So `e₂=e₁²−χp ⟺ θ₂−θ₁=120° ⟺ α₂/α₁=ζ₃` — the identity **is** the
120° law, in closed algebraic form.

---

## 3. What this changes

| before (project roadmap) | after (this result) |
|---|---|
| cap needs: purity A3 + **uniform `u=ζ₃`** (route: L-mono / `ℚ(ζ_n)^{⟨σ_λ⟩}` Galois descent) | cap ⟺ purity + **the single identity `S₂=−S₁²+2χ₂(−1)p`** |
| 120° law proved **per cell** (22 primes); uniform is the open gap; "no finite sweep gives it" | 120° law **⟺** that same identity; uniform 120° = prove **one** `F_p↔F_{p²}` trace identity |
| cap is a separate need | cap is a **corollary** — the discriminant `3(4−ε²)≥0` of the reduced quadratic |

The entire remaining structural gap is now **one explicit identity**, not a monodromy-uniformity
problem stated in the abstract.

---

## 4. Proof route for the identity (started, not closed)

`S₂ = −S₁² + 2χ₂(−1)p` is a Frobenius-descent / Hasse–Davenport-shaped relation. Splitting
`E(F_{p²})` into `F_p`-rational points and Frobenius-pairs `{P, Frob P}`:

- **`F_p`-rational part** (computed): for `P∈E(F_p)`, `χ₂^{(2)}(y_P)=1` (every `y_P∈F_p^*` is a square
  in `F_{p²}`) and `Nm_2 P = 2P`, so this part is `Σ_{P≠O} ψ_{2a}(P) = −1` (nontrivial character on the
  order-`n` group, minus the `O` term).
- **pair part** (open): `{P, Frob P}` each contribute `χ₂^{(2)}(y_P)ψ_a(Nm P)`; relating the pair-sum
  to `S₁² = V_y(a)²` (a double sum over `E(F_p)²`) is the remaining step, and must yield the `2χp`
  boundary term.

An alternative route is the project's **N9** decomposition `H¹ ≅ W ⊕ (W⊗ζ₃)` (`W` rank 2): the identity
`e₂ = e₁² − χp` is a statement about `tr(Frob|∧²H¹)`, which such a decomposition would compute directly.
Both routes are concrete; neither is finished here.

---

## 5. Grades

| item | grade |
|---|---|
| forced `e₄=p²`, `e₃=χ₂(−1)p·e₁` | `[VERIFIED-exact]` (project-confirmed + here to 1e-20) |
| **`S₂ = −S₁² + 2χ₂(−1)p`** (the identity) | **`[VERIFIED-exact, ℤ[ζ_n], 180 cells]`** — not yet PROVED for all `(a,p)` |
| identity `⟹` cap `\|V\|≤2√p` and `⟹` ζ₃-pairing | **`[PROVED — symbolic]`** (palindromic reduction, both χ) |
| the identity, all `(a,p)` | **`[OPEN]`** — route in §4 (Frobenius-descent / N9), started |

**Net for direction #1:** the cap and the uniform 120° law are now a **single explicit power-sum
identity**, verified exactly at 180 cells, with the cap and ζ₃-law proved to follow from it symbolically.
This replaces "prove uniform `u=ζ₃` by monodromy" with "prove one `F_p↔F_{p²}` trace identity" — a
sharper, self-contained target. Proving the identity (§4) is the remaining work.

**No ECDLP content.** `p ≤ 103`; character sums over the public curve.

*Grade legend: VERIFIED-exact · PROVED-symbolic · OPEN.*
