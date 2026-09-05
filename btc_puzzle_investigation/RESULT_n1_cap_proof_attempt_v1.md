# RESULT — the exact 2√p cap: attacked, not closed. 3 mechanisms ruled out, cap strengthened to a robust conjecture (v1, 2026-07-24)

**Problem** (the open piece from `RESULT_arm2_eigenvalue_v1.md`): prove that the twisted sum
`V_y(a) = Σ_d χ₂(y_d) e_n(a·d)` satisfies `max_a |V_y(a)| ≤ 2√p` — half of its Weil–Deligne ceiling
`4√p` (the sheaf is genuinely dim-4, `A_new`). This cap **is** the N1 ½-saturation.

**Honest headline: the cap is now a robust empirical theorem, but it is NOT proved. Three candidate
mechanisms were computed and REFUTED. The exact proof is a genuine open problem.**

---

## 1. The cap as a hard empirical theorem `[VERIFIED exact, 40 primes, 0 violations]`

`max_a |V_y(a)| / √p` over **40 primes** (`p ≡ 1 mod 3`, `n` prime, `p ≤ 3853`, all frequencies `a`):

```
min 1.555   mean 1.924   MAX 1.9998 (at p=1237)   violations of 2.0:  NONE
```

Never exceeds `2.0`; approaches it from below as `p` grows (55% of primes already in [1.95, 2.00]).
Combined with Experiment 1 (22 primes, saturation → 0.500), this is a **hard cap `max|V_y| ≤ 2√p`**
holding on ~50 distinct primes with 0 counterexamples — a solid conjecture, not yet a theorem.

**Source check (methodology: source-first).** The standard Weil bound for a Kummer sheaf gives
`(#R)·√p = 4√p` (the memory's P6b). No off-the-shelf result was found giving the sharper `2√p` for the
odd `y`-coordinate; the closest literature (Kohel–Shparlinski exponential sums; 2025 "division
polynomials twisted by multiplicative functions", arXiv:2508.03988; the µ₄-normal-form line) is
adjacent but does not state this cap. So `2√p` is not a citable known bound.

---

## 2. Three candidate mechanisms — each computed and REFUTED

Following the project rule (*kill a NAMED mechanism, never assert an unnamed symmetry*):

| # | candidate mechanism | killed by | verdict |
|---|---|---|---|
| M1 | **dim-2**: χ₂(y) H¹ carries top mass in dimension 2 | Arm 2 cover zeta: `A_new` is **dim-2 (4 eigenvalues)**, char poly `T⁴+pT²+p²` | **REFUTED** — χ₂(y) is dim 4 |
| M2 | **[−1] 2+2 coupling** (addendum §A2.6-4): definite-parity `y`-readout couples to one 2-dim half → 2√p | p=13 twisted config: `V_y = 2√p(cos38°+cos158°)` uses **all 4** eigenvalues, not 2 | **REFUTED** — all 4 contribute |
| M3 | **120° conjugate pairs**: eigenvalues = two conj. pairs 120° apart → `V_y = 2√p·cos(θ+60°)` | predicted identity `m₁²+m₂ = 2p`; **holds at p=13, FAILS at p=43,67,79,127,163** (`|m₁²+m₂−2p| ~ 10²`) | **REFUTED** for p>13 |

M2/M3 were the *natural* structural guesses (self-duality, CM 120°); their failure means the cap is
**not** explained by a fixed low-dimensional coupling or a rigid eigenvalue-angle relation. The four
twisted eigenvalues are general Weil numbers whose sum is bounded by a subtler constraint.

---

## 3. The live lead — the autocorrelation `c(t)`

`|V_y(a)|² = Σ_t c(t) e_n(a·t)` with `c(t) = Σ_d χ₂(y_d)χ₂(y_{d+t})` (exact integer). Findings:

- `c(t)` is **μ₆-structured** (constant on μ₆-orbits of `t`) and takes **few distinct values**
  (4 at p=43; growing slowly with p), all with μ₆-multiplicities.
- `c(t)` is **partly governed by `χ₂(x_T)`** (`T = [t]G`): `χ₂(x_T)=+1 ⟹ c(t)∈{−9,11}`,
  `χ₂(x_T)=−1 ⟹ c(t)∈{−5,−1}` at p=43 — but a residual binary split within each class depends on
  finer arithmetic of `T`, so `c(t)` is **not** a simple closed form in `χ₂(x_T)` alone.
- `c(t)` itself appears bounded by `~2√p` (max `|c(t)|=21≈1.86√p` at p=127) — a nested character sum.

A closed form for `c(t)` (or a proof that its DFT caps at `4p`) would close the problem. That is the
precise remaining object.

---

## 4. Grade and status

| claim | grade |
|---|---|
| N1 ½ magnitude `= 2√p/4√p` | `[VERIFIED exact]` (Exp 1 + this: ~50 primes) |
| `max_a\|V_y(a)\| ≤ 2√p` (hard cap) | `[CONJECTURE — strong]`: 40 primes, 0 violations, →2; not proved |
| mechanism M1 dim-2 / M2 2+2 / M3 120° | **all REFUTED** |
| exact proof of the cap | **OPEN** — reduces to the structure of `c(t)` / the geometric monodromy of the family `{L_{χ₂(y)}⊗L_{ψ_a}}` |

**This is the honest outcome of "addressing the problem": the cap did not fall to the available
mechanisms. What was achieved — a robust exact-cap conjecture on ~50 primes, three named mechanisms
killed, the difficulty localized to `c(t)` / monodromy, and confirmation it is not a citable known
bound — is real progress, not a proof.** Per the project's standard, a dissolved candidate is a
positive result; three dissolved candidates sharpen the target without overclaiming.

**No ECDLP content** (character sums over the public curve; `p ≤ 3853`).

*Grade legend: VERIFIED (exact) · CONJECTURE · REFUTED · OPEN.*
