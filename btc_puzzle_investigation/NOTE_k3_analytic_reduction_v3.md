# NOTE v3 — k=3 channel: the |T|-tail attacked; gap reduced to a sparse-near-zeros bound

**Extends v2.** Date 2026-08-17. Companion to
[CONFIRMED_k3_phase_channel_weierstrass_v1.md](CONFIRMED_k3_phase_channel_weierstrass_v1.md),
[v2](NOTE_k3_analytic_reduction_v2.md) (main term via slope²).

## Recap of what is PROVED (v2)
`Σ_b χ₂(b) T(a₀,b)³ = i√p·W(0)`, `W(0)=n²−O(n)>0` via `x₁+x₂+x₃=m²` (slope²) ⟹ `χ₂=+1` main term.
Un-normalized k=3 × χ₂ channel PROVED nonzero; `a₀`-genericity explained (flat `s=0` mode).

## The |T|-distribution (this note)
The banked object is the phase channel `|mean_QR| = |Σ_b χ₂ e^{3iθ}|/…`, `e^{3iθ}=T³/|T|³`. Transfer from
the proved `T³` result is obstructed by `1/|T|³` at small `|T|`. Attacked via moments:

- **2nd moment — PROVED exact:** `⟨|T|²⟩ = (p(n−2)−1)/(p−1)`. Derivation: `Σ_b e_p(b(x_d−x_{d'})) = p·[x_d=x_{d'}]−1`,
  and `x_d=x_{d'} ⟺ d'∈{d,n−d}`; the `d'=n−d` cross-term sums to `−1`. Matches to the digit (p=43…823).
- **4th moment — bounded:** `⟨|T|⁴⟩/n² → ~1.9` (= additive energy of the x-coords / `n²`, near the diagonal
  minimum 2). So `|T|²/n` has bounded 2nd moment — no fat upper tail.
- **Small-`|T|` tail is LOWER ORDER (measured):** dropping all `b` with `|T|²<0.1n` leaves the phase channel
  essentially unchanged (`phase_noSmall ≈ phase_full`); those `O(n)` frequencies contribute only `~√n`
  (measured 1–5 vs the `O(p)` main term). Their phases carry no `χ₂`-coherent bias ⟹ they random-walk away.

## Near-zeros count (measured) — the tail bound holds
`|T|²/n` is exponential-like: `E[r]=1.00`, `E[r²]=1.87–1.96` (exp 2), `E[r³]=5.06–5.86` (exp 6) — moments
track `k!` through 3rd order (slightly thinner). Near-zeros run at/below the exponential rate:
`#{b:|T|²<εn} ≈ ε(p−1) = O(εn) = o(n²)` (e.g. p=823: `#{r<0.05}=38≈0.05n`; linear in n). So the small-`|T|`
tail contributes `O(√n)` to the phase sum vs the `O(p)` main term — the transfer obstruction is lower-order.

## Remaining rigorous gap (precise, named)
An **equidistribution statement for `|T(a₀,b)|²`**: its distribution is exponential-like, equivalently
`#{b:|T|²<εn}=O(εn)` with `χ₂`-incoherent phases on those frequencies. Supported here by 4 matching moments
+ the linear near-zeros count. This is a Sato–Tate / moment-method result for the character sum `T` (the
kind proved for Kloosterman-type sums) — the single named estimate between this and a full proof of
`|mean_QR| ≥ c`. NOT supplied by the upper moments (Markov bounds the large-`|T|` tail only); it wants a
direct equidistribution argument. No unnamed gaps remain.

## Grade
- Un-normalized k=3 × χ₂ channel: **PROVED**. Mechanism (slope² ⟹ +1): identified.
- `⟨|T|²⟩`: **PROVED exact**. `⟨|T|⁴⟩ ~ c n²`: computed, bounded.
- Phase channel `|mean_QR| ≥ c` (banked): **EMPIRICAL**; tail shown lower-order (measured); the single
  remaining rigorous step is the sparse-near-zeros count for `T`. No further hand-wave — that count is the
  named open estimate.
