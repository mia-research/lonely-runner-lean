# NOTE — k=3 phase channel: analytic lower-bound attempt (reduction + where it stalls)

**Status: PROGRESS, NOT A PROOF.** Rigorous reduction of the *un-normalized* moment; the *concentration*
(the actual channel) remains OPEN. Date 2026-08-17. Companion to
[CONFIRMED_k3_phase_channel_weierstrass_v1.md](CONFIRMED_k3_phase_channel_weierstrass_v1.md).

## Target
Prove `|mean_QR| = |(1/|QR|)Σ_{b∈QR} e^{3iθ(b)}| ≥ c > 0` (asymptotic), `θ(b)=arg T(a₀,b)`,
`T(a₀,b)=Σ_{d=1}^{n-1} e_p(b x_d)e_n(a₀ d)`. This is the one lemma between EMPIRICAL and PROVED.

## Rigorous reduction (verified, exact)
For the un-normalized third moment, the Gauss-sum evaluation `Σ_b χ₂(b)e_p(bS)=χ₂(S)g(χ₂)` (|g|=√p) gives
```
Σ_b χ₂(b) T(a₀,b)³ = g(χ₂) · U,   U = Σ_{d₁,d₂,d₃=1}^{n-1} χ₂(x_{d₁}+x_{d₂}+x_{d₃})·e_n(a₀(d₁+d₂+d₃)).
```
Verified numerically (identity holds to 1e-6; both sides purely imaginary for p≡3 mod4, as the parity
lemma requires). **`U` is a Semaev character sum:** fixing `d₁+d₂+d₃≡s` forces `P₁+P₂+P₃=[s]G`, i.e. the
triple lies on the 3rd summation-polynomial variety `S₃=0`; `U` weights it by `χ₂` of the x-sum.

## Measured scalings (CM x³+7, p≡3 mod4)
| object | scaling | reading |
|---|---|---|
| phase channel `\|Σ_b χ₂ e^{3iθ}\|` | `≈ 0.28·p` | order-p MAIN TERM = the concentration |
| un-normalized `\|Σ_b χ₂ T³\|` | `≈ 0.8·p^{2.5}` | main term; `\|U\|~n²` (one-dim main term on S₃) |

Both are main-term phenomena — the concentration is real and structural.

## Where it stalls (honest)
1. **Wrong object.** The clean reduction bounds the *un-normalized* `T³`. The concentration lives in the
   *phase* `T³/|T|³`. The `|T|⁻³` normalization is NOT a character sum; Gauss/Weil tools don't reach it.
   The un-normalized moment (√p·U) and the phase channel scale differently, so bounding U does not bound
   `|mean_QR|`.
2. **Semaev territory.** Even the tractable object `U` requires a MAIN-TERM LOWER bound on a summation-
   polynomial character sum — the project's own open `µ₆ solving-degree` frontier
   (`ANALYSIS_semaev_cm_yield_mechanism`, `PREREG_mu6_solving_degree`). Lower bounds on character sums are
   not given by Weil (that's an upper bound); a main term must be exhibited.

## Net
Reduction is exact and locates the difficulty precisely (phase-normalization crux, on the S₃ variety).
It does NOT prove the bound. The channel stays **EMPIRICAL** (strong: order-p main term, `|mean_QR|·√|QR|`
grows 2→7). Grade unchanged. The proof is a research-level estimate, not an in-session result.
