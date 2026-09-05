# Radial self-adjointness of Ĥ=πA² — the load-bearing analytic step (2026-07-10)

Resolving whether the φ(n)-framework's operator is essentially self-adjoint (as
claimed, Thm II.2/II.3, App. B "indices (0,0)") or needs a boundary-condition
extension. Rigorous (deficiency-index) analysis; verified against the standard
examples (Reed–Simon II, §X.1). Under y=log x, `L²([1,∞),dx/x) ≅ L²([0,∞),dy)`,
`A=−ix d/dx ↦ −i d/dy`, `Ĥ=πA² ↦ −π d²/dy²`.

## The defect (on the stated space [1,∞))
- **A = −i d/dy on L²([0,∞)):** A*ψ=+iψ ⇒ ψ=e^{−y} ∈ L² (‖·‖²=½); A*ψ=−iψ ⇒ ψ=e^{+y} ∉ L².
  **Deficiency indices (1,0).** Unequal ⇒ A has **NO self-adjoint extension at all**.
  (The claim "A is e.s.a. by Stone" fails: T_t f(x)=f(eᵗx) maps [1,∞)→[1,∞) only for
  t≥0, so it is a *semigroup*, not a group — Stone's theorem does not apply.)
- **Ĥ = −π d²/dy² on L²([0,∞)):** for each of Ĥ*ψ=±iψ, exactly one root r (Re r<0) gives
  an L² solution. **Deficiency indices (1,1).** ⇒ Ĥ is **NOT essentially self-adjoint**;
  it has a **U(1) family of self-adjoint extensions**, each a boundary condition
  `ψ′(0)=c·ψ(0)` (c∈ℝ), i.e. Dirichlet/Neumann/Robin at x=1. App. B's "(0,0)" is wrong;
  the true indices are (1,1).

Consequence: the framework does not have a canonical, extension-free self-adjoint Ĥ on
[1,∞). It must **choose a self-adjoint extension** (a boundary condition at x=1), and the
spectrum — hence the zero-detection mechanism — depends on that choice. Note also the
"multiplicative modes" e^{±iy} have boundary data ψ′(0)/ψ(0)=±i (complex), which is NOT
a self-adjoint boundary condition — so "D_φ = closure of e^{±iy}" cannot itself be the
self-adjoint domain. Reconciling D_φ with a real boundary condition is the open step.

## The fix (full multiplicative line (0,∞))
State the operator on `L²((0,∞),dx/x) ≅ L²(ℝ,dy)` instead. Then:
- T_t f(x)=f(eᵗx) maps (0,∞)→(0,∞) for **all** t ⇒ a genuine **unitary group** ⇒ Stone
  applies; A=−i d/dy on L²(ℝ) is **e.s.a., indices (0,0)** (e^{∓y}∉L²(ℝ), blow up at ∓∞).
- Ĥ=−π d²/dy² on L²(ℝ) is **e.s.a., indices (0,0)** (no L² exponential solutions).
So on (0,∞) the operator core is genuinely sound and the self-adjointness the framework
needs is real. This is also the natural Mellin domain (x^s lives on (0,∞)). **Cost:** the
averaging P_n and the domain D_φ must be re-derived on the bi-infinite log-line ℝ rather
than the half-line [0,∞) — the mode-selection (multiplicative Fourier support) should
survive, but the derivation changes.

## Correction to the CM capstone (this session)
My earlier claim "Ĥ^CM=π(A_r²+A_θ²) is e.s.a., (0,0)" holds **on (0,∞)** (radial (0,0) ⊕
angular (0,0)). On the stated [1,∞) it inherits the radial (1,1) defect ⇒ indices (1,1),
NOT e.s.a. Same fix (full radial line) repairs it. The sextic angular structure is
unaffected either way.

## Re-expressing D_φ — the fix reveals a deeper obstruction (worked out)
Tried to re-express D_φ on (0,∞) / name its boundary condition on [1,∞). Result:
- **On the CIRCLE ℝ/2πℤ (compact):** with the *un-normalized* P_n (Lemma III.1, multiplier
  = c_n(k)), k=±1 stay bounded (|c_n(±1)|=|μ(n)|=1) while |k|≥2 are amplified once a prime|k
  enters the primorial (verified: c_n(3)=−1,−2,2,−2,… grows). So along the μ(n)=+1 subsequence
  P_n e^{±iy}=e^{±iy}, giving **D_φ = span{e^{±iy}}**; and Ĥ=−π d²/dy² is e.s.a. on the compact
  circle (indices (0,0)), Ĥe^{±iy}=πe^{±iy}. **No boundary condition needed — this is D_φ's clean home.**
- **On the full line (0,∞):** with the *normalized* multiplier c_n(k)/φ(n) (the §2/§3 definition),
  EVERY fixed k (incl. ±1) has c_n(k)/φ(n)→0 (verified). So P_n f→0 and **D_φ={0} is trivial.**
  The full-line fix restores self-adjointness but *empties* D_φ — so it is NOT a clean re-expression.

**The real obstruction (the load-bearing gap, sharper than a boundary condition):**
- (B) a nontrivial D_φ=span{e^{±iy}} lives on the **circle** (discrete k; the 2πr/n shifts are periodic).
- (C) the Mellin probe `x^{s₀}=e^{s₀y}` for a zero s₀=½+iγ lives on the **line** (general s∈ℂ; on the
  circle x^s is periodic only for s∈iℤ, so a general zero is not representable).
- (B) and (C) are on **incompatible real-place spaces**. The half-line boundary-condition puzzle was a
  *symptom*; the genuine gap is that the averaging (circle) and the zeros (line) are not the same object.
  Bridging them needs an **adelic / Connes-type space** (multiplicative + additive structure together) —
  precisely the structure the naive one-place operator lacks. Also surfaced a normalization clash: the
  definition carries 1/φ(n) (⇒ D_φ trivial), while Lemma III.1 drops it (⇒ D_φ=span{e^{±iy}}); only the
  un-normalized version is internally consistent.

**CM version:** identical circle/line tension (the radial factor), now decorated by the μ₆ angular
sectors. The sextic structure is orthogonal to this obstruction and survives it.

## Status
Genuine, checkable defect in the analytic foundation (indices (1,1), not (0,0), on the
stated space), with a clean constructive fix (full line (0,∞)). It is load-bearing: it
sits under both the rational spectral-wall and the CM operator side. The one remaining
open piece is to re-express D_φ on (0,∞) and confirm it selects the intended self-adjoint
realization (equivalently, on [1,∞), to name the boundary condition D_φ imposes at x=1).
