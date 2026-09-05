# NOTE — N8 reduced to ONE lemma: a signed χ₂-sum over the pencil `|(R)+(O)|` equals 1. Everything else is closed-form and machine-checked.

**Date:** 2026-09-01. **Scripts:** `scratchpad/n8/pencil_vanishing_v1.py`, `scratchpad/n8/reduction_chain_v1.py`.
Exact integers only; no float. `Z[ζ_n]` elements as length-`n` coefficient vectors (`v=0 ⟺ all entries equal`).

**Object.** N8 = *"why does `e₂ = e₁² − χ₂(−1)p` hold?"* (M21, 1171 cells / 11 primes; P19 `[PROVED — uniform]`).
Ledger's sharpened form: *"prove the identity from `hist_k1`/`hist_k2` — Hasse–Davenport / Frobenius-square shape."*

---

## 1. Setup

`E/F_p`, `p>3`, `n = #E(F_p)`, `χ := χ₂(−1)`, `ψ` a nontrivial character of `E(F_p)`.
`V₁ = Σ_{P∈E(F_p)} χ₂(y_P)ψ(P)`, `V₂ = Σ_{Q∈E(F_{p²})} χ₂^{(2)}(y_Q)ψ(Nm Q)`. Target: **`V₁² − V₂ = 2χp`**.

**The pencil.** For `R ∈ E(F_p)`, the effective `F_p`-rational degree-2 divisors `D` with `sum(D) = R` are
exactly the fibres of `φ_R : E → P¹` from `|(R)+(O)|` — **`p+1` of them** (machine-checked: `#split +
#inert + 1 = p+1` at every `R`, every curve tested). Each is split (`{P,P'} ⊂ E(F_p)`), inert
(`{Q, Frob Q}`, `Q ∈ E(F_{p²})∖E(F_p)`), or the distinguished `(O)+(R)`.

**The weight is the same object in both cases.** For `z ∈ F_{p²}*`, `N(z) = z^{p+1}` and
`χ₂(N(z)) = z^{(p²−1)/2} = χ₂^{(2)}(z)`. So the fibre norm of `y` gives `χ₂(y_P)χ₂(y_{P'})` on split
fibres and `χ₂^{(2)}(y_Q)` on inert ones — one function on the pencil. `(O)+(R)` contributes 0 (`y` has a
pole). Write `Sp(R)`, `I(R)` for the split / inert totals.

## 2. THE LEMMA — the entire remaining content of N8

> **Lemma.** `n` odd ⟹ for every `R ∈ E(F_p)`, `R ≠ O`:  **`Sp(R) − I(R) = 1`.**
>
> Equivalently `Σ_{t∈P¹(F_p)} χ₂(N_{φ_R}(y)(t))·χ₂(δ_R(t)) = 1`, `δ_R` the fibre discriminant.

**Status `[VERIFIED — exact, all R, firing control fires]`**, `pencil_vanishing_v1.py`:

| arm | curves | result |
|---|---|---|
| `n` ODD, **j=0** | p=19 | **12/12** `R≠O` |
| `n` ODD, **non-j=0** | p=17,19,23,29 | **14/14, 26/26, 28/28, 32/32** |
| `n` EVEN — **firing control** | p=13,19,23 | **0/17, 0/11, 0/15** — fails at *every* `R` |

## 3. The rest of the chain — closed form, machine-checked `[PROVED — elementary]`

| step | statement | proof | checked |
|---|---|---|---|
| (a) | `Sp(R) = (h₁(R)+1)/2`, `h₁(R) = Σ_{P≠O,R} χ₂(y_P y_{R−P})` | the involution `P ↔ R−P` on ordered split pairs has exactly one fixed point (`2P₀=R`, unique since `n` odd), contributing `χ₂(y_{P₀})²=1` | ✓ |
| (b) | `h₁(O) = (n−1)·χ` | `χ₂(y_P y_{−P}) = χ₂(−y_P²) = χ` for each of the `n−1` affine `P` | ✓ |
| (c) | **`I(O) = −χ·(2p+1−n)/2`** | `Q+Frob Q = O ⟺ Frob Q = −Q ⟺ y_Q^{p−1} = −1`, hence `χ₂^{(2)}(y_Q) = (−1)^{(p+1)/2} = −χ` — **constant on the whole set**; and that set is `E'(F_p)` for the quadratic twist, of size `2p+2−n`, giving `(2p+1−n)/2` conjugate pairs (an integer exactly because `n` is odd) | ✓ |
| (d) | `V₁² − V₂ = (n−1)χ − 2I(O)` **`= 2χp`** | Lemma ⇒ `I(R)=Sp(R)−1` off `O`; `Σ_{R≠O}ψ(R) = −1`; rational `Q` contribute `Σ_{P≠O}ψ(2P) = −1` (`P↦2P` bijective, `n` odd); substitute (a)–(c). `(n−1)χ + χ(2p+1−n) = 2χp` | ✓ |

`reduction_chain_v1.py` verifies (a)–(d) **and** the identity itself in `Z[ζ_n]` at every `a`:

```
p= 17 A=1 B=5 n= 15 chi=+1 | (a):True | CORE Sp-I=1:True | (b):True | (c):True | (d) V1^2-V2=2chi p:14/14
p= 19 A=0 B=3 n= 13 chi=-1 | (a):True | CORE Sp-I=1:True | (b):True | (c):True | (d) V1^2-V2=2chi p:12/12
p= 19 A=3 B=1 n= 27 chi=-1 | (a):True | CORE Sp-I=1:True | (b):True | (c):True | (d) V1^2-V2=2chi p:26/26
p= 23 A=1 B=4 n= 29 chi=-1 | (a):True | CORE Sp-I=1:True | (b):True | (c):True | (d) V1^2-V2=2chi p:28/28
p= 29 A=2 B=1 n= 33 chi=+1 | (a):True | CORE Sp-I=1:True | (b):True | (c):True | (d) V1^2-V2=2chi p:32/32
```

Both `χ` branches, j=0 and non-j=0. **`n` odd is used in (a), (c) and (d) independently** — it is not a
single-point hypothesis.

## 4. Where the ζ₃ comes from — and why this is not a CM phenomenon `[OBSERVATION, not proved]`

`n` odd `⟺` `E(F_p)[2] = 0` `⟺` **`x³+Ax+B` is irreducible over `F_p`** (a cubic with no root is
irreducible) `⟺` **Frobenius acts on `E[2]∖{O}` as a 3-cycle.** That is the *only* place a cube root of
unity can enter for a curve with no `μ₃` automorphism — and it explains the record's long-standing
surprise that the hypothesis is `n` odd rather than `j=0`.

Independently (algebra, this session): the identity `e₂ = e₁² − χp` is **equivalent** to the quartic
factoring as `(T²−aT+χp)(T²−bT+χp)` with `a+b=e₁`, `ab=e₁²−3χp`; and, given purity (P20), to the
spectrum being `{α, χᾱ, ζ₃α, χζ̄₃ᾱ}` — the "120° law". So the ζ₃ in the spectrum and the 3-cycle on
`E[2]` are the same phenomenon. **Lead for proving the Lemma:** the four branch points of `φ_R` are
`{Q₀ + T : T ∈ E[2]}` (`2Q₀ = R`) — an `E[2]`-torsor, on which Frobenius acts through that 3-cycle.

## 5. Scope / owed

- The Lemma is **verified, not proved** — 5 curves, all `R`, with a control that fails everywhere.
  `[VERIFIED — exact]`, not `[PROVED]`.
- §3 is elementary and complete; §4's mechanism is a **lead**, not an argument.
- P19 already grades the identity `[PROVED — uniform]` via Galois descent on `E[2]`. **This NOTE does not
  re-prove it** — it supplies a *different, elementary* route that isolates the whole difficulty into one
  statement about a pencil, which is what N8 asked for. If the Lemma is proved directly, N8 closes and
  (per the ledger) T2's finite shadow closes with **no GKR and no sheaf isomorphism**.
- No ECDLP content. Pure structure.

---

## 6. UPDATE (same day) — the Lemma is an explicit DEGREE-7 character sum on the x-line, and the mechanism is reconstructed

**The translation.** `n` odd ⟹ `2` is invertible on `E(F_p)` ⟹ `Q₀ := R/2` is **rational**. Translating by
`−Q₀` carries `{deg-2 divisors, sum R}` onto `{deg-2 divisors, sum O}` = the fibres of `x : E → P¹`.
The fibre weight becomes `χ₂( y(P+Q₀)·y(Q₀−P) )`, a function of `x(P)` alone (the two factors swap under
`P ↦ −P`). The fibre over `c=∞` is `2(O) ↔ 2(Q₀)`, weight `χ₂(y(Q₀)²)=1` — that is the `1`.

> **Lemma ⟺ `Σ_{c∈F_p} χ₂(c³+Ac+B) · χ₂( y(P+Q₀)·y(Q₀−P) ) = 0`.**

`[VERIFIED — exact, every `R`, `scratchpad/n8/xline_reduction_v1.py`]`: p=19,31 (j=0) and p=17,19,23,29
(non-j=0) — `12/12, 42/42, 14/14, 26/26, 28/28, 32/32`.

**Divisor computation ⇒ an explicit degree-7 polynomial.** With `S=Q₀` and `T₁,T₂,T₃` the 2-torsion:
`div( y(P+S)y(S−P) ) = Σ_i[(T_i−S)+(T_i+S)] − 3(S) − 3(−S)`; both are `±`-symmetric, so as a function of
`x` it is `κ·∏_i(x − x(T_i+S)) / (x − x(S))³`. Since `χ₂(z³)=χ₂(z)`:

> **Lemma ⟺ `Σ_{c∈F_p} χ₂( f(c) ) = 0`, `f(c) = (c³+Ac+B)·∏_{i=1}^{3}(c − x(T_i+Q₀))·(c − x(Q₀))`**, `deg f = 7`
> (the constant `κ` only flips an overall sign, which `=0` is insensitive to).

Explicitly `x(T_i+S) = (t_i u + 2t_i² + A)/(u − t_i)` with `u=x(S)`, `t_i=x(T_i)` — derived using
`Σt_i=0`, `Σ_{i<j}t_it_j=A`, `t_i³=−At_i−B`.

**The mechanism (reconstructed independently; matches the record's P19 route).** `E[2] ≅ (Z/2)²` acts on
`E` by translation, commutes with `[−1]` (`T` is 2-torsion), hence descends to a **Klein four-group
`V={1,σ₁,σ₂,σ₃}` of Möbius involutions of `P¹ = E/±`**, `σ_i(x) = (t_i x + 2t_i² + A)/(x − t_i)`.
**`n` odd ⟺ `x³+Ax+B` irreducible ⟺ Frobenius 3-cycles `T₁,T₂,T₃`, hence 3-cycles `σ₁,σ₂,σ₃`.** The three
*nontrivial characters of `V`* are therefore permuted cyclically by Frobenius, so the trace of Frobenius
on their summed contribution is **0** — the vanishing. This is the record's *"E[2]-translations descend to
involutions that Frobenius 3-cycles, forcing trace 0"*, here re-derived from scratch and made explicit.

**Status.** The reduction and the degree-7 form are `[VERIFIED — exact]`. The trace-0 step is stated at the
level of mechanism, not written out as a proof. **P19 already grades the identity `[PROVED — uniform]`;
this NOTE does not add a grade** — it supplies an elementary, fully explicit route (one degree-7 character
sum) that a reader can check on a laptop, which is what an open-repro package needs.

---

## 7. PROOF OUTLINE for the Lemma, with its structural predictions confirmed

**Reduction to a genus-3 trace.** `χ₂(κ)=+1` at every tested `(p,A,B,R)` (measured), so
`Σ₁ := Σ_{c∈F_p} χ₂(f(c))`, `f = (c³+Ac+B)·q_R(c)`, `q_R(x) = ∏_{2Q=R}(x−x(Q)) = x⁴ − 4x_Rx³ − 2Ax² −
(8B+4Ax_R)x + (A²−4Bx_R)`. `deg f = 7`, so `C : y² = f(c)` is **hyperelliptic of genus 3** with one point
at infinity, and `Σ₁ = −a_p(C)`.

**⚠ A hand-step that DIED on contact with data (recorded so it is not retried).** I first claimed
`Jac(C_R) ≅ E` for the quartic part, giving `Σ_cχ₂(q_R) = −1−t` constant in `R`. **False:**
`quartic_identify_v1.py` shows `Σ_cχ₂(q_R)` *varies with* `R` (p=19: `−2` at `R=(1,2)`, `+2` at `R=(2,7)`)
while `−1−t = −8` is constant. What IS true and measured: `Σ₁+Σ₂ = h₁(R)−1` and `χ₂(κ)=+1`, hence
`Σ₂ = Σ_cχ₂(q_R) = 2·I(R)`.

**The outline.**
1. Branch locus of `C` = the 7 roots plus `∞` = **`x(E[2]) ∪ x([2]⁻¹R)`**, eight points.
2. `V = E[2]` acts on `P¹ = E/±` by `σ_T(x(P)) = x(P+T)` (translation commutes with `[−1]`) and
   **preserves that locus** (`σ_T` permutes `x(E[2])` and permutes `x([2]⁻¹R)`). Hence `V` lifts to `C`.
3. `C/V ≅ P¹`; the `(Z/2)²` genus formula `g(C) + 2g(C/V) = Σ_i g(C/σ_i)` gives `Σ_i g_i = 3`, i.e.
   **`C₁,C₂,C₃` are genus 1**.
4. Kani–Rosen: `Jac(C) ~ Jac(C₁) × Jac(C₂) × Jac(C₃)`.
5. **`n` odd ⟺ `x³+Ax+B` irreducible ⟺ Frobenius 3-cycles `T₁,T₂,T₃` ⟹ it 3-cycles `σ₁,σ₂,σ₃` ⟹ it
   permutes `C₁,C₂,C₃` cyclically.**
6. A block permutation with **no fixed block has trace 0** ⟹ `a_p(C) = 0` ⟹ `Σ₁ = 0`. ∎

**The mechanism's own falsifier, run (`frobenius_cycle_prediction_v1.py`).** `Frob²` is still a 3-cycle;
`Frob³` is trivial. So the sum must vanish over `F_p` **and** `F_{p²}`, and must **not** over `F_{p³}`:

| p | A,B | `Σ` over `F_p` | `F_{p²}` | `F_{p³}` |
|---|---|---|---|---|
| 17 | 1,5 | **0** | **0** | 42 = 3·14 |
| 19 | 0,3 | **0** | **0** | −12 = 3·(−4) |
| 19 | 3,1 | **0** | **0** | 204 = 3·68 |
| 23 | 1,4 | **0** | **0** | −96 = 3·(−32) |

Both predictions confirmed, j=0 and non-j=0. **And every `k=3` value is divisible by 3** — forced by
three Galois-conjugate elliptic blocks once `Frob³` fixes each (`a_{p³}(C) = 3·a_{p³}(C₁)`). That
divisibility was *not* used to build the outline; it is an independent corroboration of step 4.

**Status.** `[PROOF OUTLINE — steps 3,4 standard but not written out here; 1,2,5,6 elementary; all
structural predictions confirmed numerically]`. This is *not* a grade move: P19 already carries the
identity as `[PROVED — uniform]`. The value here is that the whole thing is now **one genus-3 trace
computation a reader can reproduce on a laptop**, with a built-in falsifier.
