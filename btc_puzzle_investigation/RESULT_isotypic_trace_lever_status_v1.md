# RESULT — isotypic trace `ℓ(d)`: sync with parallel sessions + the lever question, tested on the real object

**Date:** 2026-08-16. Continues `RESULT_LBE_alignment_key_leakage_audit_v1.md` after pulling the
exact definitions from parallel-session work already in the repo. Script:
`scratchpad/session_2026-08-11/trace_openq_test.sage` (extends the other sessions'
`lbe_dlog.sage`). Grade: `[VERIFIED — exact, scope p=43 / |A_new|=1893]` for the three
structural tests; `[OPEN]` for the partial-info residual (unchanged from the source docs).

## Sync — what the "other accounts" already established (and how my session's tests map)

| my session (reconstruction) | parallel-session result (exact object) | relation |
|---|---|---|
| Comp 1: `(j,s)` leaked but ~0 bits about `d` | `ANALYSIS_public_gate_glv_carry_circularity_v1`: χ₃ reads orbit label; `d₀` unknown ⇒ relation between two unknowns; χ²=4.27, perm p=0.373 | **convergent** (independent) |
| Comp 3: `ε=[d+a≥n]` not observable from `P` | `RESULT_eps_to_d_constraint_v1/v2`: **two distinct objects** — public flap `eps(x)` (no `d`) vs LBE carry `ε_LBE=[d₁λ^j+d₂λ^j≥m]` (contains `d`); pre-registered, powered, plants fired: flap ≠ carry, gate `s<3/16` holds for flap, **fails for carry** (21–93 viol) | **convergent + sharper** (they separated the two ε's I had merged) |
| Comp 2: "trace" = χ₂(y)/χ₃(x), no ±0.58 | **WRONG OBJECT.** Real trace `ℓ(d)=dlog_{A_new}(S([d]G))`, `S`=isotypic projection into the supersingular `A_new` of `Jac(w⁴=x³+B)` (`OPEN_lbe_isotypic_projection_v1`) | **corrected — my Comp 2 tested a different function** |

So my Comp 2 null does not bear on their trace. Comp 1 and Comp 3 stand and are reinforced by
independent parallel derivation. The linchpin identity `eps == ε_LBE` is **falsified at scope** by
the parallel work (the same public predicate `s<3/16` separates the two objects).

## The real trace object, tested (their open Q1/Q2 + the structural crux)

`ℓ(d) = dlog_{A_new}(S([d]G))`, `A_new` order 1893 = 3·631, base of order 1893, `p=43`, `B=7`,
`λ=25`. Reproduced their `ℓ(d)` table (15 rational-lift `d`), then:

- **Q2 — μ₃-orbit covariance: YES.** `ℓ(λd) = k·ℓ(d) mod 1893` with `k∈{1849, 587}` (1849 = 43²,
  the σ-eigenvalue). So within an orbit `{d,λd,λ²d}` the three trace values are `{e,ke,k²e}` —
  orbit-structured, i.e. `ℓ` carries the **orbit label** and nothing finer at the covariance level.
  That label is the same `log₂3` bits the public χ₃ already gives — vacuous for `d` (Comp 1).
- **Q1 — affine in `d`: NO.** `ℓ(d)=a·d+b mod 1893` fails 13/15. No linear equation for `d`.
- **Homomorphism `ℓ(2d)=2ℓ(d)`: NO** (0/3). The lift is non-homomorphic, as expected from
  `E` ordinary + `A_new` supersingular ⇒ `Hom(E,A_new)=0`.

## The structural crux — where security actually sits here (named, not a mood)

`A_new` is **supersingular with embedding degree 3**: `631 | p³−1`, `631 ∤ p−1, p²−1` (verified at
p=43; structural). So `A_new`'s DLP **transfers to `F_{p³}*`** — a MOV/Frey–Rück channel, and at
secp scale `F_{p³}` is ~768-bit where DLP is **sub-exponential** (NFS), unlike secp's `2¹²⁸` Pollard-ρ.
**The only thing blocking a sub-exponential break is that `S` is non-homomorphic** (`Hom(E,A_new)=0`):
there is no linear map carrying `E`'s ECDLP into `A_new`, so the low-degree MOV structure of `A_new`
cannot be reached from `[d]G`. Both facts verified above.

**Consequence for the lever question.** To use `ℓ(d)` you must (a) evaluate it — itself a dlog in
`A_new` (an `F_{p³}` DLP at scale), and (b) invert `d↦ℓ(d)`, which is non-affine and non-homomorphic.
The affine lever and the MOV/homomorphic-transfer lever are **both refuted** at this scope. What
remains genuinely **OPEN** (unchanged from `OPEN_lbe_isotypic_projection_v1` Q3/Q4): whether the
*non-homomorphic, orbit-covariant* `ℓ(d)` carries any **partial** `d`-information beyond the orbit
label. No mechanism for such partial info is identified, and any that existed would still sit behind
the `A_new` dlog. Per project stance this is a lever stated as a lever, not a closure.

## THE GLV-halves factoring test (the live thread) — `scratchpad/session_2026-08-11/halves_final.sage`

**Why it mattered (analytic, not pre-dismissed).** The orbit action `d↦λd` rotates the GLV halves
`(d₁,d₂)↦(−d₂, d₁−d₂)` (Eisenstein order-3). If `ℓ` were affine in the halves, `ℓ=a·d₁+b·d₂+c`, the
covariance `ℓ(λd)=k·ℓ(d)` forces `c=0`, `b=k·a`, and `k²+k+1=0` — **satisfied** by the cube-root `k`.
So affine-in-halves is *consistent* with the known covariance and is the natural candidate — worth
testing, not deflating. And if it held it would be a **real lever**: `ℓ(d)` gives one linear equation
`a·d₁+b·d₂=ℓ` in the two `√n`-sized halves → CVP-solvable with the size bounds.

**Result (fit over GF(631), the embedding-degree-3 prime part; 15 rational-lift `d` at p=43):**

| fit | violations | read |
|---|---|---|
| **POSCTRL** synthetic affine-in-halves | **0/15** | machinery recovers a true affine relation |
| affine-in-`d` | 15/15 (inconsistent) | known negative, confirmed |
| **affine-in-`(d₁,d₂)`** | **15/15 (inconsistent)** | **no affine factoring — the lever is absent** |
| quadratic-in-`(d₁,d₂)` | 15/15 (inconsistent) | not even a degree-2 form |
| NEGCTRL shuffled `ℓ` | 15/15 | control fails as it must |

**Answer to the live thread: NO** (at this scope). `ℓ(d) mod 631` is not an affine or quadratic
function of the GLV halves; the positive control confirms the test would have caught one. The only
clean structure remains the orbit covariance (vacuous for `d`). The candidate partial-break — an affine
relation in the halves — was a priori consistent with the covariance and **empirically does not hold**.

## Owed / next probes (concrete)
- **Scale.** This is p=43 / 15 points only. Larger `A_new` is owed, but the Sage **function-field
  Jacobian build hangs unreliably** (wedged Singular) above p=43 this session — the scaling is blocked
  on a faster `A_new`/dlog realization (e.g. a genus-2 model of `A_new`, or MOV image in `F_{p³}*`), not
  on the test logic. Grade stays `[VERIFIED — scope p=43]`, not powered at scale.
- Higher-degree / non-polynomial factorings not excluded (no mechanism suggests them; all less exploitable).
- Rerun Q1/Q2 at a larger `A_new` (bigger `p≡1 mod 3`, `y²=x³+7`) — 15 points is their-data-scale;
  the covariance/affine reads want more points before "orbit label only" is powered.
- The one untried finer test: does `ℓ(d)` factor through the **GLV halves** `(d₁,d₂)` non-linearly in
  a way computable *without* the `A_new` dlog? (their Q1 second half — not yet built).
- experiment-designer pre-reg not run (gate unavailable) — [PROVISIONAL] on the graded slots; the
  three structural tests stand on exact arithmetic + the embedding-degree computation.

Reproduce: `scratchpad/session_2026-08-11/trace_openq_test.sage`.
