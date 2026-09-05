# LENS NOTE — Rate-function / Fisher-info formalism on the eigenvalue manifold (v1)

**Mode:** INVESTIGATION (lens-open). **Object:** Frontier #26 (uniform $\alpha_2/\alpha_1 = \zeta_3$).
**Date:** 2026-07-30. **Status:** conjectural framing of a rigorous core; nothing here is a
proof. All lens-driven claims are tagged `[LENS-CONJECTURE]`; rigorous facts are tagged
`[PROVED]` / `[MEASURED]` with their source.

This note lives in `.zcode/notes/` (my working area), NOT in the project tree. It is private
lens-led investigation; any artifact for the project would be rewritten in purist register.

---

## 1. The eigenvalue-configuration manifold

`[PROVED]` The four Frobenius eigenvalues of $H^1_c(E, L_{\chi_2(y)}\otimes L_{\chi_a})$ satisfy
$|\alpha_i|=\sqrt p$ (purity; Kohel–Shparlinski / Deligne Weil II 3.2.3(2)) and the multiset
is closed under $\alpha\mapsto -\bar\alpha$ (`RESULT_n1_phase_cap_v1.md`).

**Reduction to two phases.** Write $\alpha_1 = \sqrt p\, e^{i\theta_1}$,
$\alpha_2 = \sqrt p\, e^{i\theta_2}$. The closure $\{-\bar\alpha_i\}$ forces the other two
eigenvalues; the configuration is determined by $(\theta_1,\theta_2)\in\mathbb{T}^2$. Change
coordinates to the **common angle** $\theta = \tfrac12(\theta_1+\theta_2)$ and the **relative
angle** $\varphi = \theta_2 - \theta_1$. So $\mathcal{M}_0 \cong \mathbb{T}^2 = \mathbb{T}_\theta
\times \mathbb{T}_\varphi$.

## 2. The empirical measure under monodromy

Varying $a\in(\mathbb{Z}/n)^\times$ transports the configuration around $\mathcal{M}_0$ via
geometric monodromy $G_{\text{geom}}$. The empirical measure $\mu_p$ on $\mathcal{M}_0$ has
two marginals, both measured:

- **$\theta$-marginal** `[MEASURED]`: equidistributes to the Sato–Tate law
  ($E[u^4]=1/8$ SU(2), pooled dev $+0.00008$ over 12 primes, `RESULT_twist_orbit_monodromy_v1.md`).
  Maximum-entropy distribution on the eigenvalue circle subject to $|\alpha_i|=\sqrt p$.
- **$\varphi$-marginal** `[MEASURED]`: a $\delta$ at $\varphi = 2\pi/3$ (the 120° law, exact
  at 22 primes, `RESULT_n1_120deg_exact_v1.md`; verified to $9.5\times 10^{-40}$ at 357
  classes, `RESULT_n1_v_sign_mechanism_v1.md`).

## 3. The rate function (Sanov/Varadhan reading)

`[LENS-CONJECTURE]` The empirical measure $\mu_p$ satisfies an LDP with rate function
$I:\mathcal{M}_0\to[0,\infty]$:

$$I(\theta,\varphi) = \begin{cases} I_{\text{ST}}(\theta) & \text{if } \varphi = 2\pi/3 \\ +\infty & \text{if } \varphi \ne 2\pi/3 \end{cases}$$

where $I_{\text{ST}}$ is the Sato–Tate rate function on $\theta$ (the Cramér transform of
the semicircle). The $+\infty$ off the locus is the rate-function statement of "the 120°
lock is absolute" — configurations off $\varphi=2\pi/3$ are not rare, they are absent.

## 4. Fisher information (the core lens claim)

`[LENS-CONJECTURE]` Fisher information is the Hessian of $I$ at its zero-set:

$$\mathcal{I}_{\theta\theta} = \partial_\theta^2 I_{\text{ST}} < \infty \quad\text{(Sato–Tate is smooth)}, \qquad \mathcal{I}_{\varphi\varphi} = +\infty \quad\text{(delta-supported)}.$$

**The lens claim, precisely:** the relative-angle Fisher information is *infinite* because
the locus is delta-supported, and a delta-supported locus is, by definition, a sharp
(non-degenerate → infinite-curvature) minimum of the rate function.

**`[LENS-CONJECTURE]` Consequence (the "why"):** finite-$\mathcal{I}$ structure cannot be
fixed under monodromy transport — it gets smeared (equilibrates to max-entropy). Only
infinite-$\mathcal{I}$ structure survives. This *explains* the datum in
`ANALYSIS_n1_cap_anew_channel_kronecker_route_v1.md §2`: *absolute rigidity destroyed
($\theta$ has finite $\mathcal{I}$, gets smeared to Sato–Tate); relative rigidity survives
($\varphi$ has infinite $\mathcal{I}$, cannot be smeared).* The datum is already proved; the
lens supplies the reason in terms of Fisher information.

## 5. The monodromy-stabilizer translation

`[LENS-CONJECTURE]` "Monodromy preserves $\varphi = 2\pi/3$" ⟺ "the stabilizer of the
$\zeta_3$-locus in $G_{\text{geom}}$ is the whole group." The Fisher-info reading predicts
this stabilizer is non-trivial *because* the locus is a sharp rate-function minimum — and
predicts that any mode with finite Fisher info has a *proper*-subgroup stabilizer (would
drift under transport). **`[LENS-CONJECTURE]` Checkable:** if any mode is fixed under
monodromy, its Fisher info should be (formally) infinite; finite-$\mathcal{I}$ modes should
show drift. The $\theta$-direction (finite $\mathcal{I}$) does drift (Sato–Tate); the
$\varphi$-direction (infinite $\mathcal{I}$) does not (the 120° law). Consistent so far.

## 6. Testable predictions

### Prediction A — the $\theta$-moment curve is fully SU(2). `[UNRUN]`

If $I_{\text{ST}}$ is the max-entropy (Sato–Tate) rate function, ALL even moments follow
SU(2)'s moment curve, not just $E[u^4]$:

| moment | SU(2) | torus/CM | status |
|---|---|---|---|
| $E[u^2]$ | 1/4 | 1/2 | `[FORCED]` (instrument) |
| $E[u^4]$ | 1/8 = 0.125 | 3/8 = 0.375 | `[MEASURED]` 12 primes, dev $+0.00008$ |
| $E[u^6]$ | **5/64 = 0.078125** | **5/16 = 0.3125** | **`[UNRUN]` — formula in prereg, never implemented** |
| $E[u^8]$ | 7/128 = 0.0547 | 7/32 = 0.2188 | `[UNRUN]` — not even listed |

**This is the sharpest test of the rate-function picture.** $E[u^4]$ alone cannot distinguish
"max-entropy rate function" from "a rate function that happens to match at the 4th moment";
$E[u^6]$ and $E[u^8]$ test the *full curve*. If the lens picture is right, they match SU(2).
If they match torus/CM, the rate function is NOT max-entropy and the lens picture is wrong
on $\theta$ (while still possibly right on $\varphi$).

### Prediction B — product structure of the joint measure. `[UNRUN, STRUCTURALLY HARD]`

`[LENS-CONJECTURE]` The two coordinates decouple: $\mu_p(\theta,\varphi) =
\mu_p^{(\theta)}(\theta)\cdot\delta(\varphi - 2\pi/3)$. Knowing $\theta$ tells you nothing
about $\varphi$ (it's always $\omega$). **Honest limit** (`RESULT_theta_structure_v1.md`):
resolving $\theta_a$ requires $E(\mathbb{F}_{p^3})$ ($O(p^3)$); the folded-angle reduction
leaves a $\varphi \leftrightarrow \pi - \varphi$ ambiguity. **Prediction B is not checkable
with existing $V$-only instruments.** Noted as a structural limit, not pursued here.

## 7. What this note does NOT do (honest)

- It does **not** identify $G_{\text{geom}}$. That is Frontier #28, research-grade, open.
- It does **not** prove uniformity of the 120° law. The rate-function reading is a
  *conjectural mechanism*; the 22-prime exact-at-cells result stands on its own.
- It does **not** link the bridge $\mu_3$ to the eigenvalue $\mu_3$ — that is a separate
  `[LENS-CONJECTURE]` not developed here.
- The Fisher-info reading is **a director of attention**, per Trent's rule. It points the
  proof at monodromy-stabilizer theory; it does not substitute for identifying $G_{\text{geom}}$.

## 8. The move this note motivates

**Measure $E[u^6]$ on the same 12 primes** (`RESULT_twist_orbit_monodromy_v1.md`'s OOS
stratum-S set), using the exact-integer signal path (no float), and compare to $5/64$.
This is a direct test of Prediction A. The formula exists in the prereg signal-path
description (`$E[u^6]$ via $n\sum_{j_1,j_2}R(j_1)R(j_2)R(-j_1-j_2)$`) but was never
implemented. Preregistered separately in `PREREG_Eu6_v1.md`.
