# Is `a ↦ θ_a` structured? — the free angle, measured directly

**Date:** 2026-07-30. Scripts: `theta_structure_scan_v1.py`, OOS pass in scratchpad.
**Grade: `[EXPLORATORY — EMPIRICAL, scoped, OOS retested]`** + one **derivation** (§1).
⚠ Same user-authorised gate relaxation — **no `experiment-designer` prereg; no number here may
move a grade.** Executes the record's own ranked items **3′ and 4′**
(`SYNTHESIS_..._ADDENDUM_1_v1.md` §3.3/§4), never previously run.

---

## 1. ★★ A DERIVATION, not a measurement: `V₂ = V₁² + 2p` is FORCED by the 120° law

The record carries `V₂ = V₁² ± 2p` as **`[VERIFIED — exact]` at 8–10 primes, NOT derived**, and
`SYNTHESIS_curve_structure_and_new_directions_v1.md` shows `S_y ≤ 2` (hence the `2√p` cap) follows
from it by elementary algebra — leaving *"prove one exact identity"* as the open item.

**It follows from the 120° configuration in four lines.** With
`α₁=α, α₂=αζ₃, α₃=−ᾱ, α₄=−ᾱζ̄₃`, `α=√p·e^{iθ}` (the configuration the 120° law asserts, and which
is closed under the proved `α↦−ᾱ`):

- `1+ζ₃ = e^{iπ/3}` (modulus **1**) ⇒ `p₁ = 2i·Im(α(1+ζ₃)) = 2i√p·sin(θ+60°)`
- `1+ζ₃² = e^{−iπ/3}` ⇒ `p₂ = 2·Re(α²(1+ζ₃²)) = 2p·cos(2θ−60°)`
- put `φ = θ+60°`: `2θ−60° = 2φ−180°`, so `p₂ = −2p·cos2φ = 2p(2sin²φ − 1) = 4p·sin²φ − 2p`
- `p₁² = −4p·sin²φ` ⇒ **`p₂ = −p₁² − 2p`**, i.e. **`V₂ = V₁² + 2p`** ∎

**Consequences:**
1. **Two open items collapse into one.** The identity is not an independent fact to be proved — it is
   a *corollary* of the 120° law. The cap chain is now `120° ⇒ V₂=V₁²+2p ⇒ S_y≤2 ⇒ |V|≤2√p`, and the
   single remaining target is the one already identified: the **Kronecker/Stickelberger ideal route**
   to 120°. `[MINE — derived this session, algebra only; UNVERIFIED against an independent V₂ computation]`
2. **Extension fields cannot resolve `θ_a`.** `p₂` is a function of `p₁` alone, and the residual
   ambiguity `φ ↔ 180°−φ` leaves *both* invariant. Resolving `θ_a` requires `p₃`, i.e. `E(F_{p³})`,
   `O(p³)` — which is why `n1_twisted_eigenvalues_v1.sage` (it goes to `k=4`) only runs at tiny `p`.
   **So the object `V` actually determines is the FOLDED angle `θ̃(a) = arcsin(u(a))`,** where
   `u = V/(2i√p) = sin(θ_a+60°)`. That is what is measured below, and it needs no extension field.

**★ Why a folded angle is still worth measuring — the point of the whole probe.** The forced
identities pin the **linear and quadratic** moments of `V`
(`Σ_a V(a)V̄(a+b) = n(nδ_b−1)`, curve-independent; `V₂=V₁²+2p`, now derived). They constrain
**nothing** about `arcsin(V)`. Arrangement statistics of the angle sequence are **not forced** and
have never been measured.

## 2. Controls (all pass)

| control | result |
|---|---|
| `V` purely imaginary | `max|Re V| ≤ 6.6e−14`, all primes |
| cap `|u| ≤ 1` (⟺ `|V| ≤ 2√p`) | **True**, all primes; `max|u|` = 0.960→0.997 |
| `E[u²]` (record: **forced** = 1/4) | 0.2396–0.2600 across 8 primes ✓ |
| `E[u⁴]` (record: SU(2)=**1/8**, torus/CM=3/8) | 0.1163–0.1336 ✓ — reproduces the monodromy result **independently** |

The last two matter: `u` here is built from `V` alone, with no extension fields and no eigenvalue
solver, yet it reproduces two numbers the record obtained by other routes. The framework is sound.

## 3. Statistics — both NULL

**A · angle-increment autocorrelation** `Δ(a) = θ̃(a+1) − θ̃(a)`, `max|ρ(l)|`, `l ≤ 12`:

| p | 823 | 1303 | 1831 | 2251 | 2731 |
|---|---|---|---|---|---|
| data | 0.5050 | 0.5051 | 0.5077 | 0.4966 | 0.5061 |
| null mean | 0.5064 | 0.4978 | 0.5058 | 0.4947 | 0.4979 |
| ge / 20 | 11 | 8 | 9 | 10 | 7 |

`|ρ(1)| ≈ 0.5` at every prime **in both data and null** — the forced differencing artifact
(`ρ(1) = −½` for increments of any iid sequence), not a finding. **Clean null**; `ge` uniform.

**B · multiplicativity resultant** (`u(a)u(b)/u(ab)`; a character would give 1, generic `≈ 1/√S`):
in-sample `ge/20` = 15, 10, 8, 16, **0** — the last at **p=2731**, the same prime that popped in the
chirp scan.

**Retested, and it died twice over:**
- **OOS, 12 fresh primes** (1051…4831), 60 arrangement nulls each: **min perm-p = 0.082**
  (Bonferroni 0.0042), mean 0.572, **0 of 12 below 0.05.**
- **The in-sample hit did not reproduce at its own prime.** Re-run at `R=60`: `B` fell
  0.0335 → 0.0170, perm-p **0.295**. ⚠ **Instrument note:** `stat_B` samples `(a,b)` pairs randomly,
  and its sampling noise is comparable to the effect — the "hit" was a draw of the *statistic*, not
  of the data. Any future use of this statistic must fix the pair sample across data and null.

## 4. Scope

- **NULL** for angle-increment autocorrelation and multiplicativity, 5 in-sample + 12 OOS primes,
  against an arrangement null that preserves the forced `μ₃`+odd symmetry **and** the `|V|` multiset.
  A bounded magnitude on *arrangement* structure in the folded angle. **Not a closure.**
- **★ STRUCTURALLY UNTESTED — angle SPACINGS and every order statistic.** The arrangement null
  preserves the `|V|` multiset exactly, so it has **zero power** against any statistic depending only
  on the multiset — spacings, `Δ₃`, `Σ²`, and the whole Katz–Sarnak family. **This is the same gap
  the tail pass found for `|V|`** (`RESULT_phase_family_and_tail_v1.md` §3b), and it is now confirmed
  on a second object. **Building a cap-respecting, marginal-varying null is the prerequisite for
  items 3′(1) and 4′** — they cannot be run until it exists.
- **Untested:** the unfolded `θ_a` (needs `p₃`, small `p` only, where `n1_twisted_eigenvalues_v1.sage`
  already runs); ideal factorization of the `α_i` (the third Stickelberger target); `j≠0` control.
