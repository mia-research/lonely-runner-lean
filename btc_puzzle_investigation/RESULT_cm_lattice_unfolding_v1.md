# RESULT — CM lattice-unfolding: the public lift does NOT reveal `(a,b)` (powered bounded null); the amicable second equation is STRUCTURALLY vacuous as a public feature (v1, 2026-08-19)

**Executes** `PREREG_cm_lattice_unfolding_v1.md` (frozen). **Deviations:**
`PREREG_cm_lattice_unfolding_v1_DEVIATIONS.md` (D1 transversal correction — material; D2 common-null
max-T; D3 plant B; D4 #135-only; D5 power rung). This is **Brick B(ii)** of `ROADMAP_REDIRECT_v3.md` —
the single most load-bearing dependency (the conditional d-shadow arsenal is gated on it).
**Scripts:** `cm_lattice_setup_v1.py`, `cm_lattice_unfolding_v1.py`. Runs:
`cm_lattice_unfolding_run_v1_ladder.out` (p~10⁴), `..._powered.out` (p~1.3·10⁵). Exact int/Fraction
signal path. No ECDLP claim; scale-blocked.

---

## 1. The two questions and the answers

Object: `E: y²=x³+7`, `p≡1 mod3`, CM by `Z[ω]`, `E(F_p) ≅ Z[ω]/(π_p−1)`. Feature `Φ = eis([d]G)` is
the public exact-integer Babai lift of the point's `x` against `(π_p)`; target `(a,b) = LATT(d)` is the
private lattice unfolding of `d` (Babai of `d` against `(π_p−1)`, norm `n`); partner feature `Ψ` is `x`
reduced against the amicable `(π_n−1)`.

> **(i) Does the public lift `Φ` carry the private `(a,b)`?** **NO — powered bounded null.** At
> `p≈1.3·10⁵` (`N≈2.2·10⁴` μ₆-transversal orbits, both `p≡1` and `p≡7 mod12`), the mutual information
> `I(Φ_ℓ; (a,b) mod ℓ)` for `ℓ∈{2,3,5,7}` is **below `I_min ≈ 9·10⁻⁴ bits`**, family-wise permutation
> `p = 0.37` (class 1) and `0.76` (class 7) — inside the α=0.001 band. The public single-point lift does
> not reduce `H((a,b) mod ℓ)` beyond the `d↔[d]G` bijection, at scope.

> **(ii) Does the amicable partner supply an independent second equation?** **NO — and this is
> STRUCTURAL, not merely null.** `ARM N` (conditional MI `I(Ψ;(a,b)|Φ)`) is **exactly `0.00000` at
> every ℓ, every rung.** Reason (verified at 6+2 primes): `π_n − 1 = −π_p`, so the partner ideal
> `(π_n−1)` **is** the primary ideal `(π_p)` (differ by the unit −1). `Ψ` reduces `X` against the same
> lattice as `Φ` ⇒ `Ψ` is a deterministic function of `Φ` ⇒ adds exactly zero. **The "two equations
> pin what one leaves circular" lever fails at the public-feature level: the second equation is the
> same equation.** An independent partner constraint would need the partner-curve map, which requires
> `d` (out of the public feature path) — the circularity the arsenal already faces.

---

## 2. Controls — all fired (admissibility met)

| control | result |
|---|---|
| **Frobenius / partner exactness** | `N(π_p−1)=n`, `N(π_n−1)=p` at every rung; `π_n−1=−π_p` (associate) |
| **μ₆-transversal (D1 correction)** | `N=(n−1)/6` exactly; μ₆ lockstep quotiented |
| **μ₆-witness** (spec §3) | full non-transversal set inflates (`p_perm=0.09` at p=2089 / `0.002` smoke) vs transversal null (0.06–0.91) — inflation removed, as pre-committed |
| **positive plant** (inject `a mod ℓ`) | fires to **`ε_min = 1/32`** at `N≈2.2·10⁴` (`1/8` at `N≈1800`) — power confirmed |
| **hard null** (random re-pairings) | false-positive rate **0/30** (need ≤1/30) — permutation null calibrated |
| **power** | `I_min ≈ 8.9·10⁻⁴ bits ≤ 0.01` at the powered rungs (both classes) |
| **disjointness** | `d` never in `Φ`/`Ψ` path; `X` never in `(a,b)` path; different lattices (norm p vs n) |
| **exactness** | int/Fraction throughout; float only in `log` inside MI, ranked vs the null |

**Honest power caveat (D5).** The `p~10⁴` ladder rungs were **under-powered** (`I_min≈0.011 > 0.01`):
5/6 exceed the frozen 0.01-bit bar and are recorded as *insufficient power*, not as a bound. The valid
bounded-null claim rests on the **powered** `p~1.3·10⁵` rungs (`I_min≈9·10⁻⁴`), where both classes are
null. The ladder rungs are consistent (all family-wise `p ≥ 0.06`) but do not by themselves carry the
bound.

---

## 3. Grade and scope

| item | grade |
|---|---|
| ARM P: `I(Φ; (a,b) mod ℓ) < 9·10⁻⁴ bits`, ℓ∈{2,3,5,7}, both mod-12 classes, `p≈1.3·10⁵` | **`[EMPIRICAL — bounded null, powered, scoped]`** |
| ARM N: amicable partner adds exactly 0 (public feature) | **`[VERIFIED-exact + STRUCTURAL]`** — `π_n−1=−π_p` |
| `π_n − 1 = −π_p` (amicable ideal identity) | **`[VERIFIED-exact, 8 primes]`** |

**Scale banner.** Every number is scoped to `p ≤ 1.3·10⁵`, `y²=x³+7`, the μ₆-transversal, these features.
`p = 2²⁵⁶` is ~236 binary orders away. **No claim about the leak's presence, size, or exploitability at
secp.** The `#135` public secp feature is recorded (`eps=0`, `(u,v) mod 2 = (0,0)`); since `d₁₃₅` is
unknown and the channel is a bounded null, there is **no actionable `(a,b)` prediction** — only the
feature values, for the trail.

**In-bounds** per the 2026-08-18 boundary (uniform `d`, number-theoretic key structure, not the PRNG).

---

## 4. What this resolves (the brick)

Brick B(ii) asked whether the public Eisenstein lift reveals the CM-lattice coordinates of `d`, with
the amicable partner as a potential second equation. Both halves are now answered at small-`p` scope:

- **The public single-point lift channel is bounded** (`< 9·10⁻⁴ bits` about `(a,b) mod ℓ`), powered —
  collapsing the "public function of `P` is redundant with `P`" dependency **at this scope**, cleanly,
  with power and scope (not a closure, not a `2²⁵⁶` statement).
- **The amicable second-equation lever is refuted structurally**: `(π_n−1)=(π_p)`, so the partner lift
  is not an independent public feature. This is the durable half — it holds for all `p` (the associate
  identity `π_n−1=−π_p` is exact), independent of scale: the amicable over-determination cannot be
  realized through a public single-point lattice reduction.

**Net:** the conditional d-shadow arsenal's single load-bearing input — a public handle on the scalar
lattice via the lift — does not exist through this channel at scope, and its proposed amicable
de-circularizer is structurally the same equation. A durable redirect, per the brick criterion.

*Grade legend: EMPIRICAL (bounded null, powered) · VERIFIED-exact · STRUCTURAL.*
