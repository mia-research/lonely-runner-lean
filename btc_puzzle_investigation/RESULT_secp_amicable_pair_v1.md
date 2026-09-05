# secp256k1 is a Silverman–Stange AMICABLE PAIR — #E(𝔽_p)=N_ord and #E(𝔽_{N_ord})=p

**Date:** 2026-07-21 · **Verification:** `p·P = O` over 𝔽_{N_ord} for 3 independent points, with a
discriminating wrong-candidate that does NOT annihilate. Exact integers. Context: user Directive 3
(amicable bridge / trace conservation `t_N = 2 − t_p`).

> ## ⚠ SCOPE
> This is a **curve-arithmetic (CM) fact** about `y²=x³+7`. It involves **no private key, no d-side /
> (n,k,D) structure, and has NO ECDLP consequence.** It is exact and full-scale (the actual 256-bit
> p, N_ord). Grade: `[PROVED by verification]` (p prime ⇒ `p·P=O` ⟺ `#E(𝔽_N)=p`).

---

## 1. The fact

- `p = 2²⁵⁶−2³²−977` (prime). `N_ord = #E(𝔽_p)` (prime, cofactor 1). Both `≡ 1 mod 3` (E ordinary,
  split in ℤ[ω]).
- **Forward:** `#E(𝔽_p) = N_ord` (secp's group order, cofactor 1 — given).
- **Return (verified here):** for `E: y²=x³+7` reduced mod `N_ord`, **`#E(𝔽_{N_ord}) = p`.**
  Test: `p·P = O` for 3 random points `P∈E(𝔽_{N_ord})`; since `p` is prime this forces `#E(𝔽_N)=p`.
  Control: a different sextic-twist candidate order `N+1−2x` gives `(N+1−2x)·P ≠ O` — the test
  discriminates, so the annihilation is not a small-subgroup artifact.

**⇒ `(p, N_ord)` is an amicable pair (aliquot 2-cycle) for `y²=x³+7`:** `p → N_ord → p`.

---

## 2. The enforcing structure (per the drill: name the symmetry, don't say "chance")

- **CM by ℤ[ω] gives the bridge for free.** `t_p = p+1−N_ord` (129-bit; verified `t_p = x_p + 3y_p`
  from `p = x_p²+3y_p²`). The ideal identity `(π_n) = (π_p − 1)` is the **universal**
  `#E(𝔽_p) = N(Frob−1)` — true for *every* elliptic curve, hence not special to secp. The user's
  `t_N = 2 − t_p` is **correct but forced** by this identity (`p = N−1+t_p ⇒ t_N = N+1−p = 2−t_p`).
- **`t_N` is a genuine CM trace of N.** `N = x²+3y²`, and `t_N = 2−t_p = x − 3y` **exactly** — one of
  N's six sextic-twist traces `{±2x, ±(x+3y), ±(x−3y)}`. So `p` is an *admissible* `#E(𝔽_N)` a priori;
  `π_n = π_p − 1`.
- **The special part = the sextic twist selects the return.** Being an admissible candidate (CM
  bookkeeping) does NOT force the return; the actual curve `y²=x³+7` had to land on the `x−3y` twist.
  It does (§1). **The enforcing group is CM(ℤ[ω]) × the sextic-twist class of `b=7`** — that twist
  class is what makes the 2-cycle close.
- **Calibration (honest magnitude).** Amicable pairs for this CM family have positive density; the
  project's own measurement is `~13/50 ≈ 26%` ([[secp256k1-pure-arithmetic-study-2026-07-11]], thread
  B, S–S Conjecture 40). So secp being amicable is a **~1-in-4 CM event, not an astronomical
  coincidence** — a real exact identity with a named cause, not "generic," and not "miraculous."

---

## 3. Relation to the sextic-sector / conservation ledger

- The "6 field sectors / 3 curve sectors / missing ℤ/2 = the sextic twist" structure the directive
  invokes is **already mapped**: `masked_structure_findings_v34.md` Claim F (bidegree ℤ/2×ℤ/3;
  "field negation exchanges E with its sextic twist"). The twist-as-a-*self-symmetry* mechanism for the
  `p≡7 mod 8` conservation was **killed** in v36 (the reflection lands on the conjugate prime `π̄` — the
  amicable partner — and does not descend to 𝔽_p). This result **confirms the amicable partner is a
  real object** (secp reaches it) but does not revive the killed self-symmetry.
- The open frontier of that thread remains the two v38 lemmas (P1 `N≡μ₂ mod 2`; P2 the χ₂ balance),
  whose proof would convert the 35/35 `p≡7 mod 8` conservation from EMPIRICAL to PROVED — unchanged
  by this finding.

---

## 4. What this does and does not open

**Positive:** secp256k1 sits on a genuine CM aliquot 2-cycle `p ↔ N_ord` — an exact, verified,
full-scale structural fact, with the enforcing cause named (CM + the `b=7` sextic-twist class).
**Bound (no over-reach):** it is a curve-side / CM fact; it carries no private-key (d-side) information
and no ECDLP consequence. Whether the **d-side Dirichlet island lattice** correlates with the sextic
parities across this (now-real) bridge is a *separate* d-side↔curve-side question of the same shape as
the four scoped-null island tests this session — untested here, not claimed either way.

---

## 5. Reproduction
```
# t_p, N=x^2+3y^2, six traces, t_N = x-3y ; pi_n = pi_p - 1 (universal)
# EC over F_{N_ord}: find P on y^2=x^3+7, check p*P == O  -> #E(F_N)=p  (p prime => conclusive)
# discriminator: (N+1-2x)*P != O
```
Exact integers throughout; no float in the arithmetic (sqrt_mod / EC group law mod N_ord).
