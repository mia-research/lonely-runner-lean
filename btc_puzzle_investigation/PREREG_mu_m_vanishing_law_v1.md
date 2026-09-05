# PREREG — the `μ_m` vanishing law: a `p`-rank formula for `w^m = f(x)` at `p ≡ −1 (mod m)`

**Written 2026-08-02, BEFORE any script for this question exists and before any `p`-rank of a
`m ≠ 4` cover has been computed in this session.** Governing: session rules 1–5,
`btc_puzzle_investigation/CLAUDE.md`, root `CLAUDE.md` §2/§3.

**Pure curve arithmetic. No key, no `(n,k,D)` decomposition, no target, no `d`-side feature. No
leakage or ECDLP claim follows from any outcome.**

---

## 0. Why — this is an out-of-sample test of the reviewed derivation, not a new hunt

`RESULT_anew_supersingularity_step3_gap_and_cartier_route_v2.md` §3 (independently reviewed, clean)
shows `𝒞` vanishes on the new part of `w⁴ = f`, `deg f = 3`, at `p ≡ 3 mod 4`. The *mechanism* is
narrow: `𝒞` pairs the `μ_m`-eigenspaces `b ↔ m−b`, and the pair `{1,3}` vanishes only because
`dim V₁ = ⌊3/4⌋ = 0`.

That mechanism makes a **prediction outside the family it was derived on**, which is the strongest
available test of it. If the mechanism is right the prediction holds; if the prediction fails, the
derivation is wrong in a way the `m = 4` data could never reveal.

---

## 1. Objects (rule 5)

| symbol | definition |
|---|---|
| `m, d` | integers `≥ 2`, `gcd(m,d) = 1` |
| `p` | prime, `p ∤ m`, `p > d`. **MAIN arm: `p ≡ −1 (mod m)`.** CONTROL arm: `p ≢ ±1 (mod m)` |
| `f` | separable, `deg f = d` exactly, in `F_p[x]` |
| `C` | smooth projective model of `w^m = f(x)`; `gcd(m,d)=1` ⇒ `∞` totally ramified ⇒ genus `g = (m−1)(d−1)/2` |
| `V_b` | the `μ_m`-eigenspace of `H⁰(C,Ω¹)` spanned by `x^a dx / w^b`, `0 ≤ a < ⌊bd/m⌋`; so `dim V_b = ⌊bd/m⌋` |
| `𝒞` | Cartier operator; `𝒞(V_b) ⊆ V_{b·p⁻¹ mod m}`, which at `p ≡ −1` is `V_{m−b}` |
| **`p`-rank** | the stable rank of `𝒞` on `H⁰(C,Ω¹)` — equivalently the rank of `𝒞^N` for `N ≫ 0` |
| **`S(m,d)`** | `:= Σ_{b=1}^{m−1} min( ⌊bd/m⌋ , ⌊(m−b)d/m⌋ )` |

`S` counts each unordered pair `{b, m−b}` twice (contributing `2·min`) and the self-paired
`b = m/2` (present only for `m` even) once.

## 2. Hypotheses

- **P1 — the BOUND (should be provable).** At `p ≡ −1 (mod m)`: **`p`-rank`(Jac C) ≤ S(m,d)`**.
  Reason: on a pair `{b, c=m−b}`, `𝒞: V_b → V_c` and `𝒞: V_c → V_b`, so the stable rank on
  `V_b ⊕ V_c` is at most `2·min(dim V_b, dim V_c)`; and `≤ dim V_{m/2}` on the self-paired part.
  **Falsifier: any single `(p,m,d,f)` with `p`-rank `> S`.** That refutes the pairing mechanism, and
  with it the reviewed derivation's Step 3′.
- **P2 — GENERIC EQUALITY.** For a majority of `f`, `p`-rank `= S(m,d)`.
  **This is a rate, not a law**; a shortfall for particular `f` is expected and is not a falsifier.
- **P3 — the specific `m = 5` claim of `RESULT_anew_superspecial_consequences_v1.md` §3.** At
  `m = 5, d = 3, p ≡ 4 (mod 5)` (genus 4): the `{1,4}` piece is supersingular (`dim V₁ = 0`) while the
  `{2,3}` piece (`dim V₂ = dim V₃ = 1`) is **generically ordinary**, giving `S = 2`.
  **⇒ the new part is NOT uniformly supersingular for `m = 5`** — unlike `m = 4`.

Pre-computed predictions (from `S`, before any curve is examined):

| `(m,d)` | `dim V_b`, `b=1…m−1` | genus | **predicted `p`-rank `S`** |
|---|---|---|---|
| (4,3) | 0,1,2 | 3 | **1** |
| (5,3) | 0,1,1,2 | 4 | **2** |
| (7,3) | 0,0,1,1,2,2 | 6 | **2** |
| (3,4) | 1,2 | 3 | **2** |
| (5,4) | 0,1,2,3 | 6 | **2** |
| (3,5) | 1,3 | 4 | **2** |
| (4,5) | 1,2,3 | 6 | **4** |
| (8,3) | 0,0,1,1,1,2,2 | 7 | **3** |

`(4,3) → S = 1` is the consistency anchor: it must reproduce "new part `p`-rank 0, `E` generically
ordinary".

## 3. Statistic and procedure

Per `(p,m,d,f)`: build the graded Cartier matrix (the `m = 4` routine of
`anew_m_support_v2.sage` generalized to arbitrary `m`, with the same exponent construction
`k_b` least `≥0` with `p k_b ≡ −b (mod m)`, `t_b = (b + p k_b)/m`); report **stable rank** of `𝒞` and
the per-pair stable ranks. Compare to `S(m,d)`.

**Exactness:** all arithmetic over `GF(p)` and `ZZ`. No float in any readout.

## 4. Controls — each must be able to fire

| id | control | pass condition | if it fails |
|---|---|---|---|
| **C1 — cross-instrument** | `p`-rank from the Cartier stable rank vs `p`-rank from **point counts**: build `L_C(T)` from `#C(F_{p^n})`, `n = 1…g`, and read the Newton polygon. Restricted to `g ≤ 4` and `p^g ≤ 3·10⁵` for cost. | agreement at **every** row in scope | one instrument is wrong ⇒ **VOID** until resolved |
| **C2 — FIRING control, `p ≢ ±1 (mod m)`** | At such `p` the Cartier pairing is `b ↦ b·p⁻¹`, **not** `b ↦ m−b`, so `S` is derived from the wrong pairing and should **mispredict**. | `S` must **fail** to equal the measured `p`-rank on **≥1/3** of rows | if `S` predicts correctly there too, `S` is not testing the pairing mechanism at all ⇒ the MAIN-arm agreement is **uninformative ⇒ VOID** |
| **C3 — spread** | The sampled `(m,d)` must produce **≥3 distinct values of `S`** and at least one with `S = 0`-pair structure (`min = 0`) and one with all `min > 0`. | both | a single-valued prediction cannot be tested ⇒ widen before running |
| **C4 — anchor** | `(m,d) = (4,3)` at `p ≡ 3 mod 4` must reproduce `p`-rank `= 1` **and** new-part stable rank `0`. | both | contradicts an already-reviewed result ⇒ **VOID-and-investigate** |

**Power, pre-committed.** P1 is a **bound**; a null (no violation found) is reported as *"no violation
of `p`-rank `≤ S` in `N` rows across the sampled `(m,d,p)`"* with `N` stated — never as "P1 is true".
P2 is a **rate** and is reported as a fraction with its denominator, per `(m,d)`.

## 5. Permitted conclusions

| outcome | permitted | forbidden |
|---|---|---|
| no P1 violation, C2 fires | *"`p`-rank `≤ S(m,d)` holds in all `N` sampled rows; the Cartier pairing mechanism survives out-of-sample at `m ∈ {3,5,7,8}`, i.e. outside the family it was derived on."* | *"P1 is proved"* — the bound argument is sketched in §2 and has **not** been written as a proof or reviewed |
| a P1 violation | **the reviewed derivation's pairing mechanism is REFUTED**; name the row; re-open Step 3′ | any attempt to rescue by adjusting `S` after seeing the row |
| P2 equality at a measured rate | report the rate with denominator, per `(m,d)` | calling it a law |
| **P3 confirmed** (`m=5` new part not uniformly supersingular) | *"the `μ_m` construction does **not** always yield a uniformly supersingular new part; at `m = 5, d = 3` the `{2,3}` isotypic piece is generically ordinary."* **A structural contrast with `m = 4`, [VERIFIED-INSTANCE at the sampled primes].** | any ECDLP or hardness reading; §6 |
| P3 refuted | report it; the `m=4` vanishing is then less special than §3 claimed | — |
| C2 does not fire | **VOID** | reporting MAIN-arm agreement as support |

## 6. Scope — stated before the run

- This is **curve arithmetic about a cover family**. It says nothing about secp, nothing about the
  `a ≠ 0` uniformity gap, nothing about any `d`-side object, and **nothing about ECDLP hardness in
  either direction**. In particular, if P3 confirms, *"the `m=5` new part is not uniformly easy"* is a
  statement about `p`-rank strata, **not** a claim that any discrete log is hard — that inference is
  explicitly forbidden here and would need its own object, class, power and scope.
- Nothing reaches `p = 2²⁵⁶−2³²−977`. The derivation is scale-free; this run is not.
- N4 / Route 3 is **untouched** by any outcome.

*Frozen at first script execution. Deviations → `PREREG_mu_m_vanishing_law_v1_DEVIATIONS.md`.*
