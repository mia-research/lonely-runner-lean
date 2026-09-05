# RESULT — the cubic coherence P18 is REFUTED as the mechanism of the N7 sub-Rayleigh deficit; N7 is SHARPENED (the deficit is a c≠0 phenomenon), not closed

**Date 2026-08-17/18.** Executes `PREREG_subrayleigh_cubic_coherence_v1.md` (FROZEN, SHA-256
`fbd8616e0643c83fb6671461e693078f953f0e8e1268ef313b2047f7cb0bef87`). Deviations:
`PREREG_subrayleigh_cubic_coherence_v1_DEVIATIONS.md` (D1 CAL-OVER power-table → O2; D2 P-COH
over-excludes; D3 importance-reweight fallback). Scripts (this folder): `signal_path_v1.py` (exact int,
`check_no_float` PASS), `run_v1.py`, `harness_v1.py`. Tests intersection **α** of
`ANALYSIS_intersection_leads_v1.md`. **Model scale only** (E: y²=x³+7, p ∈ [151,12043]); **nothing
transfers to p≈2²⁵⁶** — absolute, per the frozen banner. No ECDLP/extraction/security claim.

**Grade:** α-refutation `[VERIFIED — analytic (F1) + empirical secondary, model scale]`; the slice
super-Rayleigh `[EMPIRICAL — 30 primes, consistently signed, pooled-significant, modest per-prime]`; N7
itself **remains OPEN**, now sharpened.

---

## The question and the answer

**α asked:** is the persistent N7 sub-Rayleigh L1 deficit (`mean|U|` below a matched Hermitian null,
Z=−71.8, 30/30, model-range persistent) the L1 signature of the PROVED cubic phase coherence
`Σ_b χ₂(b) T(a₀,b)³ = τ·(n²−O(n))` (P18)?

**Answer: NO — refuted, on two independent legs, one analytic and decisive, one empirical and confirming.
N7 stays open; the refutation SHARPENS where it lives.**

### Leg 1 — F1 (analytic, from the pre-registration; decisive)
The coherence lives **entirely on the c=0 slice** (`T=U(·,c=0)`; off c=0 the collinear zero-sum triples
dephase). The c=0 slice is `p` of the `p²` frequencies and carries ~`1/p` of the global L1 mass, so its
contribution to the **global** deficit fraction is bounded by `(slice deficit)/p` — at p=2089 that ceiling
is `~1e-5` vs the global `~1e-3`, and it **falls as 1/p while the global deficit is persistent**. The
cubic coherence can account for **at most ~1–2% of the global N7 deficit, a share that vanishes with p.**
This forecloses the global-DISSOLVE hypothesis by algebra, before any data. (The other known coherent
structure, the M4/Δ=0 quadruple route, was already refuted at Z=+0.95.)

### Leg 2 — the c=0 slice carries NO sub-Rayleigh deficit; it is SUPER-Rayleigh (empirical, confirming)
The instrument was validated to **reproduce the established N7 deficit globally**: `D_global = +0.13% /
+0.098% / +0.085%` at p=349/577/1093 (sub-Rayleigh, matching the known 0.06–0.10%). On the **same curves,
the c=0 slice flips sign:** `D_slice = −2.68% / −1.62% / −0.52%` — the character's slice magnitudes are
**more uniform than the null**, not less. Across the full 30-prime schedule the slice deficit is **24/30
negative** (super-Rayleigh; sign-test p≈7e-4), pooled Stouffer `≈ −5.6` over the large primes, though
**modest per prime** (`|z_slice| ≤ 3.3`) and arithmetically scattered — **not** the persistent −51σ
object the global deficit is. Mechanism of the super-Rayleigh: the slice is Weil-bounded (`|T(b)| ≤ ~4√p`),
so it lacks the heavy Rayleigh tail → lower CV → higher L1. **There is no sub-Rayleigh slice deficit for
the coherence to explain; if anything the slice is the opposite.**

**Both legs agree: P18 is not the source of N7.** (The coherence-matched primary `Z_B` came out `−4.20`
— character super-Rayleigh even vs the coherence-matched null, the same direction — but it is **INVALID as
a verdict** per outcome O2: CAL-OVER underran the spec's +4 power bar because §7's power table was ~5×
optimistic, D1. The verdict rests on Leg 1 (analytic) + Leg 2 (the clean `D_slice` secondary), not on Z_B.)

---

## Instrument integrity (what makes the above trustworthy)
- **Exactness:** signal path exact integer (`check_no_float` PASS); slice-L2 anchor `Σ|T(b)|²=p(n−2)−1`
  and global anchor `Σ|U|²=p²(n−1)` hold to `rel ≤ 1.3e-15` at all 30 primes.
- **P18 present (P-DIR):** `|C_char|/(√p·n²) ∈ [0.86,1.04]`, correct Gauss-sum axis (real for p≡1 mod 4,
  imaginary for p≡3), **30/30**. (The parity rotation of the coherence between Re/Im is the M28 lemma.)
- **N7 reproduced globally:** `D_global` in the established 0.06–0.13% band (validates the transform +
  null against the known object).
- **CAL-UNDER PASS** (pooled +1.38 ∈ [−3,3]); **CAL-OVER** fires monotonically for a calibrated +1% plant
  (reaching +4 only at p≳7600 — the D1 power-table deviation, not over-matching).

---

## Positive contribution — N7 is SHARPENED, not closed (anti-suppression, per spec)

This is a **mechanism refutation, not a closure of N7** (the anomaly-drill "refuting a mechanism ≠
refuting the claim"). What it buys:

1. **The N7 deficit is a c≠0 phenomenon.** The x-only (c=0) slice is super-Rayleigh; the persistent
   sub-Rayleigh deficit therefore lives in the **c≠0 directions — the y-coordinate / χ₂(y)-cover
   structure.** This is consistent with N7 living on the DLP character over the cover (Thread 1 /
   `A_new`), not on the bare x-coordinate. A concrete, decidable localization the deficit did not have.
2. **A new characterized object:** the c=0 slice is a **super-Rayleigh, Weil-bounded** magnitude set
   (lower CV than random), the opposite tail behavior from the global object — worth its own line.
3. **Named next probes** (each its own prereg): (i) **MC-HP separation** — is the slice super-Rayleigh
   coherence-specific or Weil-generic? (does a phase-permuted character, coherence destroyed but value
   multiset kept, also give super-Rayleigh slice?); (ii) **the c≠0 localization of N7** — repeat the N7
   deficit statistic restricted to c≠0 strata / the χ₂(y)-cover, to confirm the deficit concentrates
   there; (iii) tighten the slice statistic's power (the modest per-prime `|z_slice|` wants a larger
   ensemble or an analytic conditional-variance model).

---

## Scope / what this does NOT say
- It does **not** close N7. The deficit is real, persistent, and now localized to c≠0 — **open**.
- It does **not** transfer to secp (model scale, p≤12043, absolute).
- It does **not** refute P18 or M28 (both hold — P-DIR confirms P18 at 30/30); it refutes only the
  *claim that P18 sources N7*.
- The coherence-matched primary `Z_B` is not a verdict (O2 / D1); do not cite it as one.

**Net for the intersection map:** α (`ANALYSIS_intersection_leads_v1.md`) is **tested and refuted as a
mechanism** — the cubic spine (P18→α) does not explain N7. The live residue moves to the **c≠0 / χ₂(y)-cover
localization of N7**, which rejoins Thread 1 (`A_new` / `V(a)`), where N7's neighbors (the twist-orbit
forced landscape, sub-Weil reduction) already live. The next cheap probe is the MC-HP separation.
