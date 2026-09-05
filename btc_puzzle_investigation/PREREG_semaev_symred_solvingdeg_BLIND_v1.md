# PREREG (BLIND) — is the reduced-system SOLVING complexity coefficient-invariant? Exact, non-censoring, Semaev blinded in a shuffled pool

**Status:** FROZEN before any degree is read. Written in direct response to the audit finding that the
prior last-fall claim rested on a CENSORED statistic (d_LF pinned at Dmax). **Date:** 2026-08-31.
**Harness:** `semaev_symmetric_reduction_lastfall_v1.py` defs + `semaev_elimination_v1.py`. **Runner:**
`semaev_symred_solvingdeg_blind_v1.py`. Exact GF(p) integers only; `check_no_float` must pass.

## 0. The two locks this design adds (against the two failures just found)
- **NON-CENSORING statistic (fixes the censoring trap).** Primary statistic = **d_gb = the maximum
  total degree appearing in the reduced degrevlex Gröbner basis** of the reduced system, over GF(p).
  `groebner_basis()` TERMINATES, so d_gb is always a resolved exact integer — it cannot be pinned at a
  ceiling the way the Macaulay d_solv/d_LF were. (Secondary: d_solv via Macaulay at Dmax=40; reported as
  ">40" if censored, and then IGNORED for the decision — a censored value is NEVER read as invariance.)
- **BLIND (fixes analyst steering toward a null).** Semaev is one unlabeled member of a shuffled pool of
  systems; the runner prints the sorted multiset of d_gb values WITHOUT labels first, then reveals
  Semaev's index and value. The decision rule below is applied mechanically to integers.

## 1. Object
For the exact elementary-symmetric reduction of the m=3 prime-field Semaev relation system (|V|=6, two
planted decomposing triples ⇒ reduced variety quo=2; construction + ideal-level correctness already
verified: `reduction_correct`, `six_times_check`=6×, `ideal_equal_GB`=True), is the Gröbner-basis
complexity d_gb of the TRUE Semaev coefficients inside the spread of d_gb over random S_3-symmetric
coefficients on the same support?

## 2. Pool & statistic (frozen)
- Pool = { Semaev-reduced } ∪ { K = 16 symmetric-random-reduced }, all sharing the same e-support and the
  same membership equations r₀,r₁,r₂ (only the P-slot coefficients differ; randoms are uniform NONZERO
  GF(p), seeds `77000+p+j`, j=0..15). Each random is re-planted to vanish at the same decomposition
  (consistency), exactly as the true reduction.
- Statistic d_gb(system) = `int(max(g.total_degree() for g in ideal(system).groebner_basis()))`.
- p ∈ {307, 2069} (must agree for a single verdict).

## 3. Blind protocol (frozen)
1. Build the 17 systems (index 0 = Semaev by construction).
2. Shuffle the 17 by a fixed permutation (seed `31337+p`); record Semaev's shuffled position privately.
3. Compute d_gb for all 17.
4. **Print the sorted multiset of the 17 d_gb values with NO labels** (the blind view).
5. THEN print Semaev's shuffled position, its d_gb, and its rank among the 17.

## 4. Decision rule (pre-committed, integer order statistics)
Let a = d_gb(Semaev), [lo,hi] = [min,max] of the 16 random d_gb.
- **SECP-SPECIFIC LEVER (escalate — the counter-prior target):** a < lo (Semaev's Gröbner complexity
  strictly below every random symmetric system). Surface, do not close; prereg an m=4 confirmation.
- **INVARIANT / no coefficient lever at d_gb (scoped):** lo ≤ a ≤ hi. Report as: the Gröbner complexity
  is coefficient-invariant on this support at m=3. SCOPE CAVEAT stated up front: d_gb (max degree in the
  REDUCED GB) ≤ the solving/regularity degree, so this bounds the coefficient-lever at the Gröbner-degree
  level; it does not by itself prove full solving-degree invariance. It is NOT a route-A closure.
- **ANTI (Semaev harder):** a > hi. Report as-is.
- **Secondary d_solv:** report the multiset at Dmax=40; if all resolve (interior), state whether Semaev
  is in-spread there too; if ANY censors, mark d_solv "insufficient Dmax" and DO NOT infer invariance
  from it. The decision uses d_gb only.

## 5. Scope / power
m=3, model p, |V|=6, K=16. Settles the Gröbner-complexity coefficient question at m=3 (non-censoring,
blind); does NOT settle m≥4, the two other IC cost factors, or the full solving/regularity degree beyond
the d_gb bound. No grade above `[VERIFIED-scope, model scale]`. A blind INVARIANT result is a scoped
null, still NOT an avenue closure; a blind a<lo is a live lever to escalate.

## 6. Exactness / fence
d_gb and d_solv are exact integers from GF(p) Gröbner / Macaulay computations; no float anywhere. The
PRNG/generation boundary is untouched.
