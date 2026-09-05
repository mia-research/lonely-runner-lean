# PRE-REGISTRATION v2 (AMENDMENT) — μ₃/GLV frequency-support test

**File:** `PREREG_mu3_glv_frequency_support_v2.md`  **Written:** 2026-08-10, BEFORE any deficit data seen.
**Amends:** `PREREG_mu3_glv_frequency_support_v1.md` (which remains the CANONICAL spec for the primary
statistic, Null-B, power, scope, and falsification — **unchanged** by this amendment).

This v2 changes **nothing** in v1's decision rule. It adds two elements requested after v1 was written:
a **secondary descriptive statistic** and a **forced-diagonal implementation control**. The primary
decision (pooled Stouffer Z on the near-zero co-occurrence count `S` under Null-B, §2/§3/§7/§9 of v1)
stands exactly as in v1. Neither addition can move the primary verdict; both are reported alongside it.

---

## §10 (NEW) — Secondary statistic `S_GLV` (descriptive only, NOT decision-driving)

**Motivation.** The primary `S` targets the deficit's *carrier* — the ~8% near-zero excess (`ρ<τ`).
`S_GLV` asks the complementary question: does μ₃/GLV organization extend BEYOND the near-zero tail into
the bulk/high-tail of the magnitude field? A positive `S` with a flat `S_GLV` ⇒ the organization is a
tail phenomenon; both positive ⇒ the whole magnitude field is μ₃-graded.

**Definition.** Per column `c` and a-rep `a₀`, on the (p−1)/2 ±-reps `r` (fold `r↦min(r,p−r)`, which
absorbs the forced μ₂ so it cannot inflate the ratio):
- `M2(r,c) = |U(a₀,r,c)|²`.
- Group the ±-reps into the (p−1)/6 μ₃-triples `(r, βr, β²r)` (folded). Orbit mean
  `μ_O = ⅓(M2(r)+M2(βr)+M2(β²r))`.
- `S_GLV(a₀,c) = Var_O(μ_O) / Var_r(M2(r,c))`  — the η² fraction of magnitude variance explained by
  μ₃-orbit grouping.

**Why it is NOT the primary.** `Var(M2)` is dominated by the high tail, so `S_GLV` is low-power for the
near-zero-tail effect the deficit is (v1 FLAG F8). It is reported as a distribution over `(a₀,c)` and
compared to its OWN Null-B (permute rep-magnitudes across triples within the column), never as a
threshold verdict. **`S_GLV` must use μ₆/±-reps, not raw μ₃** — a raw-μ₃ partition duplicates every
orbit with its `−b` twin (`M2(b)=M2(−b)` forced, `−1∉⟨β⟩`), fabricating structure.

**Pre-committed reading.** `S_GLV` is descriptive: it annotates a primary positive (tail-only vs
field-wide) and a primary null (is there bulk μ₃-structure the tail-focused `S` would miss?). It carries
its own scoped phrasing and **cannot** by itself license any claim of organization or of closure.

## §11 (NEW) — Forced-diagonal IMPLEMENTATION control (a code self-test, run first)

**Purpose.** Distinct from the statistical plant/negative controls (v1 §4). This is an *implementation*
firing-control: it verifies the runner computes `U` and applies the GLV index maps correctly, using the
one place the algebra is exactly forced.

**The check.** By the verified pullback `U(a,b,c)=U(λa,βb,c)` (A1/A4), `|U|` is EXACTLY constant on the
diagonal orbit `{(a₀,b), (λa₀,βb), (λ²a₀,β²b)}`. So:
```
for random (a₀,b,c):  Var( |U(a₀,b,c)|, |U(λa₀ mod n, βb mod p, c)|, |U(λ²a₀, β²b, c)| )  ==  0
```
**Assertion (pre-committed):** intra-orbit variance `< 1e−6` (float tol on the |U| carve-out) for every
sampled `(a₀,b,c)`. If it is not ≈0, the pullback/index maps in the run loop are wrong — **ABORT the run
and fix the code**; a non-zero result here invalidates every downstream number. This is exactly v1's
FLAG F1 (the forced-zero trap) repurposed: useless as a hypothesis test, ideal as a correctness gate.

**Scope note.** The implementation control requires `λ` (a CM curve). On the non-CM discriminant curve
(v1 §4) there is no `λ`; correctness there is gated instead by a brute-force-vs-FFT agreement check on a
small prime (the runner's `--selftest`).

---

## Run order (v2)
1. `--selftest` on a small prime: brute-force `U` == FFT-path `U` (both curves); §11 implementation
   control on the CM curve (Var≡0). Must pass before any statistic is computed.
2. Per prime in the v1 §6 schedule: primary `S` + Null-B (decision), then `S_GLV` (descriptive), then
   plant / negative / CM-discriminant controls (v1 §4).
3. Report per-prime permutation z, pooled Stouffer Z, and the v1 §9 outcome-table verdict — with the
   §10/§11 additions annotating, never overriding, it.

*Exactness unchanged from v1 §8: exact-int point/index path; float carve-out only in `|U|` magnitudes;
the `ρ<τ` label is monotone and ranked against the INTEGER Null-B permutation. No float decides a verdict.*
