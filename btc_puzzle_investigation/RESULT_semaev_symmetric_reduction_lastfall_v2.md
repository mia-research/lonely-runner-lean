# RESULT (AUDIT-CORRECTED) — the elementary-symmetric reduction: coefficient-invariance holds at the reduced FIRST-fall degree; the reduction RAISES the solving degree; solving-degree coefficient-invariance is UNMEASURED (censored). Scoped, NOT a route-A closure.

**Grade:** `[VERIFIED-scope]` on (i) the reduced-system **first-fall** coefficient-invariance (d_ff = 5 for
Semaev AND all 12 symmetric-random draws, both primes, **uncensored**, zero variance) and (ii) the exact
ideal-level correctness of the reduction. `[EMPIRICAL, model scale]` on (via the reliable Gröbner statistic
d_gb, both primes) "the reduction **LOWERS** the Gröbner degree, d_gb 6→2" and "**no** secp-specific
coefficient lever (BLIND, variety-matched, d_gb 2 for Semaev = all 16 random)". **WITHDRAWN:** the earlier
"reduction raises the solving degree" and "coefficient-invariance extends to the last-fall degree" — both
were artifacts of the unreliable/censored Macaulay statistic (see Corrections 1 and 2). Model scale (m=3,
p ∈ {307, 2069}), ZERO secp power. **NOT a route-A closure.**
**Date:** 2026-08-31. **Prereg:** `PREREG_semaev_symmetric_reduction_lastfall_v2.md`.

## ⚠ CORRECTION LOG — this document was audited (isolated adversarial review, 2026-08-31) and 5 defects fixed
The pre-correction version overclaimed. What changed and why:
1. **[WITHDRAWN] "coefficient-invariance extends to the LAST-fall degree."** The reduced `d_LF` was
   **censored** — pinned at Dmax in both runs (26→26, then 34→34). Decisive internal proof it was the
   ceiling, not a measured value: the membership-only ideal ⟨r₀,r₁,r₂⟩ has **d_solv = 3** yet **d_LF = 34**
   — a system solved at degree 3 cannot have a genuine last fall at 34. The "all rungs = 34" agreement was a
   **censoring tie**, not an invariance. → Replaced by the **first-fall** invariance (d_ff = 5, uncensored,
   swept across all 12 draws — the check that was owed and is now run: `scratchpad/symred_dff_sweep.py`).
2. **[FIXED] `d_LF` mis-graded as "the Caminata–Gorla binding solving-degree invariant."** As defined
   ("largest D ≤ Dmax with a fall") it VIOLATES the CG ordering (d_LF = 34 > d_solv = 3 for the membership
   ideal), so it is not the CG last-fall degree. → `d_LF` dropped; only **d_ff** (first fall) and **d_solv**
   (first D where the quotient stabilizes) are used.
3. **[FIXED] The plant firing control (probe iii) was a Dmax-mismatch artifact.** Plant ran at Dmax=38,
   reduced at Dmax=34; `probe_iii_fires` was True only because 38 ≠ 34 (both censored to their own ceilings).
   At matched Dmax it would NOT fire → VOID by the run's own rule. → Power is instead established by **probe
   (i)**: adding Ŝ moves the membership ideal's **d_solv from 3 to > 34** (a real, non-censored move on the
   membership side) and quo 20→2. The plant is discarded.
4. **[FIXED] "measured and NULL at last fall" / "no lever at either first or last fall."** The lever's actual
   locus — the solving degree under symmetrization — is **not measured** (reduced d_solv censored > 34). →
   Restated: first-fall coefficient-invariant; **solving-degree invariance UNMEASURED**; no degree collapse
   observed.
5. **[FIXED] "not a variety-size artifact (robust against it)" + "7.5× smaller".** No theorem says a smaller
   variety ⇒ lower solving degree (it is a heuristic, and the reduced system is exactly the overdetermined
   regime where solving degree decouples from point count). And "7.5×" mixed the **non-distinct** un-reduced
   quo (15) with the **distinct** reduced quo (2); the matched (distinct-saturated) ratio is **6×** (12 vs 2,
   `six_times_check=True`). → Graded as a heuristic ("the size confound predicts the opposite sign, so it does
   not *explain* the increase"), matched ratio 6×, with the reduced-distinct vs un-reduced-non-distinct
   comparison noted.

6. **[CORRECTION 2 — the Macaulay statistic was unreliable; a BLIND d_gb re-measurement reverses "raises
   the degree".]** Prompted by "measure it now, exact, blind" (`PREREG_semaev_symred_solvingdeg_BLIND_v1.md`,
   runner `semaev_symred_dgb_blind_v2.py`), the reduced solving complexity was re-measured with the
   **Gröbner-basis max degree d_gb** (exact, TERMINATES → cannot censor) instead of the Macaulay d_solv.
   Result: the Macaulay d_solv was a **bad statistic** here — it reported ">34" for a system whose true
   **d_gb = 2**. With d_gb: UNREDUCED-x Semaev d_gb = **6** (quo 15) → REDUCED-e Semaev d_gb = **2** (quo 2),
   both primes ⇒ **the reduction LOWERS the Gröbner degree (6→2)** — the generic FGHR benefit (it quotients
   the S₃ ordering redundancy), NOT "raises" it. So correction #5's "reduction is counterproductive / raises
   the solving degree" (itself built on the censored Macaulay d_solv) is **WITHDRAWN**. And a **BLIND**,
   variety-matched coefficient test (Semaev + 16 random-symmetric all forced to the same 2-point variety;
   Semaev shuffled, revealed last): all 17 give d_gb = 2 → **INVARIANT, both primes, no secp-specific
   coefficient lever** — with the honest caveat that at a matched 2-point variety d_gb=2 is near-forced (the
   variety determines the ideal), so this is a weak null.

*The first-fall document (`RESULT_semaev_structure_firstfall_vs_m_v2.md`) was audited too and found SOUND —
its d_ff values are uncensored interior values (4 ≪ 12, 12 < 22), zero variance, both primes.*

*Lesson recorded: the Macaulay d_solv/d_LF read-out did not converge for these small overdetermined systems
and produced two false claims (a censored "invariance" and a censored "raises"); the Gröbner d_gb is the
reliable non-censoring statistic. Use d_ff (interior first-fall) + d_gb (Gröbner), never a Macaulay value
pinned at Dmax.*

---

## Object
The first-fall result located the last place a lever could hide: the solving degree under the FGHR-style
symmetric reduction. This probe builds the exact elementary-symmetric reduction of the m=3 prime-field
Semaev relation system and asks whether it collapses the solving degree, and whether any effect is
secp-specific.

## Construction (exact, correctness-verified — all controls PASS at both primes)
S₄(x₁,x₂,x₃,τ) → Ŝ(e₁,e₂,e₃) via the fundamental theorem (deterministic); factor base V, |V|=6 (two
planted decomposing triples ⇒ reduced variety quo=2); membership via divisibility rem(g, X³−e₁X²+e₂X−e₃)≡0
→ r₀,r₁,r₂. **`reduction_correct`=True** (Ŝ(σ(x))=S₄ exactly), **`six_times_check`=True** (un-reduced-
distinct variety = 6× reduced: 12 = 6×2), **`ideal_equal_GB`=True** (⟨Ŝ,r_i⟩ *equals* the true
distinct-saturated elimination ideal by reduced-Gröbner-basis comparison — ideal-level, not variety proxy).

## What ran, and what it shows (both primes)
**Earned — first-fall coefficient-invariance (uncensored).** In the reduced system, `d_ff = 5` for the true
Semaev coefficients and for **all 12** symmetric-random draws, at p=307 and p=2069, with zero variance
(`symred_dff_sweep.py`; 5 ≪ Dmax=12, genuinely interior). Semaev sits inside the random spread [5,5] ⇒ **no
secp-specific coefficient lever at first-fall** — consistent with, and extending into the reduced
coordinates, the first-fall result's support-forcing.

**Power (corrected).** Probe (i): the Semaev generator is not inert — adding Ŝ to the membership ideal moves
**quo 20→2** and **d_solv 3→>34** (the membership side, d_solv=3, is fully resolved, so this is a real move,
not a censoring artifact). So the statistic can respond to structure; the first-fall invariance is a real
coefficient-forcing, not a dead read-out. (The Dmax-mismatched plant probe is discarded — see correction 3.)

**Solving degree — censored, invariance UNMEASURED.** The reduced solving degree d_solv is **> 34** (not
resolved even at Dmax=34; a Dmax=50 resolution attempt is pending). Whether it is coefficient-invariant is
therefore **not measured** — the earlier "all rungs = 34" was the censoring ceiling. This is the same
compute wall in the reduced coordinates.

**The reduction's structural effect (via the reliable d_gb — supersedes the censored-Macaulay reading).**
The elementary-symmetric reduction **lowers** the Gröbner complexity: UNREDUCED-x Semaev d_gb = 6 (quo 15) →
REDUCED-e Semaev d_gb = 2 (quo 2), both primes (`semaev_symred_dgb_blind_v2.py`). It quotients the S₃
ordering redundancy (≈15 ordered/near-solutions → 2 unordered decomposition points), so the reduced system
is *easier*, not harder — the generic FGHR-style benefit. It also lowers the first-fall (un-reduced d_ff=14 →
reduced d_ff=5). (The earlier "raises the solving degree, d_solv 25→>34" is withdrawn: the >34 was the
non-convergent Macaulay statistic on a system whose true Gröbner degree is 2 — Correction 2.)

**Coefficient effect — BLIND, variety-matched, exact.** With all 17 systems forced to the same 2-point
variety (Semaev + 16 random-symmetric; Semaev shuffled, revealed last), every d_gb = 2 at both primes →
Semaev inside [2,2] → **INVARIANT, no secp-specific coefficient lever**. Honest caveat: at a matched 2-point
variety, d_gb = 2 is near-forced (the variety determines the reduced ideal), so this "no lever" is a *weak*
null — it shows no coefficient creates extra complexity, not that a lever is impossible.

## Verdict (scoped, graded, corrected — d_gb, blind)
At m=3, in the exact elementary-symmetric reduction (measured with the reliable non-censoring Gröbner
statistic d_gb, both primes, blind): the reduction **lowers** the complexity (d_gb 6→2, the generic FGHR
benefit), and there is **no secp-specific coefficient lever** (Semaev = all 16 random = 2, variety-matched,
blind) — a *weak* null at matched variety. First-fall is coefficient-invariant (d_ff=5, uncensored, both
primes). So symmetrization *helps generically* but not secp-specifically; the earlier "measured NULL at last
fall" and "reduction raises the degree" are both withdrawn as artifacts of the unreliable Macaulay statistic.
The genuine open question stays **m≥4** (this is all m=3, and the near-forced matched-variety null is weak).
**Scoped; NOT a route-A closure** (m≥4 open; relation-yield and
factor-base-size out of frame; the solving-degree invariance owed).

## What is NOT settled / owed
- **m≥4** — the genuine open question; all of this is m=3, where the matched-variety d_gb null is weak.
- **Full solving/regularity degree** — d_gb (reduced GB max degree) is the reliable non-censoring
  statistic used here, but it ≤ the F4/F5 solving degree; the exact regularity is not separately resolved
  (the Macaulay read-out was unreliable for these systems).
- **relation-yield**, **factor-base-size** — out of frame.
- **Gates:** `citation-verifier` on Petit–Quisquater + FGHR (before any grade promotes); `compile-diff` if folded.

## Provenance
Exact GF(p) integer Macaulay ranks. p ∈ {307, 2069}, A=0/B=7, |V|=6 (two planted triples), τ frozen (seed
1234+p). Runner `semaev_symmetric_reduction_lastfall_v1.py`; first-fall sweep `scratchpad/symred_dff_sweep.py`;
d_solv resolution `scratchpad/symred_dsolv_resolve.py`; run log `scratchpad/symred_v2c.log`. Isolated
adversarial audit 2026-08-31 (5 defects; this doc corrected to match).
