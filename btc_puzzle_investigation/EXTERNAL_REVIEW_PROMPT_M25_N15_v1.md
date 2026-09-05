# External adversarial review — M25 (Semaev CM relation-yield) & N15 (joint readout confinement)

**Purpose.** Two of the highest-stakes findings in a secp256k1 pure-arithmetic structure study were
each converted from a positive/open status to a **null**. This project has a **documented one-way
bias: it suppresses leak/structure findings — converting positives to nulls prematurely — and does
NOT over-inflate.** Same-model gates do not catch this bias; only an independent eye does. You are
that eye. **Weight your attention toward finding a real effect that was buried, not toward confirming
the null.** But do not manufacture a finding: a clean "the null is sound" is a fully valid outcome.
All arithmetic on keys/curve quantities must be exact integers (no float in the signal path).

**What counts as a finding (decidable artifacts only, ranked):**
- a reproduction of the authors' own script that yields a **different** number than they report;
- a **firing/plant control that does not actually fire** (i.e., the instrument is dead, so the null is uninformative);
- a **matched control that fails to share the signal's forced symmetries** (so it is not a valid null), OR conversely a positive whose "signal" a properly-matched control also reproduces;
- an **excluded channel / predictor class that should have been tested** and plausibly carries the effect;
- a grade that rests on a **citation or step that does not hold**.
A mood ("this looks overclaimed") is not a finding. Name the object, the check, and the artifact.

---

## Object 1 — M25 / N22: the Semaev CM relation-yield lever

**Prior status:** `[A−]` — "the strongest positive finding in the programme."
**Current status (under review):** `[null — cofactor / sampling artifact, mechanism identified, model scale]`.

**The statistic.** `T1_j0(p) = logQ_j0 − logQ_ctrl`, where `logQ = log(mean_K quo)` and
`quo = #{ (x₁,…,x_m) ∈ V^m : the points sum to the target }` — a Semaev relation-yield count over a
factor base of size `|V|`. `j0` = the j-invariant-0 curve `(A=0, B=1)` (μ₆ CM); `ctrl` = the
**nearest-#E non-CM** curve (greedy match). Measured on 24 model primes `p ∈ [523,823]`, `p ≡ 1 mod 3`,
`m = 3`, `|V| ∈ {4..8}`, K=25. The leaky headline run showed `T1_j0` rising `0.207 → 0.834` across
`|V| = 4..8` with **no saturation** — a one-sided positive at all five levels.

**The null-conversion.** `RESULT_h5_cofactor_artifact_v1.md` (+ scripts `h5_followup_run_v1.py`,
`analyze_h5_mechanism_v1.py`, prereg `PREREG_h5_factor_isolation_and_orbit_quo_v1.md`) concludes the
lever is a **cofactor / subgroup-confinement artifact** of the **non-cyclic** j=0 model curves under a
**single-generator sampler**, explained by one structural variable at **Pearson r = 0.96**, null under
a "corrected sampler," and therefore **absent at prime-order (cofactor-1) curves such as secp256k1**.

**The tension to adjudicate.** The companion `RESULT_h5_V_signature_leak_derivation_v1.md` (same date)
concludes only that a *specific* mechanism (one-sided #E-gap leak) is excluded and states **"M25/N22
stay DISPUTED"** — it explicitly does **not** promote the finding to null. The master took the stronger
("null") of the two. Which is right?

**Checks:**
1. Reproduce `h5_followup_run_v1.py` on the frozen schedule (SHA `f92cb4bb…`). Does the corrected
   sampler actually null the effect, or does the "correction" (randomized twist B) **destroy the signal
   the way a shuffle-control can** — i.e., is the corrected sampler a *matched* control that preserves
   the CM structure, or does it break CM along with the artifact? (This project has a recorded failure
   mode where a control "fires on real signal too," making the null vacuous.)
2. Is `r = 0.96` a fit to the **object** (CM relation-yield) or to a **proxy** (cofactor size)? A high
   correlation with cofactor does not by itself prove the CM channel carries nothing once cofactor is
   controlled — check whether a **cofactor-matched** j0-vs-nonCM comparison still shows T1 > 0.
3. The claim "vanishes at prime-order such as secp" is the load-bearing extrapolation. Is it **tested**
   on any prime-order CM curve, or only argued? If untested, it is an assumption, not a result.
4. Do the plants in §1 of the cofactor artifact fire on the *right* thing (a genuine +effect), and does
   the +0.5-injection control resolve a shift of the size actually claimed?

---

## Object 2 — N15: joint multi-readout confinement

**Prior status:** `[OPEN since v11]` — "the load-bearing open cryptographic question."
**Current status (under review):** `[VERIFIED-scope — scoped null]`.

**The object.** On known-`d` secp256k1 keys, does any **bounded-complexity (cheap) function `f(d)`**
predict the joint public readout `T(d) = ( e([d]G), s-class([d]G), y-parity([d]G) )` (18 cells) beyond
a matched null? Here `e` = cubic character `x^((p−1)/3)`; `s-class` = 3-class Eisenstein carry
(`{¾,⅛,⅛}`); `y-parity` = `[2y ≥ p]`. A positive would be an operational cheap keyspace pre-filter.
**Predictor family `F`:** 9 singletons `{d%3,%6,%7,%9,%12, jacobi(d,n), cube-res(d,n), hi₃(d,b),
lo₃(d)}` + all 36 pairs (45 total). Primary `S = max_{f∈F} Î(f;T)`, family-wise permutation p (B=2000,
exact integer count). Run across bit-bands 32/64/128/256 (incl. real secp band) + exact `b=16`
enumeration. Prereg `PREREG_n15_joint_readout_confinement_v1.md`, deviation **D1** applied.
Artifact: `RESULT_n15_joint_readout_confinement_v1.md`, runner `n15_readout_confinement_runner_v1.py`.

**The framing is careful** (it explicitly disclaims any information ceiling: `H(d|[d]G)=0`, the 3.65
bits is a rising floor of the chosen readouts, not a cap). The question is whether the **predictor
family is adequate**, not whether the framing overclaims.

**Checks:**
1. **Deviation D1 is the seam.** The prereg's frozen primary (the full-joint-C predictor) was declared
   "bias-unestimable" and replaced by "the estimable low-order cheap-predictor family." Verify that the
   replacement family is a legitimate estimator of the same object and not a **weaker** family that
   cannot see a joint effect the frozen primary could. Was the frozen primary truly unestimable, or
   estimable with a bias correction that was not attempted?
2. **Predictor-class adequacy.** The family is singletons + **pairs** of *specific low-order* functions.
   The authors themselves list "≥3-component joint predictors, other families/readouts" as untested.
   Is there a cheap 3-way or different-basis predictor (e.g., a small algebraic combination, a lattice
   reduction of `(d%k)` residues, a GLV-orbit-aware function) plausibly carrying the joint signal that
   this family structurally cannot represent? If so, the null is scoped to a family that excludes the
   most likely positive.
3. **Instrument liveness.** Confirm the `ε=1` plant actually fires (monotone at log₂3) at every band,
   and that the `b=128` marginal that "washed on re-seed" was a true false-positive, not a real effect
   killed by re-seeding.
4. Does the null hold identically on the **real** secp band vs the constructed bands, and is the real
   band's estimator at full power (not degraded by sample size)?

---

## Deliverable
Per object: a verdict — **null sound** / **null premature (effect plausibly buried)** / **null
uninformative (control dead or mismatched)** — each backed by a decidable artifact (a rerun number, a
control-firing check, a named excluded predictor with a rationale it should carry the effect). Rank
findings by severity. If both nulls are sound, say so plainly. Files are in
`btc_puzzle_investigation/`; all scripts and preregs named above are on disk.
