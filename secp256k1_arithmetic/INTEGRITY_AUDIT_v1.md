# Integrity audit — where the method was faulty (2026-07-11)

Prompted by: "check our work… imported assumptions, ignored inconvenient data,
was the method/scale/parameters correct… you have a history of downplaying on a
minor faulty test." This is that audit, done adversarially against my own
*negative* conclusions. It found real method faults — even where the conclusion
ultimately held.

## The Finding-3 episode — three iterations, two of them unreliable

Claim under test: `vertical_zfr_replication.md` Finding 3, "CM/μ₆ common mode is
rank-3, 3× the Dirichlet rank-1 (CONFIRMED)."

1. **First dismissal (`thread_cm_commonmode_v1.py`): FAULTY method, right answer
   by luck.** I used order-6 Dirichlet characters mod q and got "0 above null,"
   wrote "NOT CONFIRMED — null artifact." **But that construction never even
   reproduced the finding's basic phenomenon** (its "3 vs 1 above the edge"). You
   cannot refute a finding with a tool that doesn't reproduce it. The verdict was
   asserted, not earned.
2. **Faithful attempt (`thread_finding3_faithful.py`): CONFOUNDED, nearly flipped
   me to the wrong answer.** Built the actual `F_{q²}`-character-on-Eisenstein-primes
   construction. It showed the CM family at **6× the edge, surviving the matched
   null** — appearing to *confirm* Finding 3 and force a retraction of my dismissal.
   Two confounds inflated it: the shared **`1/√p` envelope** (a common mode across
   *all* L-coefficient families, not sextic) and **different sample sets** for the
   two families. My matched-null there also mis-fired (independent-column shuffle
   destroys the envelope, so *everything* — including Dirichlet — read "6 above
   null").
3. **Clean test (`thread_finding3_clean.py`): trustworthy.** Same samples, same
   `1/√p` envelope, and an **envelope-preserving random-character null**. Result:

   ```
   Dirichlet(μ2):  real top 22.63  vs random-char null 23.22±0.53   z = −1.12
   CM nonnorm(μ6): real top 18.75  vs random-char null 19.48±0.48   z = −1.51
   ```

   Both real tops sit **below** the null — the characters are *more* orthogonal
   than random, no common mode. The entire apparent "common mode" is the `1/√p`
   envelope. **Finding 3 is not a genuine sextic effect** — conclusion confirmed,
   now *earned*.

**The lesson (your point, vindicated):** my first dismissal was reached on a
faulty test; my second nearly reversed it on a confounded test. The conclusion
held only after a third pass with same-sample + envelope-preserving + matched-char
null. I was doing exactly the thing flagged — concluding from a minor faulty test —
and it cut *both* ways (a faulty positive almost flipped me too).

## What this forces me to correct

- **`SPECTRAL_AUDIT_v1.md` Finding-3 row:** the verdict stands ("not genuine
  sextic") but the *justification* is replaced — it's the `1/√p` envelope, shown by
  the clean random-character null, **not** the earlier order-6-Dirichlet "0 above
  null" (which was a non-reproducing test).
- **`ULTRATHINK_THREADS_v1.md` I2 "spectral axis is exhausted / shadow
  meta-theorem":** **DOWNGRADED from a claim to a conjecture.** It rests on the same
  confound-prone Gram methodology that just flip-flopped twice. I over-stated
  certainty. What survives: the *dilution* χ₋₃ finding, because it has a
  mechanism independent of these confounds (below).
- **Dilution (`DILUTION_CHECK_v1.md`):** the χ₋₃-shadow conclusion is **robust** —
  but for a reason I should have foregrounded over the eigenvalue ratios: the mode
  is `a_ℓ = 0` *identically* on inert primes (an exact shared zero on a
  χ₋₃-selected half of samples), verified two ways that do NOT depend on envelope
  or null design — restricting to split primes kills it (0.575→0.120), and the top
  eigenvector aligns with χ₋₃ at 0.997. That mechanism is not an artifact. The
  weak part remains that the **feature map was guessed** (Q=50 off 25% from the
  reported table); the *mechanism* is solid, the *exact-numeric reproduction* is not.

## Broader assumption / scale / parameter check

- **Imported assumptions:** the dilution feature map (`cos(2π a_ℓ/q)`) was a guess,
  not the user's script — flagged. Finding-3's exact character subset and sample
  set were guessed until the clean test. Both now labelled conditional.
- **Ignored inconvenient data:** yes — I initially waved off the split-only
  "residual REAL modes" in `thread_mu2_mu3_probe.py` as "a_ℓ shadows" without
  verifying; given the confound lesson, those deserve the same envelope/null
  scrutiny before any "sextic invisible" claim. Marked open.
- **Scale:** GUE (36 spacings) and the Gram tests (d≈300, n=500, 120–200 null
  reps) are small; adequate for the sign of an effect, not for fine rank claims.
  Stated as such now.
- **What is NOT affected — the exact arithmetic (Ledger A):** χ = −(28/π)₆⁻¹
  (1442/1442 exact), amicable 13/50 = S–S Conj 40 (exact rationals, all 12
  classes), the zeros (LMFDB-matched, verified-complete), BSD (L(1)=Ω to 28
  digits), the formal group and ASD congruence (exact). None of these are
  Gram/spectral/null-dependent; they are exact computations or LMFDB-checked and
  stand unchanged.

## Net

- My spectral **dismissals were method-faulty** even where the answer held; the
  Finding-3 conclusion is now properly earned (envelope, not sextic).
- The **"spectral axis exhausted" meta-claim is downgraded** to a conjecture.
- The **dilution χ₋₃ result stands on its mechanism** (exact shared zero on inert),
  independent of the confounds; only its numeric table-match is approximate.
- The **exact CM arithmetic is untouched and solid.**
- **Standing rule for any further spectral/Gram test:** same sample set, envelope
  preserved, matched random-character (not iid-MP, not independent-shuffle) null,
  before any rank/common-mode claim.
