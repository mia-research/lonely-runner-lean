# Adjudication of the GLM-5.2 audit of `POSITIVE_FINDINGS_MASTER_v1.md` (2026-07-17)

External model GLM-5.2 was shown the master + Handovers 2/3/v3 and asked to find where the
drafting agent converted scoped results into verdicts. It named **four** specific technical
findings. All four were checked mechanically. **All four are wrong.** Two of them, if applied,
would corrupt working code and a correct proof line.

Scope of this audit: the four named claims + tag inventory + Part V/Appendix A/B. This is
**not** a full re-audit of the master. Verdicts below are scoped to what was actually run.
Script: `_glm_audit_v1.py` (exact integer arithmetic; reproducible).

---

## Claim 1 — "Semaev `S₃` contains a `+2·7` typo; the `A`-slot must vanish since A=0" — **REFUTED**

GLM's asserted "standard" formula:
`S₃ = (x₁−x₂)²x₃² − 2[(x₁+x₂)(x₁x₂) + A]x₃ + (x₁x₂)² − 4B(x₁+x₂)`

The actual Semaev S₃ for `y²=x³+Ax+B`:
`S₃ = (x₁−x₂)²x₃² − 2[(x₁+x₂)(x₁x₂+A) + 2B]x₃ + [(x₁x₂−A)² − 4B(x₁+x₂)]`

`A=0` kills the `+A` **inside** `(x₁x₂+A)` and the `−A` **inside** `(x₁x₂−A)²`. The `2B` term
occupies a **different slot** and survives as `2·7`. The repo formula
(`summation_and_formalgroup_v1.py:19`) is correct as written.

**Decisive test** (S₃ vanishes exactly on collinear triples `P₁+P₂+R=O`, real secp256k1 points):

| formula | vanishes on |
|---|---|
| repo / master (`+2·7` present) | **1406 / 1406** |
| GLM "correction" (`2·7` deleted) | **0 / 1406** |

GLM's own working contained the disproof: it noticed its remembered formula gives the middle
term weight 3 in a weight-4 isobaric polynomial, and concluded *the document* was wrong rather
than its memory. The isobaric property the master claims is real and is what its own formula
fails.

**Damage if applied:** `S₄` is computed as `resultant(S₃(x₁,x₂,x), S₃(x₃,x₄,x), x)`. Editing
line 19 would silently recompute S₄ from a wrong S₃ — poisoning the isobaric-weight claim, the
β-covariance eigenvalues, the cusp leading form, and the first-fall-degree result at once.

## Claim 2 — "`(1−π)−1 = −π` is algebraically impossible in ℤ[ω]" — **REFUTED (misparse)**

GLM read `−1` as an **exponent** (`(1−π)⁻¹`) and correctly showed *that* is false. But `−1` here
is a **subtraction**. The line reads: `Frob@n = 1−π`, and `(1−π) − 1 = −π` — a trivial identity
carrying the actual amicability content:

`#E(F_n) = N(Frob_n − 1) = N(−π) = N(π) = p`

Verified exactly: `N(1−π) = 1 − t + p = n` ✓ (so `1−π` is a legitimate norm-`n` Frobenius for the
partner curve), and `N(−π) = p` ✓. This is the standard `#E = N(π−1)` identity. **The document is
correct.**

GLM then built a replacement narrative (formal-group logarithm, `ℤ[ω]/(π_p−1)`, "π_p ≡ 1 mod
π_n" — which is vacuous) to fix a line that was never broken.

*Actionable (cosmetic only):* the ASCII rendering `(1−π)−1` invites exactly this misread. Write
`(1−π) − 1 = −π` with spaces, or `Frob@n − 1 = −π`.

## Claim 3 — sextant densities — **METHOD OK, NUMBERS STALE**

GLM used rounded `cosθ=0.6354` and reported `p₀≈0.23480` as "exact theoretical targets".
Computed exactly (`cos2θ = t²/2p − 1`, a rational):

```
cos2θ    = −0.192572688042775637582913548821578218236893969447106423010991
p₀       =  0.234900268152131105489408666073932216267297499086645306612437
free 2   =  0.140099731847868894510591333926067783732702500913354693387563
pinned   =  0.125 exactly        sum = 1.000000000000000000000000000000
```

GLM's value is wrong in the 4th decimal. Testing the dataset against `0.23480` would have shown
a spurious deviation from a law that actually holds.

## Claim 4 — "the master stripped [HEURISTIC]/[OPEN] tags and achieved closure by deleting the open panels" — **REFUTED**

| tag | master | H3 | H2v2 |
|---|---|---|---|
| `[PROVED]` | 13 | 12 | 10 |
| `[HEURISTIC]` | **2** | **2** | 0 |
| `[EMPIRICAL]` | 1 | 1 | 0 |
| `[PARTIAL]` | 0 | 1 | 0 |
| `[GAP]` | 0 | 0 | 1 |

- Appendix A is **titled** "EMPIRICAL NULLS (scoped facts, firing controls — **NOT closures**)".
- Appendix B **preserves H2 §8's panel verbatim**: "the two-point/joint-SET bilinear bound
  (2-variable KS) at finer resolution" — the exact item GLM says was erased.
- The `[HEURISTIC]` tag on "genus-1 ⇒ no index-calc lever (Diem 2011)" is retained.
- The `1/√log p` scaling GLM says was "quietly buried without the unconfirmed warning" is marked
  **retracted** in the master. That is *more* conservative than H3's `[PARTIAL]`, not less.

Real but minor: two tag-tokens were lost in the compile (H3's `[PARTIAL]`, H2's `[GAP]`), with
the underlying caveats surviving as prose.

---

## What IS worth acting on (found by checking, not by GLM)

1. **`Part V-3`, master line 155 — the one genuinely soft line.**
   "For general poly-time readouts, 'no concentration' **⟺ ECDLP hard** (Boneh–Shparlinski)."
   The `⟸` direction is trivial (ECDLP easy ⇒ `e_n(a₀d)` is cheap and concentrates). The `⟹`
   direction (concentration ⇒ extraction) is a real reduction that Boneh–Shparlinski does **not**
   prove at that generality — B–S is MSB/hardcore-bit for Diffie–Hellman. Mitigating: the line is
   transcribed **verbatim from H4 lines 94–96**, i.e. inherited, not manufactured by the compile;
   and both H4 and master Appendix C flag B–S as "cited — verify before relying".
   **Fix:** downgrade `⟺` to `⟸ trivially; ⟹ [GAP — no reduction in hand]`.

2. **`T_y` max-bound: H3 `OPEN` → master `[PROVED|KS]` — an earned move resting on one citation.**
   H3 called this "a live un-bounded corner". `t_y_maxbound_v1.py` then did source-first work and
   found the general-`f` Kohel–Shparlinski / Lange–Shparlinski bound covers `bx+cy` (pole order
   ≤3 at O) with a constant depending only on `deg(f)` — hence uniform in `(b,c)`. The script
   grades this **CITED**; the master grades it **`[PROVED|KS]`**. That is a one-notch upgrade
   whose entire weight sits on whether L–S's constant really is uniform in the coefficients.
   **This is the single highest-value verification target in the document.** Appendix C already
   says "verify before relying" — this is where that sentence does real work.

   Note: GLM asserted this panel *must* be open because `e_n(ad)` is not algebraic in the
   coordinates so Weil cannot bound the mixed sum. That is **correct about Weil and irrelevant to
   KS** — Kohel–Shparlinski is precisely the machinery built for mixed sums of that shape. GLM
   retracted its own Weil proof correctly and then drew the wrong conclusion from the retraction.

---

## Meta — why this audit failed, and the bias it mirrors

The user's diagnosis of the drafting agent (prose layer reverts to "ECDLP is proved hard" because
the training prior says so) is real and is already recorded
(`feedback_negative_bias_enlarge_nulls_2026_07_17`). **This audit is not evidence for it.**

GLM was asked to find overclaiming and produced four confident, well-structured, entirely false
findings. That is the **mirror** of the same failure: pattern-matching to the genre "LLM agent
overclaims crypto security" and manufacturing findings to fit. CLAUDE.md §3 already names it —
*"reviewers asked for issues will manufacture them."*

The asymmetry to hold onto: replacing "agree with the training prior" with "agree with whoever
critiqued last" is the same error with the sign flipped. The defense in both directions is the
same and it is not rhetorical — it is that `S₃` either vanishes on 1406 collinear triples or it
does not, and `N(1−π)` either equals `n` or it does not. Both were run. Both are reproducible.

**Standing caution on this file:** it defends a document written by a previous Claude session, so
it carries the opposite bias risk. Every verdict above is therefore mechanical and rerunnable
(`_glm_audit_v1.py`); none rests on interpretation. Re-run it rather than trusting it.
