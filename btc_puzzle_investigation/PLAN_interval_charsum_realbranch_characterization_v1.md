# Real-branch characterization plan — what to run IF L=80000 refutes the generic prediction

**Date:** 2026-08-02. **Contingent** on `bq4af5tea`'s L=80000 row showing intervals ≪ random
(`ratio ≪ 1`, `P(int<rand) → 1`, growing vs L=20000, `z ≳ 3`) — i.e. **refuting** the generic-mixing
prediction of `ANALYSIS_interval_charsum_generic_prediction_v1.md`. If instead it confirms generic
(`P≈0.5`), only **R3** runs — as a mixing *confirmation* — and the rest is shelved.

Goal if the anomaly is real: locate its **specificity** (generic-to-all-curves vs secp/j-structural)
and its **mechanism** — never label it "generic" without the control-curve evidence (Rule 4).

---

## R3 — orbit autocorrelation [RUN FIRST; useful on BOTH branches]
**Question:** are consecutive orbit char-values correlated, or independent (mixing)?
`[s+d]G = [s]G + [d]G`, so `c(s)=χ₃(x([s]G))` and `c(s+d)` are related by "translate by `[d]G`". Under
mixing they are independent for `d≠0`.
**Statistic (exact integer):** for lags `d ∈ {1,2,3,…,32, and a few large}`, the shifted correlation
`A(d) = |Σ_s ω^{c(s)−c(s+d)}|²` over an orbit of length L. **Matched null:** the same `A(d)` on a
*random* re-indexing (shuffle the orbit's codes) — kills any real lag structure, keeps the marginal.
- `A(d) ~ L` for all `d≠0` (matched to shuffled null) → **mixing confirmed** → generic; the
  interval=random result is fully explained, dissolution earned + mechanism named.
- `A(d) ≫ L` at some small `d` → **short-range χ structure** = the anomaly's source. Note: `A(d)` is a
  χ₃-difference under translation by `[d]G` — this is exactly a **group-law difference-set** quantity
  (ties to C2), so a hit here is a bridge, not a dead end.
**Cost:** O(L) per lag; cheap on secp (L=10⁵, ~32 lags ≈ minutes).

## R1 — the scaling exponent [only if R3/L=80000 show a real effect]
**Question:** does `|Σχ|²` grow like `L` (generic random walk) or slower (extra cancellation)?
Median E3 over a ladder `L ∈ {10³,10³·⁵,…,10⁶}`, fit `E3 ~ L^θ` (integer medians; θ from a
log-log slope, display-only float). **Generic θ=1.** `θ<1` = sub-random cancellation, the quantitative
signature of the anomaly, and its exponent is the thing to explain.
**Cost:** O(L) per point; the L=10⁶ point is a logged background run (~1 h on secp).

## R2 — control-curve specificity [the "is it a lever" test]
**Question (Rule-4-compliant characterization, NOT dismissal):** is intervals≪random present on
- **secp256k1** (j=0, CM by ℤ[ω], μ₆) — the target,
- **another j=0 curve** at a *different* prime `p'≡1 mod 3` — tests j=0/μ₆-structure vs the specific secp prime,
- **a j=1728 curve** (CM by ℤ[i], μ₄) at `p''≡1 mod 3` — tests μ₆-specific vs CM-generic,
- **a random ordinary curve** (generic j) at `p'''≡1 mod 3` — tests curve-universal vs structured?

Same interval-vs-random statistic, matched small primes (≈2³²–2⁴⁸ for speed; the effect's
*presence/scaling* is prime-size-independent if real). Outcome map:
- present on **all** curves, same magnitude → a **generic orbit fact** (still reported with the
  evidence, per Rule 4 — earned, not asserted; not a secp lever).
- present only on **j=0** (or only μ₆) → a **CM/torsion-structural** effect — a candidate lever tied to
  secp's automorphism structure.
- present only on **secp's exact prime/generator** → maximally specific — chase hardest.

**Setup per control curve:** pick `p'≡1 mod 3`; `y²=x³+b'`; find a generator `G'` and its order; reuse
the exact-integer char/stat machinery (only `p, b, G, n` change). j=1728 uses `y²=x³+a'x` and needs the
quartic-character analog for the μ₄ readout, or stay on χ₂/χ₃ which are defined at any `p'≡1 mod 3`.
**Cost:** small primes → each curve's full L-ladder is minutes.

---

## Discipline
- Every run: matched null (Rule 3 — here the shuffled-orbit null for R3, random point-sets for R1/R2),
  exact integer stats, real op-count + timing (Rule 2), OOS where a fire is claimed.
- **Pre-registration + experiment-designer gate before any of R1–R3 runs** (CLAUDE.md §2/§7) — this
  file is the design, not the frozen spec.
- Grade every outcome; "generic" is a GRADED claim requiring the R2 control-curve evidence, never a
  reflex (Rule 4 / closure-grade discipline).
- If L=80000 CONFIRMS generic: run **R3 only**, expect `A(d)~L` (mixing), record it as the earned
  mechanism, shelve R1/R2, proceed to C2.
