# RESULT — signature leakage test for C_a (pre-reg: PREREG_L3_signature_leakage_v1)

**[PROVISIONAL — experiment-designer gate unavailable this turn; owed]**
Grade: **VERIFIED-scope** (empirical, controlled, scaling sweep). Conditional null:
bound holds for this feature (full Frobenius signature) + this target (family
parameter `a`) + this method. Does NOT promote any grade on its own (§2a).

## Controls (must-fire) — both fired
- Positive (feature = `a`): `N_sig = 66 = p−1`, frac = 1.000. Counter can see a leak. ✓
- Negative (feature = `a mod 12`): `N_sig = 12`, bounded. Counter reads bounded as bounded. ✓

## Result
Full genus-3 Frobenius signature of `C_a`, `a` over `F_p^*`, `p ≡ 7 mod 12`,
swept `p = 7 … 1699` (240× range):

```
 p      N_sig  maxclass  recov_bits  frac_pinned
 7        6       1        2.585        1.000
 43       6       7        2.585        0.479
 163      6      27        2.585        0.352
 691      6     115        2.585        0.274
 1699     6     283        2.585        0.241   → 0
```

**`N_sig ≡ 6`, flat across the whole range.** Max class size grows ∝ `(p−1)/6`:
each signature bundles ~`p/6` distinct values of `a`. Recoverable info is a
**constant 2.585 bits** regardless of `p`; the fraction of `a` pinned → 0.

## Verdict vs pre-committed prediction
Pre-committed H0 (N_sig bounded, flat, frac→0). **Confirmed.** Falsifier
("N_sig rises with p") did **not** trigger — flat at 6 over 240×. Prediction was
right in kind and nearly exact: I guessed ~12 (`cubic × quartic`); the truth is
**6** = `F_p^*/(F_p^*)^6`, the sextic-twist classes of the `j=0` curve (the quartic
character collapses to quadratic since `p ≡ 3 mod 4`, so `3 × 2 = 6`).

## Interpretation (now tested, not argued)
The entire arithmetic signature of `C_a` — including the μ₃ split and the `L^(3)`
perfect-square structure — is a **6-valued forward function of `a`**: exactly "which
sextic-residue class does `a` lie in." Those 2.585 bits are the residue symbols of
`a`, computable forward in one exponentiation; they are not the inversion of anything.
At 256-bit scale: `2.585 / 256 ≈ 1%` of the parameter, and that 1% is public.

The §5 "collapse-to-scalar ⇒ no lever" claim in
`ANALYSIS_L3_perfect_square_mu3_schur_route_v1.md` is now backed by a controlled,
scaling **measurement**, not an inference.

## Honest scope boundary (uncovered — self-audit, §2a frame layer)
This tests recovery of the **family parameter `a`** from the family's arithmetic — the
object the original idea was actually about (`C_a`, twist `a`). It does **not** test the
**fixed-curve secp ECDLP** (`Q = kG` on one curve, a different object); nothing here
speaks to that, and nothing here claims to. Mechanical layer covered by the fired
controls; frame layer's one open item is exactly this family-vs-fixed-curve distinction,
stated not hidden.

## Owed
experiment-designer pre-registration audit (gate unavailable this turn).
Reproduce: `btc_puzzle_investigation/leak_test.sage`.

---

## SELF-REVIEW CORRECTIONS (same session, `selfaudit.sage` / `rootcheck.sage`)

Three items I asserted rather than checked in the body above; corrected on re-audit.
None overturns the null; one sharpens it, one is a mis-attribution, one is imprecision.

- **C1 — mis-attribution of the 6.** The `N_sig = 6` is carried by the **elliptic
  quotient `E_a`** (its sextic twist: distinct `E_a` = 6), NOT by the new μ₃/L^(3)
  object. Measured: distinct `E_a` = 6, **distinct `N_a` = 2**, distinct full `L_a` = 6
  (p = 43,67,127,163,691). So the *classical* `j=0` CM twist of `a` carries `log2 6 ≈
  2.585` bits; the **new part — the actual object of the idea — carries exactly 1 bit**
  (which cubic class ⇒ square at Frob¹ vs Frob³), flat in `p`. The body's phrase "the
  μ₃/L^(3) structure is a 6-valued label" was wrong; it is a **1-bit** label, and the
  other 2.585 bits are the well-known elliptic sextic residue. Conclusion (no lever)
  unchanged, and *strengthened* for the specific object.

- **C2 — weak positive control. [CLOSED — `graded2.sage`]** Feature = `a` was only the
  trivial extreme. Graded synthetic controls with known leak-scaling exponents, run
  through the SAME `N_sig` detector over `p=43…4243` (p≡7 mod12), recover the true
  exponent to ±0.003:

  | synthetic feature      | true slope | measured |
  |---|---|---|
  | `a mod 12` (constant)  | 0.00 | 0.000 |
  | `a mod ⌊p^0.5⌋`        | 0.50 | 0.498 |
  | `a mod ⌊p^0.75⌋`       | 0.75 | 0.751 |
  | `a` (full)             | 1.00 | 1.003 |

  The detector tracks partial and scaling leaks faithfully. Therefore the flat real
  feature (full signature `N_sig=6`; new part `N_a`=2; both slope ≈ 0 to `p≈1700`) is a
  **calibrated** null on scaling, not a blind one — a `√p`-scaling leak would have shown
  slope ≈ 0.5 and did not appear. C2 discharged.

- **C3 — the target was never a real attack surface.** `a` is public (it sits in the
  equation `w^4=x^3+a`); "recover `a` from `L_a`" is a well-posed info-theoretic
  question but its bearing on any ECDLP was always thin. The null is real for this
  channel; it does not evidence security of anything — it confirms a many-to-one map
  that test #2 (`l3_test2`) already implied. Confirmatory, not independent.
