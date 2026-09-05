# PREREG v3 — `A_new` re-audit, corrected control on DISJOINT unread data

**Written 2026-08-02, after `VOID_anew_cartier_c4_adjudication_v1.md`, BEFORE any v3 script exists.**

v2's run is void: control **C4 fired** (7/18 primes). Session rule 2 forbids rescuing it and marks
that sample `[CONTAMINATED — outcome known before corrected control]` permanently. This file is the
"v2 pre-registration written before unread data is touched" that rule 2 prescribes.

**v2 is inherited in full** — objects (v1 §1 + v2 §0), hypotheses H-A / H-B / H-C, exponent table
(v2 §2), controls C1, C2, C3, C5, PC, permitted conclusions (v2 §5), and the power/scope statements.
Only the items below change. Everything not listed here is unchanged and still binds.

---

## 1. CHANGE 1 — the sample is disjoint from the contaminated one

No prime and no random seed from the v1/v2 runs is reused. The contaminated sample is
`MAIN {p ≡ 3 mod 4 : 7 ≤ p ≤ 199} ∪ {211, 251, 503, 1019}`,
`CONTROL {p ≡ 1 mod 4 : 5 ≤ p ≤ 197} ∪ {257, 509, 1013}`, seeds `20260802 (+1, +2)`,
and for H-A `{7, 11, 19, 23, 31, 43, 67, 103, 127, 211}`, seed `20260802`.

| arm | v3 sample (disjoint by construction) |
|---|---|
| **MAIN** `D=3` | `{p ≡ 3 mod 4 : 211 < p < 500, p ≠ 251}` ∪ `{1031, 1039}` |
| **CONTROL** `D=3` | `{p ≡ 1 mod 4 : 197 < p < 500, p ≠ 257}` ∪ `{1021, 1033}` |
| **PLANTED** `D=5` | the MAIN v3 primes `< 500` |
| **H-A** | `{223, 227, 239, 263, 271, 283, 307, 311, 331, 347}` |
| seed | **`20260803`** (`+1`, `+2` for the control and planted arms) |

`C5` compute cap: `p ≤ 300` (fixed now, not post-hoc). Curated cubics are retained; at these primes
they were **never run** by `supersingular_mu4_mechanism_v1.py` (`prime_range(13,200)`), so on this
sample **every row is blind** and the v2 §4 blind/observed split is moot.

## 2. CHANGE 2 — C4 replaced, with its firing condition made reachable

The v2 C4 failed because it fixed `f = x³+2` without requiring `E : y²=f` to be **ordinary**; at
`p ≡ 2 mod 3` that `E` is supersingular, the true Hasse invariant is `0`, the corrupted one is `0`,
and `0 ≡ 0` passes. Replacement, stated in full:

- **C4a (the `b=2` / C1 path).** For each tested `(p, f)` **restricted, by a rule fixed here and
  checked before the perturbation is read, to pairs with `E` ORDINARY (`a_p(E) ≢ 0 mod p`)**:
  perturb `t₂ → t₂+1` and require `Tr(M)` to **change**.
  **Pass: change at ≥ 95% of ordinary-`E` pairs, and ≥ 20 such pairs tested.**
  Pairs with `E` supersingular are **reported separately and excluded from the rate** — they are
  guards, not controls, and are labelled so.
- **C4b (the `b=3` / new-part path).** On the **CONTROL and PLANTED arms only**: perturb `t₃ → t₃+1`
  and require the new-part block to **change**. **Pass: ≥ 95%.**
- **C4c — stated, not run.** On the **MAIN** arm the new-part block is forced to zero, so no
  perturbation of `t₃` can move it; v2 §3 wrongly wrote a pass condition there. **The MAIN arm has no
  C4 leg. `PC` is the MAIN arm's only control**, exactly as v2 §4 said and v2 §3 failed to encode.

## 3. CHANGE 3 — what the two artifacts can and cannot carry

Rule 2 bites on the *sample*, not on a derivation. Kept apart explicitly:

- **The H-B derivation** (that `𝒞` vanishes on `V₁⊕V₃` at `p ≡ 3 mod 4`, for the three ingredients
  named in v2 §0) is a proof. It is **not** validated by any sample and is **not** contaminated by
  one. Its grade is gated on **an independent reader**, per v2 §5, and no run in this session can
  raise it. Until that reader has run, it is `[UNREVIEWED DERIVATION]` and nothing more.
- **The empirical shadow** `[VERIFIED — N distinct classes]` is gated on this v3 run passing
  C1, C3, C4a, C4b, C5, PC and C2.
- **H-A** is re-run on the disjoint prime list above. The v2 H-A result is contaminated and is
  superseded by whatever this run reports, not averaged with it.

## 4. UNCHANGED and still binding

v2 §5's outcome table in full, including: any MAIN-arm non-zero ⇒ **H-B retracted**, failing pair
named; `PC` not firing ⇒ **VOID**; `C2` not firing while `PC` does ⇒ **H-C refuted**, not instrument
death; superspecial kept distinct from supersingular in every sentence; external fact (i) discharged
only by A5, external fact (ii) **not re-derived** and still owed if H-B falls.

v2 §4's unforced accounting in full: the MAIN `D=3` arm carries **0 unforced bits** — its zeros are
forced twice over — and is reported as an **instrument check on my code**, whatever `N` is. The
unforced content is `PC`, `C2`, `C3`, `A1`, `A5`, and now `C4a`.

Rule 1 void condition in full: every number in the result must be traceable to an executed `.log`.

---

*Frozen at first v3 script execution. If a control fires again, the v3 sample is likewise
contaminated and a v4 disjoint sample is required — the sample is cheap, the rule is not negotiable.*
