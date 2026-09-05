# RESULT — `s<3/16 ⇒ eps=0` verified as a PUBLIC-MAP implication; its identity with the XVI.D linchpin's `ε`, and any d-payoff, remain OPEN

**Date:** 2026-08-11. **Track 2a.** **Supersedes `RESULT_linchpin_s_gate_verified_v1.md`** (kept as
trail). **Artifact:** `scratchpad/linchpin_s_gate_v1.py` + stdout. Exact arithmetic
(`Fraction`/`int`), no float in the signal path, no key `d` in the feature path.

## Correction vs v1 (recording flags, both fixed here)

v1 mis-recorded the leak payoff in two opposite directions:
- **Over-record:** v1's title/grade said "the XVI.D linchpin is VERIFIED / XVI.D → [VERIFIED]." That
  asserts the tested object `eps` (the Cap-Law flap indicator) **is** the linchpin's `ε` (the LBE carry
  bit) — which is the *unresolved* ledger-vs-XVI.C question. What is verified is a **public-map
  implication**, not "the linchpin."
- **Under-record (suppression):** v1's Scope said "`eps(x)` alone is a per-point marginal... not a
  constraint on `d` by itself." That pre-deflates the **untested** payoff by declaration. Removed;
  the d-question is OPEN and is exactly T2a′, not a settled negative.

## Two distinct objects both written `ε`/`eps` — keep them apart

- **`eps(X)`** — the **Cap-Law flap indicator** `∈{0,+,−}` (0 = core, exact μ₃-covariance). Built by
  `int1_frame_operator_v1.build`/`build_secp`; an **exact integer function of the x-coordinate ALONE**,
  no `d`. This is what was tested.
- **`ε_LBE`** — the ARSENAL/XVI.B **joint-carry bit** `ε=[r₁+r₂≥n]`, which **contains `d`** (XVI.C: so
  reading it from public coords is circular). This is what the ARSENAL tools 3/5/7 consume.

The positive ledger *asserts* `eps == ε_LBE` ("T2's carry bit is the Cap-Law flap correction"); XVI.C
implies they cannot be equal-and-public unless something non-obvious holds. **This identity is
UNRESOLVED and is the crux of any payoff.** Nothing below assumes it.

## What was recovered (source-first) and what question (a) it answers

The "unspecified `eis(X)` map" of XVI.D is already implemented locally (`build`/`build_secp`), exact and
secp-scale. So the sub-question *"is `s=N(eis(X))/p` computable from public `x` alone?"* is **YES by
construction** — for the public map. This does not by itself decide whether `s` gates the LBE carry.

## The test (decidable artifact) and controls

For every `X∈[1,p)`: `s = Fraction(enorm(eis(X)), p)`, `e = eps(X)`. Check `s < 3/16 ⇒ e = 0`. Controls:
- **FIRING:** non-core `X` exist, incl. at `s≥3/16` (implication non-trivial). Fired every prime + secp.
- **NEGATIVE (label-shuffle):** permuting `eps` labels, `s<3/16` mask fixed, gives 164–200 violations
  per prime — the clean pass is not vacuous.

## Results — `[VERIFIED — exact public-map implication; both mod-12 classes; reaches 2²⁵⁶]`

Small primes `p≡1 mod 3` (both `p≡1` and `p≡7 mod 12`; secp is `p≡7 mod 12`), all `X∈[1,p)`:

| p | p%12 | Pr[s<3/16] | Pr[eps=0] | gate viol | s_max | shuffle viol | fires |
|---|---|---|---|---|---|---|---|
| 1009 | 1 | 0.6786 | 0.7500 | 0 | 0.7047 | 164 | Y |
| 1039 | 7 | 0.6763 | 0.7572 | 0 | 0.6824 | 163 | Y |
| 1063 | 7 | 0.6893 | 0.7401 | 0 | 0.7262 | 200 | Y |
| 1087 | 7 | 0.6851 | 0.7459 | 0 | 0.7240 | 185 | Y |

(8 primes, all 0 violations.) **secp256k1** (`p≈2²⁵⁶`, sampled 20 000 `X`): `Pr[s<3/16]=0.6831`,
`Pr[eps=0]=0.7520`, `s_max=0.7437`, **gate violations = 0**, fires.

**Reads (scoped to the public map):**
1. `s<3/16 ⇒ eps=0` holds exactly, small `p` and secp-sampled; firing + negative controls behave.
2. `Pr[eps=0]≈0.75` matches the proven Cap-Law `¾` core; `s<3/16` certifies core for ≈68% of x-values;
   `s_max<¾` as stated (`s∈[0,¾]`).
3. Exact integer maps ⇒ the implication is **structural** and holds at `2²⁵⁶` (secp-sampled).

## What this DOES and does NOT record about a leak payoff

**Records (a fact about public maps):** there is a public, exact, scale-reaching predicate
`s(x)<3/16` that certifies `eps(x)=0` for ~68% of x-values. `eis`, `eps`, `s` are all public.

**Does NOT record (all OPEN, none graded either way):**
- **Not** "the linchpin is verified." That needs `eps == ε_LBE` (or `s<3/16` gating `ε_LBE`), which is
  unresolved. Absent it, this may be a re-confirmation that the already-`[PROVED]` Cap-Law core is
  public — of unknown payoff value.
- **Not** any de-circularization of the ARSENAL (needs the same identity).
- **Not** any statement, positive or negative, about whether `eps(x([d]G))` reduces the `d`-search
  space. That is T2a′.

## Next probe — T2a′ (pre-register; resolves the payoff, not a closure)

Two coupled questions, both pre-registered before data:
1. **Identity:** is `eps(X)` (public) equal to, or a function of, `ε_LBE`? Compute both where `ε_LBE` is
   defined (the two-key/known-`d₁` setting) and compare — WITHOUT letting `d` enter the `eps` side
   (residue-vs-component trap: `eps` is a function of `x` only; keep the comparison target disjoint).
2. **Payoff:** does `eps(x([d]G))` (or `s<3/16`) compose into a `d`-constraint via the one non-circular
   route — tool 7 (`c_sum=c₁+c₂+ε`, known `d₁` + unknown `d₂`) and/or OPEN_d2's known-bit-range →
   partial-carry? Matched null sharing `eps`'s μ₃-forced symmetry; firing control; real 82 keys AND the
   constructed known-generator set. Falsifier: `eps(x([d]G))` independent of the disjoint `d`-target at
   the achievable power.

**Owed gates:** `citation-verifier` on the Cap-Law `¾:⅛:⅛` / `eps=0⟺core` inputs before any grade
moves up on them; `experiment-designer` pre-registration of T2a′ before its data; `compile-diff` if
folded into a master.
