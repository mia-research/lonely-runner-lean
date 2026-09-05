# RESULT — public-feature → `d mod q` leakage: idea-level battery (re-opens N17/N18 as SCOPED, not CLOSED)

**Grade: `[EMPIRICAL — NULL at power, SCOPED]`.** Date 2026-08-17. Motivation: the D2/mod-6 audit
(`AUDIT_d2_bridge_mod6_reduction_v1`) tested only the **source's 5 specific predictors** and its own §6
concedes *"absence of any cheap public function correlating with d mod 3/6 … cannot be proven by
sampling."* v12 nonetheless carried N17 (mod-6) and N18 (Dirichlet-island) as **"CLOSED NULL."** This
re-test does the *idea-level* version — a broad battery, the island's own CF features, larger moduli, with
a cardinality-matched control and OOS — to replace an argued closure with a tested scoped null.

Signal path exact (Python `int`); MI is a float statistic ranked ONLY against a matched permutation null
(project no-float rule). Reproduction: `scratchpad/idea2.py`, `island_largeq.py`, `island_control.py`.

## Test 1 — broad battery (the "test the idea" version of D2/mod-6)
11 cheap public features of `(x,y)` — `x%{2,3,6}`, `y%2`, `s=[2y>p]`, `jac(x,p)`, `hi2(x)`,
`floor(p/x)%6`, `maxPQ(x/p)%4`, `(x·y)%6`, `cubic-e` — × `d mod {2,3,5,6}` × 6 prime-order CM curves
(`p=211→2029`). Matched-permutation p (shuffle target, 1500 perms).
- **Survivors at p<0.01: 2 / 264 cells** — vs **~2.6 expected by chance**. Both sporadic (1/6 curves), do
  not persist across scale.
- **Firing control** (feature = `d%6` with 30% random flips) **FIRES**: MI=1.30, p=0.0007. The machinery
  detects a real partial leak; it saw none here.

## Test 2 — the Dirichlet-island idea at its OWN moduli (in-scope core)
The island claim reduces, in scope, to: *does a public CF/best-approximation feature correlate with
`d mod q`?* Features `maxPQ(x/p)` (largest partial quotient — the "island"/best-approx object),
`floor(p/x)` (Dirichlet hyperbola), `len_CF(x/p)` × `q=2..24` × 2 curves.
- Raw survivors at p<0.01: **7 / 138 vs ~1.4 chance (~5×)** — SURFACED as a candidate, not dismissed.
- **Two tells** demanded a specific control: survivors were **inconsistent across curves** (different
  `(feature,q)` on each) and the high-MI ones (`maxPQ` 0.86/0.71) use **high-cardinality** features (MI
  upward-biased).

## Test 3 — DECISIVE controls (the candidate dissolves)
- **Cardinality-matched scramble** (same value-multiset, x-relation destroyed): produces survivors **as
  often as the real feature** — p=1213 scrambled `maxPQ` = **3** survivors vs real = **0**; real/scrambled
  interchangeable throughout. A genuine x→d leak needs real ≫ scrambled; it isn't. ⇒ the count is
  high-cardinality MI-bias, not leakage.
- **OOS on 6 independent curves:** each survivor fires on only **1–2/6** (`maxPQ`↔d%19 **1/6**;
  `floor(p/x)`↔d%9 **2/6**; ↔d%16 **1/6**; `len_CF`↔d%3 **1/6**), p-values uniform-scattered on the rest.
  A real leak persists; these don't.

**Anomaly-drill outcome: the candidate DISSOLVED into a cardinality artifact — a sharper law
(high-cardinality features inflate MI; the matched control is the fix), not a closure.**

## Grade & scope
- **`[EMPIRICAL — NULL at power]`** that no *cheap single public feature* in this battery (incl. the
  island's own CF/best-approx and Dirichlet-hyperbola features) correlates with `d mod q`, `q≤24`.
- **This STRENGTHENS N17/N18** from "source's 5 predictors" to an idea-level battery, and **REFRAMES them
  from CLOSED to SCOPED.** It does NOT make them closures.
- **Explicitly OPEN (unchanged):** (i) the **joint** multi-feature question (N15 — `e ⊕ s ⊕ parity ⊕
  interval` together), untested here; (ii) larger scale / non-CM / larger q; (iii) the general "absence of
  ANY cheap public function" — DLP-adjacent, **unprovable by sampling** (audit §6). A scoped null, held to
  its scope.
