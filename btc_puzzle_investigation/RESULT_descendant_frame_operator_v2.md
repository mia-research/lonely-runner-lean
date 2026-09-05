# RESULT v2 — AUDIT of v1: math stands (bias check clean); the "no d-side content" disclaimer is CORRECTED

*2026-07-24. Supersedes `RESULT_descendant_frame_operator_v1.md` on two points; the verified results of v1
§1–§5 stand unchanged except as noted. Triggered by (a) a self-cert word ("genuinely open") and (b) the
user pointing at the specific phrase "there's no d-side content." Checks run, not reread. No ECDLP claim
is made (see §3 for why that phrasing, not the withdrawn one).*

---

## 0. Audit outcome in one line

The **mathematics is sound** — a bias check confirms the construction is unbiased, and three
load-bearing assumptions were verified against the record's actual code. **One scope claim was wrong:**
"no d-side content" asserted a security-irrelevance about the object that was never analyzed. Corrected
in §3.

## 1. The math survives — checks that could have refuted it, and did not

- **Bias check `[VERIFIED]`.** Over 40 primes `1000<p<4000`: `ℓ=1` mean `0.7504` (target `0.7500`,
  `|mean−target| = 4×10⁻⁴ ≈ sd/√N`), `ℓ=3` mean `0.8802` (target `0.8802`, bias `−0×10⁻⁴`). **The point-set
  construction is unbiased**; the earlier `ℓ=1` scatter (0.781…0.757) was finite-size boundary noise, not
  a systematic error, and `ℓ=3`'s landing on `(8+√37)/16` is **not luck** — it is the unbiased mean.
- **`eis` is order-based, summed over all `F_p` `[VERIFIED — record's code]`.** `int1_frame_operator_v1.py:75`
  is `for x in range(1, p):` with `C = Σ_x eis(x)eis(x)ᵀ` (line 6) and the `¾` theory stated as "uniform
  60° rhombus" (line 99). So M10 reduces every `F_p` value through the lattice, exactly what my descendant
  computation does through `O_3/(π')`. My construction is the faithful analog, not a different object.
  *(Scope note kept: eis on a descendant is a definition-by-analogy — the record never computes a frame
  operator off the crater. It is the natural extension, not a recipe already in the record.)*
- **secp's 3-descendant is `F_p`-rational `[VERIFIED]`.** `Φ_3(0,Y)/Y` has exactly **1 root mod secp's
  `p`** (root-count via `gcd(Y^p−Y, ·)`, validated against brute force at `p=43,67,79,103`). §5's "a real
  256-bit `F_p` curve" holds.

## 2. Deviation not filed at run time — the "monotone" criterion `[recorded]`

Prereg §3 pre-committed "ℓ=3 → 0.8802 ± 0.01 **(monotone in p)**". The `±0.01` gate passed **decisively**
(all `|Δ| ≤ 8×10⁻⁴`). The **monotone qualifier did not**: `ℓ=3` reads `0.8793, 0.8801, 0.8803, 0.8800,
0.8802` — it oscillates within `3×10⁻⁴` about the target. That oscillation is finite-size noise about an
exact algebraic limit (confirmed unbiased in §1), **not** drift, so the promotion to `[VERIFIED]` stands —
but it rests on **convergence-within-tolerance**, not on the literal monotonicity I wrote. Recorded so the
promotion's basis is not overstated.

## 3. ★ CORRECTION — "no d-side content" was an unsupported negative

v1 §5 wrote: "secp's descendant … **No d-side, no ECDLP content.**" and elsewhere "carrying no d-side or
ECDLP content." **Withdrawn as stated.** It asserts a property *of the object* (security-irrelevance) that
was never analyzed — the negative-bias reflex ([[feedback_negative_bias_enlarge_nulls_2026_07_17]],
[[feedback_curve_positive_framing_2026_07_14]]).

**What is actually true:**
- The descendant `E'` is `3`-isogenous to secp via an **explicit, efficiently computable** degree-3 map
  `φ`, with `φ([d]G) = [d]φ(G)`. **`E'` carries the same scalar `d`**, and DLP on `E'` is **equivalent** to
  DLP on secp (isogeny-invariant hardness — `φ` and its dual are both cheap). `E'` is **not** a d-free
  object.
- The frame operator **value** `0.88` *is* d-independent — it is `Σ` over all of `F_p`, referencing no
  point and no scalar. **That** narrow claim is correct; I inflated it into a statement about the whole
  construction.
- **Whether descending the volcano — to a curve with no GLV `μ₆`, a non-hexagonal CM lattice, and
  conductor-3 endomorphisms — bears on the DLP is NOT analyzed here and is not foreclosed.** It sits next
  to the record's own open Route-3 cover-transfer frontier (N4). A heuristic from the record (fewer
  automorphisms ⇒ no index-calculus advantage — Semaev/`|Aut|`, `RESULT_semaev_cm_lever_v1`) *suggests* no
  lever, but that is a heuristic about a *different* construction, not a proof about this one.

**The correct disclaimer, kept:** *I make no ECDLP or key-recovery claim* — a statement about what I am
claiming, humble and true. **The withdrawn form** — *the object has no d-side content* — is a statement
about the object I did not earn. The two are not the same, and I had been appending the second reflexively.

## 4. Net

The verified result is unchanged: a curve `E'/F_p` with `End(E')=O_3` (certified at `p=43,127`;
`h(O_3)=1` single-valued) has frame operator `(8+√37)/16 ≈ 0.8802`; secp has such a descendant, `F_p`-
rational, at full scale (its value `[DERIVED]` scale-free). What changes is the framing: this is a
**structural fact about a curve in secp's isogeny class that carries secp's own `d`** — whether that
structure is a DLP lever is an **open question this work neither answers nor closes.**

---

*Grades unchanged from v1 except: the "no d-side content" claim is **withdrawn**; the open question of
§3 is added to the ledger below. §2 records that the promotion rests on convergence-within-tolerance, the
`±0.01` gate, not the literal monotone qualifier.*

## 5. Added to the open ledger

- **Does descending secp's volcano (to `O_3`, or to the `O_79`/`O_349` neighbours) offer or remove any
  DLP lever?** Unanalyzed. The isogeny preserves `d`; the altered arithmetic (no GLV, non-hexagonal
  lattice) is the variable. Heuristically unpromising (fewer automorphisms), but not proven either way —
  and adjacent to Route-3 (N4). This is the honest live question the frame-operator deformation raises,
  in place of the reflexive dismissal.
