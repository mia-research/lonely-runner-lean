# ANALYSIS — N4 / Route 3: the cover FAMILY vs known index calculus over F_p (FINAL)

**Supersedes the provisional `ANALYSIS_n4_cover_family_indexcalculus_provisional_v1.md`.**
Date 2026-08-05. Gate CLEARED (citation-verifier, fresh isolated run) — v1's four
`[PROVISIONAL — citation-verifier unavailable]` items are now primary-source verified,
**with four material deltas / corrections that v1 did not have.**

Object: the family of covers `C → E` of secp256k1's `E/F_p` (`p` prime, ~256-bit), and
whether any member yields a KNOWN index-calculus DLP solver faster than Pollard's `O(√p)`
for the order-`p` E-instance. Extends master v4 §VII.3 / §XI.13 (N4).

> **Scope banner (governs every line).** This maps the genus/field tradeoff of KNOWN
> algorithms over a prime field. It is **not** a security claim; the words secure /
> closure / proven-hard / dead are not used. Every statement is "no *known* algorithm of
> class X beats `√p` here," with its power and scope, and the residual (R1–R3, §3) stays
> live.

## 1. Gate provenance

Fresh isolated citation-verifier, primary PDFs read directly (SHA-256 recorded, in session
scratchpad): Diem *On the DLP in elliptic curves* (Compositio 147, 2011); Diem *An Index
Calculus Algorithm for Plane Curves of Small Degree* (ANTS VII, LNCS 4076, 2006); Diem
*The GHS Attack in odd Characteristic* (JRMS 18, 2003); Huang–Kosters–Petit–Yeo–Yun
*Quasi-subfield Polynomials and the ECDLP* (J. Math. Cryptol. 14 (2020) 25–38, DOI
10.1515/jmc-2015-0049); Euler–Petit *New Results on Quasi-Subfield Polynomials*
(arXiv:1909.11326); Gaudry (eprint 2004/073) and Joux–Vitse (eprint 2011/020) abstracts.

## 2. Source-verified characterization

### 2a. The genus/field arithmetic `[CITED — verified]`
- Genus-`g` Jacobian index calculus: **`Õ(q^{2−2/g})`**, `g` fixed, `q→∞` (GTTD 2007;
  Nagao). Beats generic `q^{g/2}` for `g≥3`. Genus 1 (elliptic): index calculus is
  **slower** than generic `O(√q)`. (Enge survey arXiv:0712.3916 §2.6, verified last turn.)
- `2−2/g` is increasing in `g` ⇒ for all `g≥2`, `Õ(p^{2−2/g}) ≥ Õ(p) > O(√p)`; growing
  `g` (fixed `p`) → `Õ(p²)`, worse. Diem's **subexponential** regime (Compositio 2011) is
  `F_{q^n}` with `n→∞` in explicit windows (`n ≈ √log q`); at `n=1` (prime field) the main
  theorem gives `e^{O(log q)}` — exponential, never sub-`√p`. `[PROP A — SUPPORTED]`
  *(Care: Diem's "prime powers `q_i`" = `F_{p^{n_i}}` extension fields, NOT prime fields.)*
- **⇒ Family minimum** to solve the order-`p` E-instance by known index calculus is
  Pollard's `O(√p)` (at `g=1`); every `g≥2` cover is `≥ Õ(p)`. **No cover in the family
  provides an index-calculus speedup over Pollard.** `[PROVED — arithmetic over the cited exponents]`

### 2b. Our specific cover — exponent refined `[PROVED structure + CITED bound]`
`C: w⁴=x³+7` is **bielliptic**: `w↦−w` has elliptic quotient `C/⟨w↦−w⟩ = E` (`u=w²`,
`u²=x³+7`). Bielliptic genus-3 ⇒ **non-hyperelliptic** ⇒ smooth plane quartic (`d=4`).
Hence:
- **Heuristic `Õ(p)`** — Diem 2006's plane-model bound `Õ(q^{2−2/(d−2)})`, `d=4` ⇒ `Õ(q)`
  (his own genus-3-quartic example). `[CITED — Diem 2006, explicitly HEURISTIC, "almost all" instances]`
- **Provable `Õ(p^{4/3})`** — the GTTD-variant `Õ(q^{2−2/g})`, `g=3`, needs a **cyclic**
  degree-0 class group + bounded-degree plane model. `[CITED — verified]`

Both `> √p`. **This refines the master's flat `Õ(p^{4/3})`:** the sharper (heuristic) figure
for this cover is `Õ(p)`; the family conclusion (no speedup over `√p`) is unchanged.

### 2c. The subfield obstruction — corrected scope `[PROP B — SUPPORTED, with 2 caveats]`
GHS / Weil descent / Gaudry decomposition / Joux–Vitse cover-and-decomposition **all
require a proper subfield `F_q ⊊ F_{q^n}` (`n≥2`)** — primary-confirmed. A prime field has
no proper subfield, so none of these named attacks has an input. **Two corrections v1 got wrong:**
- **NOT "no index calculus over `F_p`."** Prime-field-native Semaev point-decomposition
  index calculus **exists** (Petit–Kosters–Messeng 2016; Amadori–Pintore–Sala,
  eprint 2017/609). It yields **no known advantage** over `√p`, and is not proven to beat
  generic — but it runs. The sharp statement is *"no subfield-exploiting cover/descent
  over `F_p`,"* not *"no index calculus over `F_p`."* (v1 mis-cited 2017/609 as a survey
  supporting exclusion; it is in fact a paper **proposing** a prime-field Semaev algorithm.)
- **Special prime-field classes ARE sub-`√p`** (stated plainly): supersingular curves via
  MOV/Frey–Rück pairing → subexponential (Diem 2011 intro); anomalous `#E=p` via SSSA/Smart
  (marked CANNOT-VERIFY by the gate — primary not pulled; n/a below). **secp256k1 is
  ordinary with large embedding degree** (`ord_n(p)=(n−1)/6`, 254-bit; master §VII.3 route
  1) ⇒ **outside both classes.** So 2a–2c is for *general ordinary large-embedding-degree*
  prime-field curves like secp — not a blanket "all prime fields" claim.

## 3. Residual = the LIVE LEVER (positive framing)

- **R1 — prime-field-native Semaev / point-decomposition index calculus.** This is the
  lever, and it is real (it runs over `F_p`; §2c). Current evidence of no advantage is
  scoped: our §XI.4 `RESULT_semaev_cm_lever_v1.md` — first-fall degree curve-independent
  `[PROVED, all m]`; matched first-fall + solving degree identical CM vs non-CM
  `[VERIFIED, p≤307, m≤4]`. **OPEN:** `m≥5`, larger `p`, whether prime-field Semaev IC ever
  beats `√p` (a general open problem; first-fall degree grows with `m`). **→ target B.**
- **R2 — quasi-subfield polynomials.** `[PROP C — SUPPORTED]` QSPs are defined **only over
  extension fields** (`L(X)=X^{p^{n'}}−λ(X) ∈ F_{p^n}[X]`, `n>1`); HKPYY prove only that
  they beat *exhaustive search* `O(N)`, not generic `O(√N)`; Euler–Petit derive **no
  speedup**. **Not a prime-field lever** (downgrade from v1, which over-listed it as one).
- **R3 — a hypothetical genus-`g` algorithm below the GTTD/Nagao exponent**, or a
  non-index-calculus transfer. Not excluded; an open problem for ALL prime-field ECDLP.

## 4. Self-audit — what remains OPEN

- R1 (prime-field Semaev at `m≥5` / large `p`) and R3 are live; **not closed.** The §2
  statement is "no *known* sub-`√p` cover/descent for ordinary large-embedding-degree
  prime-field curves," per the banner.
- The anomalous `#E=p` (SSSA) sub-`√p` fact is CANNOT-VERIFY here (primary not pulled);
  it does not bear on secp (ordinary), but the general "special classes exist" point stands.
- Diem 2006's `Õ(p)` for the quartic is **heuristic**; the provable figure is `Õ(p^{4/3})`.
- Bias note: §2 caught two v1 slips (2017/609 direction; "no IC over F_p"). Both ran toward
  over-closing — the documented one-way suppression direction. The isolated gate, not an
  inline reread, caught them.

## 5. Disposition — N4 grade move

- **N4 upgrades** from "one cover, `Õ(p^{4/3})`, family OPEN" → **"cover family: no known
  index-calculus speedup over `O(√p)` for the order-`p` E-instance of an ordinary
  large-embedding-degree curve over `F_p`; subfield-exploiting cover/descent has no input
  over a prime field (GHS/Gaudry/Joux–Vitse); residual R1/R3 OPEN = the live lever."**
  Our cover: heuristic `Õ(p)` / provable `Õ(p^{4/3})`.
- **Master-ledger reconciliation (v5, compile-diff-gated) is OWED** — batched with target
  B's forthcoming R1 result rather than a one-item v5, per the project's batch-consolidation
  pattern. This ANALYSIS v2 is the standing N4 artifact until then.
- Cross-links: `RESULT_semaev_cm_lever_v1.md` (R1); master v4 §VII.3, §XI.13; provisional v1.
