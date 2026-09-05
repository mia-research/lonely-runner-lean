# ANALYSIS — N4 / Route 3: the cover FAMILY vs known index calculus over F_p

**Grade slot: `[PROVISIONAL — citation-verifier unavailable]`.** Date 2026-08-04.
Object: the family of covers `C → E` of secp256k1's `E/F_p` (`p` prime, ~256-bit),
and whether any member yields a KNOWN index-calculus DLP solver faster than Pollard's
`O(√p)` for the order-`p` E-instance. Extends master v4 §VII.3 / §XI.13 (N4), which had
only the single cover `C: w⁴=x³+7` at `O(p^{4/3})`.

**No grade is promoted by this note** (§2a condition 4). The master-ledger move on N4
is HELD until the isolated citation-verifier clears the frame layer named below.

---

## 1. Gate status (§2a — UNAVAILABLE, not FAILED)

The mandatory citation-verifier (CLAUDE.md §2) was spawned 2026-08-04 and terminated by
an **account session limit** (API error, resets ~17:20 Australia/Brisbane) before
emitting a report. It reported **no defect** — it could not run to completion. Per §2a
this is the *gate-unavailable* branch: provisional work may proceed under the four
conditions; the standing precedent (*a run that did not complete did not pass*) holds.

**Owed (§2a condition 3):** re-run the ISOLATED citation-verifier after the reset, on
CLAIM 4 + the quasi-subfield residual + Diem [18]'s exact plane-curve hypotheses (§4).

## 2. Source-verified MECHANICAL facts (self-audit sufficient per §2a table, artifact = the source)

Primary source read directly: **A. Enge, "Discrete logarithms in curves over finite
fields," arXiv:0712.3916, §2.6 "The low genus case," pp. 12–13.** (This is Enge's
SURVEY; the master's URL association of 0712.3916 with "Diem" was imprecise.)

- **F1 `[CITED — GTTD 2007 [35] + Nagao [55]; verified vs Enge §2.6]`.** Genus-`g`
  Jacobian index calculus runs in `O(q^{2−2/g})` arithmetic ops, regime **`g` fixed,
  `q→∞`**, via the two-large-prime variation. Beats the generic `q^{g/2}` **for `g≥3`**.
  Formulated for hyperelliptic curves but *"carries over to arbitrary curves"* (Enge
  p.13); the arbitrary/plane-curve instance is **Diem [18]** — so `[CITED — Diem]` is
  defensible for our non-hyperelliptic plane cover, but the *exponent* traces to [35]/[55].
- **F2 `[CITED — verified]`.** `g=3 ⇒ O(q^{4/3})`. Enge states genus-3 needs +12.5% bit
  length for security parity ⇒ the cited `O(p^{4/3})` for `C: w⁴=x³+7` is correct.
- **F3 `[CITED — Enge §2.6, verified]`.** **Genus 1 (elliptic) index calculus is SLOWER
  than the generic `O(√q)`** (the discreteness-of-`B` obstruction). So no genus-1 cover
  helps; the elliptic instance's best is Pollard `O(√p)`.
- **F4 `[PROVED — arithmetic over F1/F3]`.** `2−2/g` is increasing in `g`; for all `g≥2`,
  `O(p^{2−2/g}) ≥ O(p) > O(√p)`. Growing `g` (fixed `p`) → `O(p²)`, worse. The `L(1/2)`
  subexponential (Enge §2.4, ADH [3]) needs `g→∞` vs `log q` with the DLP modulus = group
  size `q^g`; a fixed order-`p` target over a prime field cannot supply that parameter.

**⇒ Family arithmetic (mechanical, source-backed):** across the whole genus range, the
minimum cost to solve the order-`p` E-instance by KNOWN index calculus is Pollard's
`O(√p)` at `g=1`; every `g≥2` cover is `≥ O(p)`. **No cover in the family provides an
index-calculus speedup over Pollard.** This is a statement about the genus/field tradeoff
of KNOWN algorithms over a prime field — scoped exactly as written, not a security claim.

## 3. The residual = the LIVE LEVER (positive framing; NOT a closed door)

The KNOWN cover/higher-genus route offering no advantage over `F_p` *sharpens where any
prime-field ECDLP lever must live*. Two named, live directions — neither secp-specific,
both shared by every prime-field curve:

- **R1 — prime-field-native point-decomposition / Semaev-summation index calculus.**
  Our own §XI.4 measurement (`RESULT_semaev_cm_lever_v1.md`): first-fall degree is a
  leading-form invariant, curve-independent `[PROVED, all m]`; matched first-fall AND
  solving degree identical CM vs non-CM `[VERIFIED, p≤307, m≤4]` — no curve-specific
  collapse for secp's curve. **OPEN:** `m≥5`, large `p`, whether prime-field Semaev IC
  ever beats `√p` (a general open problem; first-fall degree grows with `m`).
- **R2 — quasi-subfield polynomials** (Huang–Kosters–Petit–Yeo–Yun, JMC 2020): proposed
  as an index-calculus lever; follow-up (Euler–Petit) reportedly derives **no speedup**
  over prior approaches. Status "proposed lever, no speedup found," **not closed** — and
  the prime-field-specific comparison was NOT settled in the sources read here. → gate.
- **R3 — a hypothetical genus-`g` algorithm below the GTTD/Nagao exponent**, or a
  non-index-calculus transfer. Not excluded; an open problem for ALL prime-field ECDLP.

## 4. Self-audit — what this note does NOT cover (§2a condition 2)

**FRAME layer (isolation needed; my inline read cannot discharge it; my documented
suppression bias runs toward over-closing here):**
- **CLAIM 4 unverified from primary source.** The framing "cover/Weil-descent needs a
  proper subfield ⇒ a prime field blocks it across the family" is standard lore and is
  *consistent* with F1–F4, but I did NOT retrieve the explicit prime-field-exclusion
  scope statement from a primary source (Enge p.4 confirms Weil descent as a *mechanism*
  only). The family conclusion in §2 rests on the genus/field arithmetic (F1–F4), which
  IS source-backed; the additional "no-subfield" narrative is not yet primary-verified.
- **R2 quasi-subfield status** is from a search summary, not the primary Euler–Petit text.
- **Bias check:** §2/§3 must be read as "known higher-genus cover route = no advantage
  over F_p," NOT "N4 closed." R1–R3 are live. Language rules obeyed: no
  secure/closure/proven-hard/dead.

**MECHANICAL layer (discharged, artifact = Enge §2.6):** F1–F4 above.

## 5. Disposition

- N4 stays **`[OPEN]`** in the master ledger. Do NOT edit the ledger grade until the gate
  clears.
- On gate clear: fold F1–F4 (source-verified) + a gate-cleared CLAIM 4 + R2 status into a
  master successor, upgrading N4's *characterization* (family, not one cover) while
  keeping the residual R1–R3 as the live frontier.
- Cross-links: `RESULT_semaev_cm_lever_v1.md` (R1, §XI.4); master v4 §VII.3, §XI.13.
