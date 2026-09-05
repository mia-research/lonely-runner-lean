# AUDIT — Memory Layer (v1)

**Final phase of the narrative-conclusion audit.** Target = the memory files read at the *start* of every session (`btc_puzzle_INDEX.md`, 3295 lines, + the closure-tagged secp topic memories). This is the highest-propagation conclusion: a memory that over-states a closure boots a false belief before any current document is consulted.

**Reference:** `POSITIVE_FINDINGS_MASTER_v9.md` (2026‑08‑11). **Method:** one isolated agent, memory-vs-v9 (and memory-vs-its-own-source), decidable quotes + lines, "clean is valid." **Staleness note:** most memories are dated ~2026‑07; v9 is 08‑11, so a "closed" memory can reflect a July belief the results later re-opened — and that is exactly the propagation risk, because the memory is read first.

---

## Result: 5 of 8 faithful, 3 firmer-than-v9

**FAITHFUL (5) — real closures, not nulls dressed as closures** *(the audit correctly passes these; it is not manufacturing):*
- `secp_amicable_transport_circular` (08‑13, postdates v9) — narrow single-point-transport circularity, exact CRT fact, explicitly scoped ("does NOT close the CM avenue / boundary C / D / the public‑ε route"). Consistent with v9 keeping the non-hom amicable map OPEN.
- `secp_bilinear_closure_scope_eps_readout` (08‑14) — *exemplary scoping-down*: re-grades the two ε nulls to EMPIRICAL and names the 2⁻¹²⁸ lift bound as OPEN. Agrees with v9.
- `secp256k1_bsd_tamagawa_resolved` — a settled theorem+computation (Rubin + exact L(1)/Ω), out of leakage scope; low mis-boot risk. *(Cites LMFDB 21168.ce2 — not web-verifiable here.)*
- `btc_puzzle_gect_debunked`, `btc_puzzle_tiny_curve_crt_debunked` — genuine *mechanical* debunks (demonstrated circularity; no small-subgroup factor ⇒ no Pohlig–Hellman; non-homomorphism; vₚ(t)=0). Math-dead, not statistical nulls. v9 does not resurrect them.

**FIRMER-THAN-v9 (3) — a startup read would mis-bootstrap:**

| # | Memory (verbatim + line) | v9 (verbatim + line) | Note |
|---|---|---|---|
| **M‑1 ★** | `secp_N2_supersingular_closed_2026_07_20` L11: "N2 … **CLOSED (2026‑07‑20): `A_new` is supersingular at secp, `[PROVED]`.**" | L296 (under "**A.3 Not established (open — not closed)**"): "verified 24/24 at small p, **not proved for dimension 2** … an **assumption** … load-bearing for §VII" | **FIRMER + STALE.** The highest-risk memory: read first, stamps `[PROVED]/CLOSED` on the exact dim‑2 gap that v9, P13, and §VII all hold OPEN. |
| M‑2 | `btc_puzzle_bilinear_closure_2026_07_17` L11/L23: "**analytical closure of the joint‑SET / bilinear / multilinear frontier** … **NO … handle EXISTS (not just 'not found')**" | §XI.7 L805: "→ **NARROWED** … **Open**: k growing with p; genuinely joint multi-key readouts; the full two-point panel" | headline over-closes; the memory's own 08‑14 addendum walks back only the ε class |
| M‑3 | `btc_puzzle_closure_theorem_2026_07_14` desc: "**Proved** … single-coordinate **lift** readouts … decorrelate" | L381: "eisx's grading defect set is exactly the flap … **ungraded**"; ε readouts re-graded EMPIRICAL by the 08‑14 memory | C1 (bounded-degree) FAITHFUL; the ε/lift-geometry over-reach is the firm |

---

## The standout — M‑1, and a memory-internal contradiction

`secp_N2_supersingular_closed` even hedges *inside itself* ("[PROVED — pending independent adversarial re-derivation]", L28) yet stamps **CLOSED/PROVED** in its headline — which is what a fast startup read takes. And the index *itself* contradicts it: `btc_puzzle_INDEX.md` L296–301 (its own GATE‑0b review) holds the same object at "`[PROVED — one independent review; two citation caveats open]`. **NOT flat `[PROVED]`**." So the memory layer disagrees with itself on N2: the standalone memory says CLOSED, the index says not-flat-proved, v9 says open. This is **H‑1** (from the live-leads map) realized where it does the most damage — first read.

## Index closure entries (Step 2)

- **I2 · 120° law** — index top-section (L256/L1112, dated 08‑03): "the 120° law is **a theorem**" `[PROVED]`. v9 (08‑09 audit, M21 L286): "**`[VERIFIED]`, not `[PROVED‑exact]`**" (one-sided modular route on 8/11 primes). **FIRMER + STALE** — the index never recorded its own downgrade. *(Matches the live-leads-map "overclaims to watch".)*
- **I4 · symmetry programme** — L1170/L1183: "**SYMMETRY PROGRAMME DEAD, EXHAUSTIVELY OVER F̄** … **Do NOT run another symmetry search — closed at grade.**" The index *self-corrects* at L1114: this over-closure "**hid [the #26 theorem] for five rounds**" because "exhaustive over F̄" was exhaustive over the wrong set (deg G=7 odd ⇒ 8 branch points, stabiliser order 4). **FIRMER-THAN-v9.** A full-context reader recovers via the later entry; a grep-level read of L1170/L1183 boots the false closure — *and its "do NOT search" directive would stop a session from re-finding the theorem it hid.*
- I1, I3, I5, I6 — FAITHFUL (tightly scoped closures, each naming an explicit open residue).

---

## What this phase adds to the owed list  *(logged, not fixed — per the standing choice)*

1. **`secp_N2_supersingular_closed` (M‑1)** — the single most damaging memory: a false closure, read first, on a load-bearing object. Owed a correction to match v9's open N2 (or deletion). Ties to **H‑1**.
2. **I4's "do NOT run another symmetry search — closed at grade"** — a *directive* born of an over-closure that already hid a theorem once. Owed removal/qualification, or it re-suppresses the same search.
3. **M‑2, M‑3, I2 (120°)** — firmer-than-v9 headlines owed a downgrade to match the current grades.

## What this phase does NOT say

The memory layer is *mostly disciplined*: 5 of 8 audited closures are faithful, two of them (the 08‑14 scope memories) are exemplary scoping-*down*, and the debunks are genuine dead ends v9 agrees are dead. The failure is **concentrated and nameable** — three stale/firmer closures plus two index entries — not a pervasive rot. Reporting it as "the memory is inflated" would itself be the over-collapse this audit exists to avoid.
