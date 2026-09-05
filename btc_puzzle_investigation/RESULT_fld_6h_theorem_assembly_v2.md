# RESULT v2 — `|FLD|=6h(−p)`: the (†) route proves it for the *cent/ρ-flap*; transfer to the
# reduced-basis FLD rests on ONE unproven cross-construction identity. **v1's `[PROVED]` was an overclaim.**

*2026-08-08. Supersedes `RESULT_fld_6h_theorem_assembly_v1.md` (kept as the audit trail; its `[PROVED]`
grade and its "link 3 = P1 Step 1" claim are **corrected here**). Grade now:
`|FLD|=6h` is `[PROVED — modulo the flap-equivalence bridge (B), verified 194/194, not proved]`.
No leakage / ECDLP claim.*

---

## 0. What the audit changed

v1 concluded `|FLD|=6h` is `[PROVED]`, on the strength of six links each graded `[PROVED]`. An adversarial
self-audit (`fld_audit_v3.py`, `fld_reconcile_v1.py`) found **one link mis-graded**:

- v1 link 3 said *"geometric flap = arithmetic window `[PROVED via P1 Step 1]`."*
- **P1 Step 1 (flap-lemmas v2) proves `cent-window == ρ-window` — an identity INTERNAL to the
  flap-lemmas' own cent-based construction** (verified here **194/194**). It says nothing about the
  master's FLD, whose σ is the **reduced-basis** flap `sign(u−v)`, a *different* construction.
- **The two flap SETS are not equal** (`cent-flap == reduced-basis-flap`: **12/194**; `ρ-window ==
  reduced-basis-flap`: 12/194). What the assembly actually needs is a **cross-construction
  character-sum identity** (B, below), which holds numerically **194/194** but is **not proved**.

So v1 silently assumed the flap-lemmas object and the master's FLD are the same set. They are not.
(The earlier audit scripts `_v1/_v2` compounded this with a bug — they recomputed σ as raw `sign(u−v)`
and ignored that `sigma_fn` selects orientation `−` OR `+` by a preflight; `+` occurs for ~half the
primes. Using the authoritative σ, `fld_reconcile_v1.py` confirms σ **is** odd, `FLD=2S+`,
`Σ_flap χ₂=0`, all 72/72 — so the mechanics are sound; only the set-identity claim was wrong.)

## 1. What is genuinely proved (unchanged from v1, re-verified with authoritative σ)

For the **flap-lemmas' object** `S′ := Σ_{s∈T⁺}χ₂(s)`, `T⁺` = ρ-window `{s∈[1,H]: ρs mod p ∈
[(p+1)/2, H+s]}`, on `p≡7 mod12`:

| link | grade | source |
|---|---|---|
| `S′ = A + C`, `C+C′ = A` | `[PROVED]` | flap-lemmas v3 §1 |
| `A = Σ_{[1,H]}χ₂ = (2−χ₂(2))h` | `[PROVED / CITED Dirichlet]` | flap-lemmas v3 §2; review re-derived `h=−(1/p)Σχ₂(a)a` |
| `(†) C′−C = 3h` | `[PROVED — reviewed]` | `RESULT_fld_dagger_proof_v1.md`, `REVIEW_twisted_dedekind_v1.md` |
| ⇒ `S′ = (3h/2)(1−χ₂(2))` | `[PROVED]` (assembly) | here |
| ⇒ `|2S′| = 6h` at `p≡19 mod24`, `0` else | `[PROVED]` | here |
| corollary `|S′| = F4` (this is L1, on the ρ-window object) | `[PROVED — corollary]` | here |

**These stand.** The dagger route genuinely closes the class-number law **for the ρ-window/cent flap**,
with **no** appeal to L1, and it makes the master's named lemma L1 a corollary *on that object*.
The ledger's item 16 ("(†) still open, needs Rademacher") remains **stale** — that finding is unaffected.

## 2. The one unproven link — the flap-equivalence bridge (B)

The master's `FLD = Σ_x σ(x)χ₂(x)` uses the **reduced-basis** σ. Writing `signed := Σ_{s∈[1,H]} σ(s)χ₂(s)`
(so `FLD = 2·signed`, from σ odd + χ₂ odd, **194/194**):

> **(B)  `|signed| = |S′|`** — i.e. `|Σ_{s∈[1,H]} σ(s)χ₂(s)| = |Σ_{s∈ρ-window} χ₂(s)|`.

- **Verified 194/194** (`p≡7 mod12`, `p<6000`); signed-equality (not just magnitude) holds 151/194,
  the 43 sign flips tracking the `sigma_fn` orientation split (`−`/`+`).
- **Not proved.** The two index sets differ (symmetric difference 20–90 elements); (B) is an identity
  between χ₂-sums over two *different* flap constructions, not a set identity.
- **Consequence:** `|FLD| = 2|signed| = 2|S′| = 6h` **iff (B)**. So `|FLD|=6h` is
  `[PROVED modulo (B)]`, everything else discharged.

**The "single open step" has moved a third time:** `(†)` (proved) → `L1` (corollary) → **(B)**, a
genuinely new object — a character-sum equivalence of two lattice flap constructions.

## 3. Exact status of every check (authoritative σ, `p≡7 mod12`, `p<6000`, 194 primes)

| statement | result |
|---|---|
| σ odd; `FLD = 2·signed`; `Σ_flap χ₂ = 0` | 72/72 (to `p<2000`, `fld_reconcile_v1`) |
| `A=(2−χ₂(2))h`; `C+C′=A`; `(†) C′−C=3h`; `S′=(3h/2)(1−χ₂(2))` | 246/246 (to `p<8000`, `fld_6h_assembly_check_v1`) |
| `|FLD|=6h @ p≡19 mod24`; `FLD=0` off it | 122/122; 362/362 |
| P1 Step 1 `cent-window == ρ-window` (internal) | 194/194 |
| **cent-flap / ρ-window == reduced-basis flap (SET)** | **12/194** (they differ) |
| **(B) `|signed| = |S′|`** | **194/194 — verified, NOT proved** |
| `h(−p)` vs 20 known values | 20/20 |
| `sigma_fn` skips (selection bias) | 0 |

## 4. Corrected grade and the honest ledger

- **`|FLD| = 6·h(−p)` (M11): `[PROVED — modulo (B); (B) verified 194/194, not proved]`.** Not
  `[PROVED]`. Still a real advance: the remaining gap is (B), a specific character-sum identity — **not**
  L1 and **not** "(†) needs Rademacher."
- **`(†)`: `[PROVED]`** (dagger, reviewed). Ledger item 16 stale — unchanged from v1.
- **L1: `[PROVED — corollary of (†)]` on the ρ-window object**; it is not the FLD blocker.
- **The FLD blocker is now (B)**, which no current document names.
- **Sign of FLD**: still open, and now visibly the *same* phenomenon as the (B) sign split (§2).

## 5. Reproduction
```
python3 fld_6h_assembly_check_v1.py 100 8000     # the proved chain on the ρ-window object
python3 fld_reconcile_v1.py       100 2000       # σ odd, FLD=2S+, |S+|=|S′|, authoritative σ
python3 fld_audit_v3.py           100 6000       # (B), and cent/ρ-flap != reduced-basis flap
```
(all three scripts in the investigation dir; exact `int`/`Fraction` only.)
