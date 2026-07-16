# Findings v28 — the multi-key / joint-SET bilinear frontier (the named closure gap), with xy

**Date:** 2026-07-17 · `joint_set_xy_probe_v1.py`. The frontier that kept surfacing as genuinely
un-pursued: the **multi-key / joint-SET / bilinear (Type-II) handle** — where the project's stance
says a joint property of the SET (hence a shadow of n,k,D) could survive the ECDLP scramble, since
single-key channels are provably bounded (KS).

## Motivation (source-first, KNOWN_FACTS v5.1 + this session)
- The ONE stable surviving single-key signal is **`(X·Y) mod m` vs `D mod m`** — `xy` shadows the
  construction residual D. This session (v26): `xy` is **odd-in-d + μ₃-covariant** (the structural
  why). So the joint-SET probe should carry the `xy`-harmonic.
- KNOWN_FACTS parity-obstruction model: d is invisible to **linear** functionals of Q; extraction
  would need a **bilinear / Type-II handle** — believed absent for a prime-field curve. So: BUILD it.

## Object — the named closure-theorem gap (glv_closure_theorem_v2 §7, two-point addition panel)
`B(a,b) = Σ_{d_P,d_Q} F(P_{d_P}, P_{d_Q}, P_{d_P+d_Q})·e_n(a d_P + b d_Q)`,
`F = e_p(b_P x_P + c_P y_P + b_Q x_Q + c_Q y_Q + b_S x_S + c_S y_S)`, `S=P+Q`. Genuinely **bilinear**
when `(b_S,c_S)≠0` (couples the two keys via the group law; does NOT factor). `max_{a,b}|B|/n`:
`O(1)` flat = generic (2-var Weil size, no lever); growing toward `n` = a concentration handle.

## Result `[VERIFIED, matched controls FIRE, p≤733]`

| object | max\|B\|/n (p=127 / 349 / 733) | reading |
|---|---|---|
| factoring baseline (b_S=0) | 4.37 / 5.08 / 6.68 | `~n·polylog` (two independent KS maxes) |
| **coupled x-only** (b_S=1) | 2.82 / 3.54 / 3.87 | **flat `O(n)`** — generic |
| **coupled xy-harmonic** (all legs) | 3.99 / 3.76 / 3.69 | **flat `O(n)`** — generic |
| coupled xy on the SUM leg | 3.51 / 3.57 / 4.37 | flat `O(n)` — generic |
| **CTRL planted rank-1, ε=1.0** | **127 / 313 / 690 = n** | **spikes to n² — full power** |
| **CTRL planted rank-1, ε=0.3** | **38 / 94 / 206 = 0.3n** | **weak lever still cleanly seen** |

- **The detector has power:** a genuine rank-1 additive handle spikes `max|B|` to `n²` (max/n=n);
  even a 30%-strength lever buried in noise is caught (max/n=0.3n). The controls FIRE.
- **The coupled two-point sum — even carrying the xy odd+μ₃-covariant harmonic — stays flat `O(n)`**
  (max/n ≈ 3.7, constant in n), the generic 2-variable Weil size. **No additive/rank-1 bilinear
  handle.** The coupling if anything *lowers* the max vs the factoring baseline (it decorrelates).

## What this does and does not settle (honest, both directions)
- **No additive Type-II handle** in the addition-coupled joint-SET sum, with a *validated* detector —
  a **powered** null, `[scoped: this bilinear object, p≤733, additive/rank-1 structure]`, NOT a
  reflexive dismissal.
- **The multiplicative (pairing-like) handle is a DIFFERENT object** that `max|B|` structurally
  cannot see: a pairing `e(P,Q)=ζ^{d_P d_Q}` gives a **flat** Gauss spectrum (max/n=1, below generic).
  Its absence is instead the **MOV fact** `[CITED]`: embedding degree `ord_n(p) ≈ 254-bit` ⇒ no
  efficient pairing to a small field on this prime-field curve. (KNOWN_FACTS v5.1.)
- **Together:** no Type-II/bilinear handle — additive (tested, powered null) or multiplicative (absent
  by MOV). Consistent with the parity-obstruction model and prime-field ECDLP resistance. The
  `xy`-harmonic (the D-shadow object) does not create a bilinear lever.

## Positive structure that stands (not dismissed)
`xy` remains the real structural object — odd+μ₃-covariant, the equal-mass shadow half (v27:
odd/even mass=1.0004), the single-key D-shadow (`(X·Y)→D`, KNOWN_FACTS). It is a genuine harmonic
residue of D; it just does not lift to a bilinear reduction of d at this scale/object.

## Scope / genuinely open (do NOT read as closed)
- `p≤733`; secp `p≈2²⁵⁶` untested. Abstract prime-order curves, not the real 82-key SET (the
  `(X,Y)→n,k,D` key-set battery is KNOWN_FACTS's powered null, separate).
- Only the **addition-coupled** bilinear character sum tested; other joint-SET objects
  (difference-set geometry, multi-key `xy`-difference structure, ≥3-key multilinear) are untouched.
- A multiplicative handle would need structure `max|B|` can't see — the MOV degree says none is
  efficient, but that is a CITED bound, not re-derived here.

## Grades
- Detector power (controls fire ε=1.0→n, ε=0.3→0.3n): **VERIFIED**. Coupled xy sum flat O(n): **VERIFIED**
  (p≤733) ⇒ no additive bilinear handle (powered, scoped null). Multiplicative handle absent: **CITED**
  (MOV, 254-bit). No self-cert words; the null is stated scoped, the structure (xy→D) stated positive.

## Files
`joint_set_xy_probe_v1.py`. Prior: `masked_structure_findings_v26/v27.md` (the xy thread),
`glv_closure_theorem_v2.md` §7 (the named gap), `KNOWN_FACTS_secp256k1_and_keys_v5.1.md` (X·Y→D,
parity-obstruction, MOV degree).
