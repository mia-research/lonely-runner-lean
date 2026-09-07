# Translating the n=11 AP route to n=8 — the structural difference, and what it makes possible

2026-09-08. The n=11 **AP paper** (`lrc_n11_ap_paper_v30.md`) is a different route from the
fine-cell / prime machinery, and it is the one worth translating. Exact rational arithmetic
throughout (`experiments/n8/pacemaker_n8_v1.py`, written by the earlier session); no float.

## 1. The route, and where it stops being an AP argument

`lrc_n11_ap_paper_v30.md` splits three ways:

- **Bounded ratio `e₁₀/e₁ ≤ 10`** (§3.1). One line: `t* = 10/(11e₁₀)` gives
  `1/11 ≤ e_i t* ≤ 10/11` for every `i`. **Translates verbatim to n=8**: `t* = 7/(8e₇)`
  works whenever `e₇/e₁ ≤ 7`. This is Theorem 6.1 of our general-`n` manuscript; we own it.
- **Irrational ratio** (§3.2). Kronecker closure. No primality; should translate.
- **Large ratio** — the essential case, and where **the AP witness family is abandoned**.
  §3.3 is explicit, with Example 3.1 exhibiting a configuration that blocks all ten AP
  witnesses `{m/11}` while `t = 4/17` is a valid witness. The paper then switches to the
  window `W_ref = [1/(11e₁), 10/(11e₁)]` and the pacemaker slots.

**Why the switch comes sooner at n=8.** The AP witness family has `φ(n)` usable members. At
`n = 11` that is `φ(11) = 10`, one per runner — exactly tight. At `n = 8` it is `φ(8) = 4`
against 7 runners. So the AP witnesses run out at `n = 8` earlier and harder, which is the
same `(ℤ/8)ˣ` fact recorded elsewhere, seen from the AP side.

## 2. The slot architecture does translate — and the counts are general

`n−2` pacemaker slots against `n−3` free runners, surplus exactly 1, at every `n`
(9 v 8 at `n = 11`; 6 v 5 at `n = 8`). Instantiated at `n = 8`: `a_i = 7e_i/e₇`, `a₇ = 7`,
`B_{j,k} = [(8k+7)/(8a_j), (8k+9)/(8a_j)]`, `I_s = [(8s+1)/56, (8s+7)/56]`,
`W_ref = [1/(8a₁), 7/(8a₁)]`.

## 3. The structural difference, computed exactly  `[PROVED — deterministic exact evaluation]`

AP limit `a_j = j`, `W_ref = [7/56, 49/56]`, units of `1/56`:

| slot | witness | covering chain | tight-touch owners | chain overlaps |
|---|---|---|---|---|
| `I₁ [9,15]` | `1/4` | `r6, r5, r4` | **none — unclaimed** | `7/10`, `7/20` |
| `I₂ [17,23]` | `3/8` | `r3, r6, r5` | `{3,5}` | `7/2`, **`0`** |
| `I₃ [25,31]` | `1/2` | `r2, r4, r6` | **none — unclaimed** | `19/4`, `25/6` |
| `I₄ [33,39]` | `5/8` | `r5, r3, r6` | `{3,5}` | **`0`**, `17/6` |
| `I₅ [41,47]` | `3/4` | `r4, r5, r6` | **none — unclaimed** | `7/20`, `7/10` |
| `I₆ [49,55]` | `7/8` | — | empty in `W_ref` at `a₁ = 1` |

> **At `n = 11` all eight interior slots are covered with a single touching point each — the
> configuration is critically braced, and the complementary-pair table is the bookkeeping
> that tracks which pair owns which touch. At `n = 8` only two of six slots are braced
> (`I₂`, `I₄`, both owned by the pair `(3,5)`); the other three are covered with strictly
> positive overlap.**

That is the real difference, and it is the opposite of a deficiency. `n = 8` has **slack**
where `n = 11` has none. The three unclaimed slots are exactly the even-witness ones —
`1/4, 1/2, 3/4`, where `gcd(m,8) > 1` so no runner sits at a boundary — and the overlaps are
explicit rationals, not an asymptotic.

## 4. What this makes possible, and it is not Rosenfeld's computation

Complete blocking requires **every** slot closed. The Coupling Principle transfers verbatim
(`N11_TRANSLATION_v2.md` §2): each runner's bad intervals are a rigid arithmetic progression
scaling as `1/a_j`, so a slot cannot be closed in isolation — positioning one interval fixes
the whole chain. Hence the target:

> **Show that consuming the slack in `I₁, I₃, I₅` — while keeping the braced slots `I₂, I₄`
> closed and closing `I₆` — is impossible.**

This is the shape of the n=11 argument's Cases A–D (`lrc_n11_algebraic_lemma_v1.md` §6),
which closes a sign class by resonance-plus-coupling and an explicit incompatibility, **and
it needs no complementary-pair table.** What it needs is the overlap budget, which §3 above
supplies as a finite list of exact rationals.

**Why this is on-task.** It consumes the AP route's own machinery (coupling, slots, `W_ref`),
targets the extremal configuration rather than excluding it, and produces a witness rather
than a divisibility certificate. It is a translation of a proof, not a re-run of a search.

## 5. Status and what is not claimed

`[PROVED]` the bounded-ratio witness at `n = 8`; the slot/`W_ref` instantiation and the
AP-limit table above. `[CITED]` the n=11 route it translates. **No claim** that the
large-ratio case at `n = 8` is closed, or that the slack cannot be consumed — that is the
target, untested. Known obstacles already on file: v33's `GF > 0` target is false at `n = 8`
(two collision-type tight instances have `GF = 0` in every slot), and the naive sign-range
box `a_j ∈ (j−1, j+1)` fails on the same two. Both live in the large-ratio regime, so an
argument here must handle them, and the ladder already settles them (`8 ∤ v` ⟹ `t = r/8`).

`n = 8` is not proved. Rosenfeld's ledger is untouched and irrelevant to this line.
