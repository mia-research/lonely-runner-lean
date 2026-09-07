# The general-`n` corpus has two lineages, and `n = 8` sits in a hole in the older one

2026-09-07. Written after being redirected from small-`n` reductions to the `n = 9…11`
and general-`n` corpus. Everything below is a quote from a file in this repository,
with line number, plus elementary arithmetic. No new mathematics is claimed.

## 1. There are two general-`n` architectures, and the canonical pointer names only one

| | `lrc_proof_v10_21.md` | `lrc_proof_allN_v11_8.md` |
|---|---|---|
| date | 2026-05-08 | 2026-05-27 |
| architecture | residue / floor-state: `Unit-Complete`, floor-reset events, `B_safe`, coset orphaning, `n = p²` (`N-PSQ-*`) programme | Weyl equidistribution: BSR 6.1 / LR 7.1 / DI 10.1 / DI-MOD 11.1, Theorem 5.2, fine cells |
| headline | **Theorem A proved for all squarefree `n` and all `n = p^k`, `k ≥ 3`** | conditional on Conjecture 5.2-H |
| sole open item | `n = p²`, `p ≥ 17` (actual speeds, unbounded `q_ρ`); squarefree `n = pq`, `n > 15`, actual speeds | Conjecture 5.2-H, which at `k_G + k_A = n−1` is **equivalent to LRC(`n`) itself** |

Token counts, whole file: `9.2c` — v10.21 **17**, v11.8 **0**. `Unit-Complete` — **21 / 0**.
`floor-reset` — **32 / 0**. `unit runner` — **19 / 0**. The v11 line is a **restart**,
not a revision: `lrc_proof_allN_v11_4.md:9` opens *"We prove the Lonely Runner
Conjecture for all $n \geq 3$"* and builds from four new theorems.

The v11 line already collapsed once. `lrc_whole_project_review_2026-04-18.md:14`:

> "| A — n=all Tier 1 (v11.2) | Tier 1 COMPLETE (2026-04-18) | **INCORRECT** | Lemma 2.5
> iff false (two counterexamples at n=5); Lemma 10.2 floor formula wrong for q_e≥1;
> Thm 8.2 L-bound false; Thm 11.1 Case A L-bound false. |"

and `:20`: *"The n=all proof is, at this writing, **not proven**."* The project then
rebuilt on v10.13 → v10.15 → v10.21.

**`CLAUDE.md` §8 and `memory/MEMORY.md` name `lrc_proof_allN_v11_8.md` canonical and
record "No active frontier."** Neither mentions the v10 lineage. That pointer hides
the stronger claim, its open item, and everything in §2 below.

## 2. `n = 8` is listed as proved in v10.21 — and the listing is not supported

`lrc_proof_v10_21.md:13` (status line) and `:1422`:
> "*Case 2, composite $n$, both non-units dropped, $n$ even:* Sub-case B1 (parity
> argument; proved)."

`n = 8 = 2³` is even, so Sub-case B1 is what covers it. The **entire** treatment of
`n = 2^k` in the manuscript is one sentence — `grep` for `2^k` over all 1400+ lines
returns exactly one hit, line 936:

> "(where $n = 2^a m$, $m$ odd $\geq 3$), giving $|U_{\rm unit}| \leq 2\varphi(n) < n$
> so some residue is uncovered by unit runners. For $n = 2^k$ ($k \geq 3$): $n$ is
> even, so Sub-case B1 (parity argument, §11) applies directly: the parity of $d_1$
> (an odd non-unit in $\mathbb{Z}_{2^k}$) gives an uncovered residue at floor 0,
> giving $B_{\rm safe} \geq 1$."

Three defects, each checkable in one line.

**(a) The density bound excludes `n = 2^k` by its own hypothesis.** The displayed
identity is `2φ(n)/n = ∏_{p | m}(1 − 1/p)` with `n = 2^a m`, **`m` odd `≥ 3`**. At
`n = 2^k` we have `m = 1`, the product is empty, and

    2φ(2^k)/2^k = 1   for every k ≥ 2   (computed: k = 2..6 all give exactly 1.0)

against the claimed `≤ 2/3 < 1`. So `|U_unit| ≤ 2φ(n) < n` becomes `2φ(n) = n` — the
**strict** inequality fails, and it fails at `n = 2^k` and nowhere else among even `n`.

**(b) The citation is self-referential.** "Sub-case B1 (parity argument, §11) applies
directly" — that sentence *is* Sub-case B1. The only parity argument in §11 is
**Lemma 11.3c**, whose hypothesis is (`:906`) *"$d \in \{1,\ldots,n-1\}$ a **dropped
unit residue class**"*. Sub-case B is defined at `:922` as *"**Both dropped runners
are non-units**"*. Lemma 11.3c's hypothesis is the complementary case and cannot apply.

**(c) The parenthetical names an object that does not exist.** "the parity of $d_1$
(**an odd non-unit in $\mathbb{Z}_{2^k}$**)". In `ℤ/2^k` the units are exactly the odd
residues, so a non-unit is even and **an odd non-unit does not exist**. Under the
Sub-case B hypothesis `d_1` is a non-unit, hence even — and Lemma 11.3c's parity
argument works precisely *because* `r_d` is odd, which is what a dropped **unit**
gives. The manuscript's own motivating remark states the correct fact two clauses
later, and it is the opposite of what the argument needs.

**(d) Corollary 11.0's proof does not list `n = 2^k` at all.** The branch enumeration
at `:930` reads: `E_div = ∅` (Sub-case B2a); squarefree `n = pq` (Lemmas 12.2/12.3);
`n = p²`, `p ≥ 5` — *"⚠ **OPEN**"*. No branch for `n = 2^k`.

**Scope of this finding.** Defects (a)–(d) are quotations plus arithmetic; they show
the *stated* justification does not hold. They do **not** show LRC(8) is false, and
they do not rule out a repair. `Theorem 11.5` cannot be that repair: `:1173` states it
for *"$n=p^k$ with $p \geq 3$"*, excluding `p = 2`. Whether some other section covers
`n = 2^k` was checked by `grep`; it does not.

## 3. The obstruction is one quantity, and two independent routes found it

`2φ(n)/n = 1` exactly when `n` is a power of 2. Odd prime powers give
`2φ(p^k)/p^k = 2(1 − 1/p) ≥ 4/3 > 1`, with room; `p = 2` is the unique break-even.
The same threshold appears independently in `lrc_n_psquared_structural_analysis_v1.md:104`:

> "`PROOF_PS4_DENSITY` … **Survives** (statement). 2φ(p²) = 2p(p-1) > p² iff **p > 2**
> — true for p ≥ 3. The density bound holds."

and in `lrc_prime_power_tier2_v1.md:19` — *"Let n = p^k (**p odd prime**, k ≥ 2)"* —
and `:134`, whose sign estimate needs `p ≥ 3` (at `p = 2` it gives `+1`, the wrong
sign). **The whole prime-power tier of the general-`n` programme is written for odd
`p`, and `n = 2^k` is the excluded family.** `n = 4` is classical, so `n = 8` is the
smallest open member.

This is the same obstruction the bottom-up `n = 8` work reached from the other side.
`docs/n8/N11_TRANSLATION_v2.md` §1 records `φ(8) = 4` unit witnesses against 7 speeds,
ratio `(n−1)/φ(n) = 1.75`, and `(ℤ/8)ˣ` of exponent 2 collapsing five complementary
pairs to two. Same quantity, same break-even, reached independently. That convergence
is the reason to trust the location of the gap.

## 4. What this changes

1. **`n = 8` is not settled by the general-`n` corpus.** It is *listed* as settled in
   v10.21's own status table; §2 shows the listing rests on one self-citing sentence
   whose hypothesis is the complementary case and whose density bound is exactly
   break-even at `n = 2^k`.
2. **The canonical pointer is wrong by omission.** v10.21 carries a materially
   stronger claim than v11.8 and a different open frontier (`n = p²`, `p ≥ 17`).
   `CLAUDE.md` §8's "No active frontier" is not accurate for the general-`n` programme.
3. **The target is now specific**: supply the `n = 2^k` branch of Corollary 11.0 —
   Unit-Complete, both dropped runners non-units, `|E_div| ≥ 1`, `n = 2^k`, `k ≥ 3`.
   That is `n = 8` and it is stated in the corpus's own vocabulary.

## 5. Owed

- The v10 lineage has not been audited the way `lrc_whole_project_review_2026-04-18.md`
  audited v11.2. Only Sub-case B1 was examined here. Sections 12 and 13 of v10.21
  (Silence Fibre, `N-PSQ-*`) are unread by this session.
- Whether the v11 restart was a decision to abandon v10, or a fork that lost it, is
  not recorded anywhere found. Recorded as a question, not an accusation.
