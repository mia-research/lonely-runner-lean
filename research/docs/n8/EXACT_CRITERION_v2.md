# A ℤ/2 symmetry of the whole n=8 bridge — and two items I wrongly called open

2026-09-10. **Supersedes `EXACT_CRITERION_v1.md`.** Scripts `experiments/n8/ok_*.py`,
exact rational arithmetic, entry-and-exit evaluation. v1's §1–§3, §5–§7 stand unchanged;
§4 and §8 are corrected here, against me, in §5 below.

---

## 1. Theorem R, at full generality  `[PROVED]`

> **Theorem R.** For **every** integer `e` and every `t`,
> `bad(e, e−1−t) = { 7−r : r ∈ bad(e,t) }`, where `bad(e,t) = {r : er+t ≡ 0 or 7 (mod 8)}`.

*Proof.* `e(7−r) + (e−1−t) = 8e − 1 − (er+t) ≡ −1 − (er+t) (mod 8)`, which carries `0 ↦ 7`
and `7 ↦ 0`. `r ↦ 7−r` is an involution, so the sets correspond bijectively. ∎

**The proof never uses the parity of `e`** — v1 stated it for odd `e` only. It holds for
divisible speeds too. Verified: 0 failures over all 64 `(e mod 8, t mod 8)` pairs and over
`e = 1..59`, `t = −20..59`.

Since `⌊e(1−x)⌋ = e−1−⌊ex⌋` off the breakpoints, the whole bridge is equivariant:

> **The n=8 bridge carries an exact ℤ/2 symmetry:** `x ↦ 1−x` acts on the blocked-residue
> set by `r ↦ 7−r`. That is, `cover(1−x) = 7 − cover(x)` for any speed set whatsoever.

Verified on 12 random **mixed** unit-and-divisible speed sets, 1208 interior points, 0
mismatches. `ℤ/8` is partitioned by `r ↦ 7−r` into the four pairs
`{0,7}, {1,6}, {2,5}, {3,4}`.

## 2. What it gives immediately  `[PROVED]`

- **`U = 1 − U`** (all-blocked is self-paired). Verified, 0 mismatches.
- **`S = 1 − S` for every leaf and every speed set.** `S = {x : some residue uncovered}`,
  and `uncovered(1−x) = 7 − uncovered(x)`, so uncovered is non-empty at `x` iff at `1−x`.
  **Every safe-measure computation in this project only ever needs `[0,1/2)`.**
- **`V = 1 − O`** for the four units (v1 §1): `r ↦ 7−r` swaps `ODD` and `EVEN`. Hence
  `v = o` and `U = O ∩ (1−O)`.
- **`|A_even ∩ O| = |A_odd ∩ V|`.** For `m ≡ 4 (mod 8)`, `t_m ↦ m−1−t_m` with `m−1 ≡ 3`,
  so `A_even = {t ∈ {0,7}} ↦ {3,4} = A_odd`, while `O ↦ V`. This **proves** the identity
  `|S^c| = |A_none ∩ U| + 2|A_even ∩ O|` that `O_STRUCTURE_v2` §1 carried as given.

## 3. The single-residue trap is forced, not accidental  `[PROVED]`

`DROPPED_UNIT_THEOREM_v1` records the one place the entry-and-exit discipline is
load-bearing — the extremal absent-`(3,4)` case, `E_non = {1,2,5,6,7}`:

> `x ∈ [3/7, 1/2) → uncovered {2}`;  `x ∈ [1/2, 4/7) → uncovered {5}`

`x = 1/2` is the **fixed point** of `x ↦ 1−x`, and `7 − 2 = 5`. The residue *must* hand
over to its reflection partner exactly there. The trap is where the symmetry acts, and any
tracker following one residue across `1/2` will lose it — in this leaf or any other.

Verified independently: `uncovered(1−x) = 7−uncovered(x)` and `S = 1−S`, 0 mismatches over
16 cells; `|S| = 19/35`, reproducing the doc's figure. And the extremal absent pair `(3,4)`
is itself one of the four reflection pairs — the self-paired absent pairs are exactly
`{0,7}, {1,6}, {2,5}, {3,4}`. That the extremum sits on a self-paired class is a
**prediction worth testing across the other leaves**, not yet a theorem.

## 4. Corrected map of what is open  `[the whole n=8 tree]`

| leaf | representative | non-representative |
|---|---|---|
| Case 1, no multiple of 8 | `t = 1/8` | same |
| Case 2, dropped unit | **PROVED** | **(NR) — OPEN** |
| Case 2, Unit-Complete `\|E_div\| = 2` | **PROVED** | **(H′) — OPEN** |
| Case 2, Unit-Complete `\|E_div\| = 1` (twin) | **PROVED** | — |

**(H′)** has a **proved** Fibre Criterion behind it (`STATUS §2`):
`|S^c| ≤ (o+u)/2 + (n_U + 3n_O)/(4M)`, `M = e_{ρ₀}/4`. Two things must hold:
- **main term:** `o + u < 1`. By Theorem R, `v = o` and `u ≤ o`, so **`o < 1/2` suffices**.
  Observed maximum of `o+u` is `3/5`, at `(1,3,5,7)`.
- **error term:** `(n_U + 3n_O)/(4M) ` must be beaten. `n_O` grows with the unit speeds
  while `M` depends only on `e_{ρ₀}`, so this does **not** close for fixed `e_{ρ₀}` against
  large units. `STATUS §3` records the consequence: the primitive a-priori failures are
  **not finite** (57 at `q ≤ 6`, at every max speed up to the sweep limit). The proposed
  route there is to iterate the fibre argument over `e_7`, then `e_5`, then `e_3`.

**(NR)** — `|S| ≥ 1/2` for every non-representative `E_non` in the dropped-unit leaf
(`DROPPED_UNIT_THEOREM_v1` §80). Untouched so far. It now has `S = 1−S` available.

## 5. Two corrections, both mine, both the same direction  `[RETRACTED]`

v1 §4 wrote of the `m → ∞` statement:

> "*If* the three `A`-sets equidistribute against `(O,V,U)` … a Weyl statement, **not
> proved here, and exactly the kind of claim that fails on resonance**"

and v1 §8 listed as open

> "(ii) the finite-`m` statement `|S^c| < 1/2` uniformly, which is what the census
> supports and the limit argument does not reach".

**Both are wrong.** `STATUS_n8_ANALYTIC_v1.md` §2 already carries it as proved —
"**Fibre criterion `[PROVED]`.** … exact identities for `|S^c|`, plus a discrepancy lemma
… give `|S^c| ≤ (o+u)/2 + (n_U + 3n_O)/(4M)` for `ρ₀ = 4`" — with main term `(o+u)/2`,
exactly the quantity I derived. Not a limit: an explicit error term.

Second: v1 §8 listed the single failing cell `{1,3,4,5,7}` as **OPEN**, needing a direct
witness. `STATUS §3` says the opposite — the non-representative case closes "together with
§2's reduction, the Dilation theorem, and **Lemma D for the one primitive exception**", and
`|S(4)| = 5/14` is precisely that exception. **Lemma D already covers it.**

Both errors run one way: I marked as open something the corpus had proved, because I had
not found it. That is the documented one-way suppression bias, and the fix is mechanical —
**before grading anything open, grep `STATUS` and the leaf docs for it.** Same rule that
v1 §7 stated for proposing a bound, applied to declaring a gap.

## 6. Grades

Theorem R at full generality, the ℤ/2 equivariance, `U = 1−U`, `S = 1−S`, `V = 1−O`,
`|A_even∩O| = |A_odd∩V|`, and the `W₂` explanation: **PROVED**, each verified. The
self-paired-extremum prediction: **CONJECTURE**. `o < 1/2` in measure: **OPEN**. The
`(H′)` error term: **OPEN**. `(NR)`: **OPEN**.
