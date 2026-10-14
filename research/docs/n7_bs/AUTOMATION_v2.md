# n=7 automation — driver, gate, and the open work order

Created 2026-09-05. Companion to `ROADMAP.md` (which is the status board).

## 0. Ground truth discovered at session start (2026-09-05)

Two infrastructure defects made the previous "build clean" signal hollow. Both
are fixed; recording them so the signal is not trusted blindly again.

1. **`lake build` was building almost nothing.** `lakefile.toml` declares
   `[[lean_lib]] name = "LonelyRunner"` with no `globs`, so the default target
   is the single root module `LonelyRunner.lean`, which imports only
   `LonelyRunner.Basic`. Neither the n=6 nor the n=7 tree was in the default
   build closure. Reported job counts (2485) were essentially mathlib.
   **Fix:** the gate builds explicit module targets
   (`LonelyRunner.LRC.SmallN.IntLRC_7`, `...IntLRC_6`) — 3357 jobs.
2. **Four `.olean` artefacts were dataless.** The project lives under
   `~/Desktop`, which is iCloud-synced; four build artefacts had zero allocated
   blocks (`stat -f %b` = 0) and were unreadable, while lake's content-hash
   traces still marked their modules up to date. `lake build` therefore reported
   success while `lake env lean` failed with `invalid header`.
   Affected: `IntLRC_6_BHK_MainLemma`, `IntLRC_6_BHK_Section6`,
   `IntLRC_6_BHK_Section7`, `IntLRC_7_BS/Defs`.
   **Fix:** `scripts/n7/gate.sh` step [0] purges dataless oleans before every
   build. This will recur; the purge is permanent, not a one-off.

## 1. The gate (`scripts/n7/gate.sh`) — the `/goal` done-check

Exit 0 only when all of:

- [0] no dataless `.olean` remains (purged, then rebuilt)
- [1] `lake build LonelyRunner.LRC.SmallN.IntLRC_7 LonelyRunner.LRC.SmallN.IntLRC_6` exits 0
- [2] zero `sorry` tokens in `IntLRC_7_BS/*.lean` + `IntLRC_7.lean`
- [3] `#print axioms intLRC_seven` = `[propext, Classical.choice, Quot.sound]`
      and contains no `sorryAx`

Steps [2] and [3] are separate on purpose: [2] catches a `sorry` in a file that
`intLRC_seven` does not happen to depend on; [3] catches an axiom leak that no
`sorry` grep would see.

## 2. Open work order (7 `sorry` tokens, 4 mathematical items)

Ordered by dependency and by how explicit the source is. Items 1–2 are
self-contained; item 3 needs a lemma composition; item 4 needs a statement
redraft before any proof work.

| # | Item | Lean site | BS source | Blocker |
|---|---|---|---|---|
| 1 | **Case 6.5 `(3,0,2)`** `case_65` | `Case_A5.lean:3137` | §6.5, `sources_barajas_serra_2008.txt` L698–730 | none known. Endgame table `case65_window_choice` already `decide`-proven. Symmetric to the closed `case_64`. Front half = establish (14): `ℓ(A₁)≤3 ∧ ℓ(A₄)≤3` **or** `ℓ(A₁)≤4 ∧ ℓ(A₄)≤2`, across the four Lemma-11 branches (i)/(ii.1)/(ii.2) × `h<m`/`h=m`. The `2·`/`3·` remultiply sub-branch needs `rmk8_i_k3`-style reasoning. |
| 2 | **Case 6.6 `(2,2,1)`** `case_66` | `Case_A5.lean:3150` | §6.6, L732–770 | none known. Endgame `case66_window_choice` `decide`-proven. Self-contained: target (15) `ℓ(A₁)≤2 ∧ ℓ(A₂)≤2` then `lemma5`. Sub-case (a)/(b) are explicit finite `q`-tables over `k ∈ {1,2,3}` with the (16) bad-pair list. |
| 3 | **Case 6.1 `(5,0,0)`, `ν(E) ≠ {m}` branch** | `Case_A5.lean:295, 418, 428, 429` | §6.1, L509–546 | `case_61_top` (`ν(E)={m}`) is done. The open branch needs Lemma 10 on a 4-subset + 5th element, `lemma9_i_dispatch` compression, then `place_window5` / `dichotomy_core`, with the `3·`-remultiply (`rmk8_i_k3`) for the `{p,q}={2,4}` exception. |
| 4 | **§7 `m = 1`** `five_avoid_m1` | `Case_A5.lean:124` | §7, L800–830 | **Statement is FALSE as written** (roadmap, 2026-06-28): three 5-sets over `ZMod 49` — `{1,4,11,39,43}`, `{1,4,18,22,29}`, `{1,4,18,44,46}` — have no unit multiplier. BS resolves them jointly with `d₆ = 7k` over `N' = 98`, where the survivors all have `gcd ≥ 2`, contradicting the LRC normalisation. **Requires a statement redraft** to carry `d₆` and the `gcd = 1` hypothesis, then an exhaustive check. Feasibility of that check by kernel `decide` is unestablished — sizing it is the first task, not proving it. |

## 3. Driver protocol (per item)

1. **Source first** (CLAUDE.md §5). Transcribe the BS passage for the exact
   case before touching Lean.
2. Spawn a fresh-context agent with: the statement, the source passage, the
   available API inventory, and the criteria. Never the session narrative.
3. Run the gate. A green gate is the only evidence that counts.
4. On green, commit that item alone. On red, feed the compiler output back.

## 4. What "automated to completion" can and cannot mean here

Items 1–3 are transcription-and-composition work against a written proof; a
supervised agent loop is a reasonable fit. Item 4 is not: it needs a
mathematical decision about the statement first, and its exhaustive search may
not be kernel-feasible. The loop must not be allowed to "close" item 4 by
weakening its statement — that is the failure mode the gate's step [3] exists
to catch, and a reviewer must check the *statement*, not just the axioms.

---

## 5. Axiom-hygiene regression found and fixed (2026-09-05)

The first full gate run turned up something the `sorry` inventory could not see.

**`#print axioms intLRC_seven` listed 126 `native_decide` axioms**, all from
`IntLRC7BS.fallback_63_l1._native.native_decide.ax_1_*`. Single site:
`Case_A5.lean:1635`, introduced with the case_63 branch-8 fallback work.

This contradicts the recorded project state ("Zero custom axioms /
`native_decide` / `unsafe` / `admit`", `memory/MEMORY.md`, audited 2026-06-25) —
that line is stale as of the case_63 commits. `native_decide` discharges a goal
by compiling it and running it, so it trusts the Lean compiler and runtime
rather than the kernel; it is not admissible under this project's stated
done-check.

**Cause.** Not search size. The statement quantifies over
`(T34, e0, rho, p, e1, Atar) : ZMod 7`, which is tiny. `Decidable` instance
synthesis failed under the binders because the conditions were phrased as
`Finset` membership (`Atar ∉ ({0,6} : Finset (ZMod 7))`), and `decide` therefore
could not even be attempted. Raising `maxSynthPendingDepth` does not help.

**Fix.** Split into `fallback_63_l1_core`, stating every membership as explicit
(in)equalities — which synthesises and closes by kernel `decide` in ~2s — plus a
`simp` bridge restoring the original `Finset` phrasing. Verified in isolation:
`#print axioms` on the bridged theorem = `[propext, Classical.choice, Quot.sound]`.
Total elaboration ~3s.

**Generalisable lesson for the remaining cases.** When a finite `ZMod 7` check
resists `decide`, the first thing to try is restating `Finset` memberships as
(in)equalities — not reaching for `native_decide`. Every endgame table in this
tree is small enough for the kernel.

## 6. Endgame feasibility map (computed 2026-09-05)

Pre-registers exactly what each case's front half must deliver. `intervalAvoids
a ℓ s k` = `∀ j < ℓ, a + j + s·k ∉ {0,6}`; entry `Y` means a good `k` exists for
*every* pair of window starts, so no normalisation of `A₁` to start at `1` is
needed.

Two classes (`A₁` shift 1, `A₄` shift 4) — `Y` at `(ℓ₁,ℓ₄)`:

```
        ℓ₄=1  2  3  4  5  6
  ℓ₁=1      Y  Y  Y  Y  .  .
  ℓ₁=2      Y  Y  Y  .  .  .
  ℓ₁=3      Y  Y  Y  .  .  .
  ℓ₁=4      Y  Y  .  .  .  .
  ℓ₁=5      .  .  .  .  .  .
```

This is exactly BS condition (14) for Case 6.5 — `(3,3)` or `(4,2)` — and shows
`ℓ(A₁) ≤ 4` is mandatory, never `5`.

Three classes (`A₁` shift 1, `A₂` shift 2, `A₄` shift 4) with `ℓ₄ = 1`:
`Y` exactly when `ℓ₁ ≤ 2 ∧ ℓ₂ ≤ 2`. This is BS condition (15) for Case 6.6, and
nothing weaker suffices.

**Missing endgame tables** (both `decide`-true, generic starts, not yet in
`Lemmas.lean`): the `(3,3)` pair at shifts `(1,4)` — a `lemma6_303` analogue of
the existing `lemma6_330` — and a generic-start `(4,2)` at shifts `(1,4)`
(`lemma6_402` currently fixes the `A₁` window start at `1`).
