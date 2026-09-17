# Pending for v9.6 — items recorded but not yet written into the manuscript

Opened 2026-09-18, against `MANUSCRIPT_v9_5.md` (the record). Append-only. Nothing here has been
written into a manuscript yet; this file exists so items are not lost between versions.

---

## 1. Appendix A item 6 — the terminal-time witness  `[to record]`

**Source.** A colleague's memo (proprietary origin, obfuscated framing; not queried, by instruction),
proposing:

    t_N > 0  ∧  I(t_N) = ∅   ⟹   Lonely(8, ds, t_N)

with `ε_d(t) = ⌊dt + 7/8⌋ − dt ∈ (−1/8, 7/8]`, and concluding that Existence is discharged by the
terminal cascade time, leaving only: is there a proof that some `t_N > 0` has `I(t_N) = ∅`?

**Verdict: correct mathematics, already in the tree, and it does not move the board.**

- The `ε` convention maps exactly onto `circDist`. Checked both directions: `inWay n d t` holds iff
  `ε_d(t) ∈ (−1/8, 1/8)`.
- In this encoding the arrow is **definitional**. `inWay n d t := circDist (d·t) < (n:ℝ)⁻¹` and
  `Lonely n ds s := ∀ d ∈ ds, (n:ℝ)⁻¹ ≤ circDist (d·s)`, so `I(t) = ∅` **is** `Lonely n ds t`, by
  `not_lt`. The memo's four-line derivation re-derives the definition under another convention.
- As a lemma about the cascade it is `MomentIterationN.lonely_of_fixed` (`Iteration.lean:132`),
  proved for every `n ≥ 2`, axiom-clean, and long predating this work.
- The memo's closing question — *is there a proof that some `t_N > 0` has `I(t_N) = ∅`?* — is
  `ExistenceAt8_cascade`, and `LRC.Spec.target_forms_agree` proves
  `ExistenceAt8 ↔ ExistenceAt8_cascade`. So it is not a lemma that would yield Existence; **it is
  Existence**, restated. `CascadeCapped` is a third equivalent form
  (`existence_of_capped`, `capped_of_existence`).

**So the hypothesis that the Existence hole is "only witness plumbing in Lean" is refuted by the
file**: the plumbing has been done since before v9. What is open is termination.

**On the frame.** The memo is stated about `t_N`, the instant the exhibited rule produces, so it sits
in the framework's native form and not in the discarded `∃ f : Finset ℝ → ℝ` naming form. Confirmed
absent from the tree: the only occurrence of that shape is the caution in `Target.lean`'s docstring.
`Classical.choice` in the axiom lists is `inWay`'s real comparison, not a choice-extracted naming
function — see `NAMING_VS_EXISTENCE_v1`.

**What to write.** An Appendix A entry beside item 5 (the depth floor), making the same shape of
point: a proposal that is true, elementary, and already discharged, whose residue is the open
problem itself.

---

## 2. Repository items, not manuscript items  `[to fix]`

- **`.gitignore`'s `*.out` silently drops deposited outputs.** `git add` on a deposit directory
  lands the scripts and omits the evidence; the documents cite those outputs as their witnesses.
  Caught on `residue_route_v1` and `long_return_circle_v1`, force-added in `a45bba8`. The trap
  remains for the next deposit. Consider a negation for `experiments/n8/**/*.out`, after checking
  what else it would pull in.
- **`scripts/cascade/gate.sh` leaves `LonelyRunner/_CascadeGateAxCheck.lean` in the source tree**
  after every run, untracked and not ignored. It cannot reach the bundle (nothing imports it and it
  is not an import-closure seed), so this is hygiene, not correctness.
- **`PROOF_DEV_v1` is cited and not deposited.** Already explained in place in Appendix A item 4 —
  it sits in a separate working tree and the passage is quoted verbatim in `LOST_FUNCTIONS_v1` §E.
  Listed here only so it is not re-discovered as a defect.
