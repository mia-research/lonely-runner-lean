/-!
# n = 7 (Barajas–Serra) — assembly

Assembles `Case_A4` + `Case_A5` (via `Reduction`) into the Hard-Case lemma
`6·v₁ < V ≤ 6·v₅ ⟹ ∃ t, ∀ j, circDist (v_j · t) ≥ 1/7`, then rewrites the
single `sorry` in `LonelyRunner.LRC.SmallN.IntLRC_7`.

Done-check: `lake build` clean **and**
`#print axioms intLRC_seven = [propext, Classical.choice, Quot.sound]`.

Status: not started. See `docs/n7_bs/ROADMAP.md`.

Planned imports: `IntLRC_7_BS.Case_A4`, `IntLRC_7_BS.Case_A5`.
-/
