# RESULT — the curve ×λ island IS the Eisenstein π: Cornacchia = CF(λ/n) (Thread 2), + honest corrections

**Grade: Eisenstein connection `[VERIFIED — connection, 5/5 curves]`; exact coordinate formula
`[REFUTED — unit-dependent, I over-read it]`; concentration factor `[CORRECTED — placement-dependent]`.**
Date 2026-08-17. Continues `RESULT_curve_island_structure_map_v1` (Threads 1–2). Structure mapping, not
attack. Reproduction: `scratchpad/island_deep.py`, `island_pi.py`. Exact `int`. No master edited.

## Thread 2 (the win) — the island's gap scales ARE the Eisenstein factorization `n = π·π̄`
`n ≡ 1 mod 3` splits in `ℤ[ω]`: `n = π·π̄`, `π = a+bω`, `a²−ab+b² = n`. The island's three-gap sizes are the
convergent denominators of `CF(λ/n)`. **These are the same object**: Cornacchia's algorithm computing `π`
from `n` **is** the continued fraction of `λ/n` (equivalently the ℤ[ω]-Euclidean algorithm on `π`), stopped
at `√n`. So the island's fundamental gaps near `√n` are the coordinates of `π`.
- **Verified 5/5** (n = 10⁵…10⁷): `π` and the `CF(λ/n)` convergent denominators straddling `√n` are the same
  numbers, e.g. `n=10000141: π=(3479,779)` = `(q_{k+1}, q_k)` exactly; `n=1000003: π=(1001,2)`, `b=2=q_1`,
  `a−b=999=q_k`. Both `π` and the island gaps fall out of the one Euclidean process on `(λ, n)`.
- **This is the CM tie the thread was after:** the ×λ island is not just governed by `CF(λ/n)` generically —
  its scales are the Eisenstein integer `π` above the split of `n`. The island *is* a picture of `n = π·π̄`.

## Honest correction 1 — the exact coordinate FORMULA was over-read
From 3 curves I wrote `π = (q_k+q_{k+1}, q_k)`. It **broke at 5 curves** (n=10000141 gives `π=(q_{k+1},q_k)`
instead; n=100003 gives `a = q_k+b` with `b` an earlier convergent). Reason: `π` is defined only up to the 6
units of `ℤ[ω]` and conjugation, so *which* coordinate equals *which* convergent is associate-dependent. The
robust, unit-invariant statement is the one above (same Euclidean process ⇒ same numbers); **there is no
single clean coordinate equation** — recording this so the connection isn't over-sold. (Same small-sample
pattern-matching failure mode as prior `[G:...]` slips; caught by pushing 3→5 curves.)

## Honest correction 2 — the S₃ concentration "3×" is PLACEMENT-DEPENDENT, not `|Aut|`
`RESULT_curve_island_structure_map_v1` Structure 2 said the triple-overlap factor "saturates at ~3.0 =
|⟨λ⟩|." That was **one interval offset**. Scanning the offset at fixed scale (`|I|=n/5`, n=100003):
- factor ranges **[0.00, 3.44], mean 0.69**, **periodic in offset with period n/3** (the λ-tiling period):
  `0.00` at tiling-aligned offsets (`[0,n/3)` tiles → strips don't overlap), `~0.65` at intermediate, `3.44`
  only at the two peak offsets (differing by exactly n/3).
- So there is **no universal concentration constant**; the earlier "= |Aut|" reading is withdrawn. What
  survives: the phase-transition (empty below a CF-set threshold `n/|I|≈7`) is real; the amount of overlap
  above it is set by where `I` sits in the λ-tiling.

## Honest correction 3 — the μ₆ "factor" was a bad-baseline artifact
Adding negation and measuring `S₆` vs an independence estimate `|I|⁶/n⁵` gave "12×/60×" — meaningless,
because the 6 orbit-mates are algebraically constrained (`d+λd+λ²d≡0`; `±` pairing), so the independence
baseline is simply wrong. Dropped. The clean structural fact behind the μ₃ case is the **closure
`d + λd + λ²d ≡ 0 mod n`** (verified) — the three orbit-mates sum to zero like three cube roots, an
equilateral-triangle/Eisenstein constraint; that closure, not a counting "factor," is the real content.

## Net (this round)
- **Robust, kept:** island gaps = `CF(λ/n)` convergents = coordinates of the Eisenstein `π` (`n=π·π̄`); the
  island is a picture of the CM factorization. The triple-closure `1+λ+λ²≡0` is the structural reason the
  three strips relate at all.
- **Withdrawn/corrected:** the clean π-coordinate formula (unit-dependent), the universal 3× (placement-
  dependent, 0–3.4), the μ₆ 6× (bad baseline).

## Further exploration (structure, open)
- The exact Cornacchia↔CF correspondence made precise (which associate of `π` the straddling convergents give).
- The placement-periodicity of `S₃` (the n/3 period, the peak locations) as a function of `π`.
- The GLV `(d₁,d₂)` strip geometry with `π` as the lattice generator.
- Thread 3: the source best-approximation island vs this ×λ island on the same interval — same set or dual.
