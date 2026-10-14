# Plan: test the arrangements by exhaustion, by cells, with the equivalences logged (v1)

2026-10-02. Owner: scale is not an issue and intermediate speeds are covered by `d_min`, so there may be a limit to the arrangements we need
to test; exhaustion is acceptable if the log of look-alike arrangements is kept (`ARRANGEMENT_EQUIVALENCES_v1.md`).
Mapping, not proxies: every object here is the cascade's own path.

## What the maps give
1. Coordinates: `ρ_1 = 1 < ρ_2 < … < ρ_7` (scale removed). A state is `R = (8j+1)/ρ_x`, an exit of a setter; the start is `R = 1`.
2. All conditions that decide a path are homogeneous LINEAR in `ρ` (a zone edge is `(8j±1)/ρ_y`; comparing two edges clears the denominators).
   So the arrangements with one given path (result) are a finite union of polyhedral cones; the path changes only where two edges cross (E312).
3. Hops are births and deaths of components of the lonely set (E313); all of a bounded window is a finite hyperplane arrangement.

## The enumeration (symbolic cascade over cells)
- Window `W_J`: `ρ_7 ≤ 8J + 1`. For `J = 1` every reading is in `(1, 9]` (laps 0 and 1 only).
- Recursion: at a state, split each reading into clear / blocker (with its lap `j`) by linear inequalities (strict/non-strict as the zone is open); the
  setter is the blocker with the largest end (pairwise linear comparisons); the next state is its exit; repeat; a leaf has no blocker.
- A branch is kept only if its cell has an interior point (linear programme with maximal slack on the strict inequalities); an exact rational witness
  from the cell is run through the exact cascade and must reproduce the branch's path (soundness).
- Coverage test: random arrangements in `W_J` (exact Fractions) must each lie in exactly one cell; any that does not is an exception to be explained.
- Output per cell: path signature, defining inequalities, landing `R*` range, flank. Cells with the same signature are one RESULT class.

## Questions the enumeration answers
- `J = 1, 2, 3, …`: number of cells and of result classes; does it stop growing (the limit the owner expects) or grow with `J`?
- Do the cells for `ρ_max` in a higher lap window repeat the lower ones (the grid's own scale invariance for the path, not only for the class events)?
  E314 says not for the fastest runner at lap ≥ 2 (no hops), so the question is which structure repeats.
- Which cells have equality (tangent) boundaries (arrangements on the hyperplanes): treat as closed cases with the cascade's strictness, listed separately.

## Order of work
1. `symbolic_cells_v1`: `J = 1`, exact witnesses, coverage test (prototype: E316).
2. `J = 2, 3` and the growth table; classify new cells by which laps they use.
3. Log every look-alike pair found (the equivalence log) with its check.
4. If the count stabilises: state the finite list of cells as a theorem about the window plus a statement for readings above it; Lean owes the five crossing types
   (E312) and the cell lemma; each cell's landing certificate is a pair `(b, k)`.
5. If it does not stabilise: the growth law is the next object to map.
