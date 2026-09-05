# DEVIATIONS — `PREREG_descendant_frame_operator_v1.md`

*Filed with `RESULT_descendant_frame_operator_v1.md`.*

**D1 — ★ Recurring bug: a hardcoded conclusion print contradicted its own output.** `floor_check.py`
printed "=> descendant is a FLOOR curve … End(E')=O_3" **unconditionally**, for every prime. At `p=307`
the output above it showed the descendant `j'=289` has 3-neighbours `{0,13,233,262}` — **not** a floor
curve (the volcano is deeper there, `v_3(f)=2`). The print was written before the neighbour list existed.
**This is the identical failure mode as the "pigeonhole" print in the Kummer run (D4 there) — third
occurrence of a hardcoded narration outrunning the data this session.** Correction: certified-curve
claims are **restricted to `p=43` and `p=127`**, where the descendant's only 3-neighbour is the crater
`j=0` (airtight conductor-3). `p=307` is reported as a deeper-volcano case, not a floor.

**D2 — Method change (improvement): `Φ_3` primary, Vélu as cross-check.** The prereg §5 named "Vélu
construction + conductor check" for Step 3. I used the **modular polynomial `Φ_3(0,Y)`** as the primary
existence certificate (its roots *are* the 3-isogenous `j`-invariants, by definition), with Vélu as an
independent cross-check where the descending kernel is `F_p`-rational (matched at `p=43,127,307`). Cleaner
and more rigorous than Vélu alone; not a scope change.

**D3 — Conductor certificate via the isogeny graph, not Kohel's algorithm.** "End(E')=O_3" is certified
by: (i) `E'` is 3-isogenous to the crater `j=0` (maximal order, conductor 1), (ii) a 3-isogeny changes
only the 3-part of the conductor by ±1, (iii) `j' ≠ 0` so `E'` is not maximal, and (iv) at `p=43,127`
`E'`'s **only** 3-neighbour is the crater ⇒ it is one step below ⇒ conductor exactly 3. This is a valid
certificate for these primes; I did **not** run a general conductor algorithm.

**D4 — Clarification, not deviation: "eis'" is the record's abstract definition applied to `O_3`.** The
record defines `eis(x)` = representative of `x ∈ F_p ≅ ℤ[ω]/(π_p)` in the reduced cell — the **residue-ring
reduction**, not the curve points `[d]G`. For a curve with `End = O_3`, the faithful `eis'` is the
representative of `x ∈ F_p ≅ O_3/(π')`. That is what was computed. `λ_max/Tr` is independent of the choice
of `π'` vs `π̄'` (conjugate lattices, same shape) and of the unit (rotation), so the value is well-defined.

**D5 — Out-of-scope addition (flagged, not smuggled): the secp consequence.** The prereg fixed scope at
small `p` and disclaimed secp. §5 of the RESULT notes that `v_3(f_secp)=1`, so secp *has* a 3-descendant
with `End=O_3`, and the frame value `(8+√37)/16` is scale-free (a property of the **order**, not of `p`).
This is a **`[DERIVED]` consequence**, filed as such — not a measurement at secp, and carrying no d-side
or ECDLP content.
