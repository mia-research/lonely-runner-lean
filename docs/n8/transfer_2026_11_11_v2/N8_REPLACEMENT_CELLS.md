# Replacement cells when the third reading moves

[Moving both edges](N8_MOVING_CORE_EDGES.md) extends this argument to
independent movements of the readings at 3 and 4.

Fix normalized readings (1,2,4,5). Replace the reading (3) by
(s\in[17/7,28/9]), and let the two other readings vary independently
in ([1,15]). Lean proves a (1/8)-clear time in ([1/8,7/8])
throughout this domain. The same argument applies to any core that
retains the cells used by the proof.

## The first rejected cell supplies the constraints

At the first slow cell ([1/8,7/40]), call a reading blocking the
left edge (p), and the other variable reading (q). Then (7<p<9),
so (p)'s opening is (u=9/(8p)), and (p) is clear at the right
edge. If (q) blocks both (u) and the right edge, there are two
possibilities. The overlap at (u) sharpens the earlier bounds.

| Right blocker | Required overlap |
| --- | --- |
| (5<q<45/7) | (7p<9q) |
| (75/7<q<85/7) | (5p<3q) |

These are necessary conditions for failing the candidate checks.
They hold whether or not (s) remains at its original value.

## Lowering the third reading

The slow closing in the second cell moves from (7/24) to
(7/(8s)). If (p<51/7), the candidate (17/(8p)) fits exactly
when (17s\le7p). For the lower right-blocker band it also needs
(17q\le15p). In the higher band, (q) is clear at that candidate.

When this extension is unavailable, (5/8) clears the lower band
through (q=31/5). The end of the minimum reading's first window,
(7/8), clears the rest of the lower band and the higher band.
For (p\ge51/7), the original second closing (7/24) still works.

## Raising the third reading

For the lower band with (p\ge68/9), (9/32) works. The upper
limit (28/9) on (s) is the condition for (s) to stay clear
at (9/32). For the higher band, the overlap forces (p<51/7)
and (q>35/3). That retains the witness at (3/8).
The lower band with (p<68/9) and (q\ge17/3) also clears there.

The remaining lower-band case has (p<51/7) and (q<17/3).
The moving opening (17/(8s)) works if (17q\le31s) and
either (17p\le39s) or (41s\le17p). Otherwise the late cell
([33/40,7/8]) supplies a witness. The reading (q) clears at
its start. If (p\le235/33), (p) also clears there. For larger
(p) its opening (49/(8p)) still fits, because the lower
bound on (p) and the upper bound (q<17/3) imply (49q<39p).
That last comparison says that (q) remains clear until (p)
reopens.

## Exact replay

The replay checks the stated witness and its order relative to the
ordinary first landing in 3,744 rational controls. In 1,404 the
old slow point at (3/8) disappears. Three recorded first landings
illustrate the different replacements.

| (s) | (p) | (q) | First landing |
| --- | --- | --- | --- |
| (29/10) | (71/10) | (12) | (85/284) in the extended second cell |
| (301/100) | (71/10) | (111/20) | (33/40) in the late cell |
| (31/10) | (71/10) | (111/20) | (85/124=17/(8s)) at the moving opening |

Run `python3 cascade_replacement_audit.py` alongside the previous
cascade audit scripts. The checked replacement theorem and
the comparisons for the moving endpoints are in
`Fresh/CascadeReplacementCell.lean`. The two-reader theorem now
shares the sharper first-cell overlap lemma.

The interval for (s) is a proved range. Extending this to
arbitrary slow blocks requires a way to force or replace the
remaining core cells when more of their defining readings move.
