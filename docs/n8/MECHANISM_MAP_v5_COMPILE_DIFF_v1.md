# compile-diff: MECHANISM_MAP_v5 section 11 against log E269-E330 (first pass, 2026-10-03)

Run by the `compile-diff` agent on the first draft of v5 §11 (lines 926-965 of that draft) against `RUNNING_LOG_order8_v1.md` lines 10128-10858. The agent read all of E269-E330 and the draft §11 in full. This file is a condensed record; the agent's full table (about 120 rows) was delivered in-session.

## Findings
- Entries with at least one item carried: 18 of 62 (E311, E312, E313, E315, E316, E317, E319-E330 and partly E270). Entries with nothing carried: 44 (E269, E270-E310, E314, E318, E322).
- Dropped categories: (e) owner rulings E270-E318 (about 36); (b) withdrawals in E269, E274, E278-E279, E281, E284, E287-E289, E293-E296, E299, E301, E304, E311/E313, E316, E329; (a/c) open items and stated limits E269-E330; (d) grades of E280, E319-E322.
- Stale v4 statement: "Open: multi-pinches and the bounded-time half" (v4 ~line 235), bounded by E280.
- Twelve statements stronger than their source: C1 "R up to 11.966" (a closure value); C2 sampler maxima presented without scope; C3 the 14-class claim without the "stated approximately" caveat; C4 72%/99.8% side by side (E328: not comparable as frequencies); C5 K2a argument without the K2s1 gap; C6 the strict pairwise setter form without the exit-tie rule; C7 the step-0 20,000 not traceable to a log entry; C8 the "greedy cover" framing (E269 cautions that covering is an imported shape); C9 the 2,939 witness figure not in the log; C10 an owner statement not in the log range; C11 opener counts as lower bounds; C12 the J=3 count from the truncated run (disclosed).
- Grade moves without artifact: `[LEAN ZoneLinkN]` (no axiom output in the log); `[TREE]` on the closure-vertex tangency.

## Disposition in the revised §11
- Corrected: C1 (supremum is a closure value; largest member landing 11.5925), C2 (reach scoped; E315/E317 cited), C3 (caveat added), C4 (not comparable as frequencies), C5 (K2s1 gap), C6 (tie rule), C7 and C9 (facts entered in log E331), C8 (greedy-cover phrase removed; E269 caution cited), C10 (replaced by what the owner asked), C11 (stated as lower bounds).
- Added: §11.8 owner rulings, withdrawals, open items, Lean artifacts; §11.7 extended (Cover8, WindowBound, (T), tail-update rule, R* <= 12, W6); stale multi-pinch statement marked.
- Grade artifact: 2026-10-03 `lake env lean` `#print axioms` for `LRC.ZoneLink.slower_lap_le`, `faster_lap_lt`, `equal_not_inZone`: `[propext, Classical.choice, Quot.sound]` (recorded in E331). The vertex tangency is written as "derived from the vertex; general statement not proved" (E321).

## Not done
- A second `compile-diff` pass on the revised §11 (owed before v5 is relied on or replaces v4).
- The 36 owner rulings are carried as one-line summaries, not quotes; the quotes are in the entries named.
