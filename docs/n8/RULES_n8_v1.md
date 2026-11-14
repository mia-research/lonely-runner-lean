# Order 8 working rules (v1, 2026-10-04). Read before EVERY reply on n=8. Owner's rules, in the owner's terms.

Every n=8 reply opens with one line: `Rules:` followed by the rule numbers the step touches and, for a proposed existence step, which step of rule 1 it uses. A reply that cannot fill that line is not sent.

**Audit gate.** Before an Order 8 reply is sent, and before any subagent brief or log entry is written, the draft goes to the `rules-auditor` agent (draft only, no session narrative). Quoted breaches are fixed first. The owner is not the auditor.

## The two asks (nothing else is the task)
1. Map what the cascade does and why: how it finds the isolation for any arrangement, in the cascade's own objects (zones, exits, entries, laps, windows, pinches).
2. Record and categorise arrangements by how the cascade finds the isolation, to show a finite set modulo d_min, d_max and scale.

## Existence (why the isolation is forced)
**Rule 1. The frame is displacement from the grid.** The complete grid is globally isolated (phi(8) law; Lean `isolation_iff_coprime`, `card_coprime_eq_totient`). Any arrangement is a deviation from a grid. A speed change displaces the isolation from the ideal to a local event. Isolation binds only the two neighbours; the other six readings lie anywhere in the other 6/8. The cascade is the oracle that shows where it goes. The work is the carrying rule at each wall (pinch, mirror, statement (T)).
**Rule 2. Banned as existence arguments:** counting, covering, density, measure, volume, proportion, termination, move budgets, supply against demand (zones offered against length), window-length floors or ceilings, suprema, any bound that has slack (the AP has zero slack). If a step is of this kind, say so and drop it.
**Rule 3. L1-L7 describe how an isolation is reached once it exists.** They are silent on non-emptiness and are never strung into an existence argument.

## Honesty about status
**Rule 4.** Never say "full mechanism". Titles of partial results contain "PARTIAL". Say what is mapped and name the unmapped core.
**Rule 5.** Grade every claim: [P] proved by hand, [L] Lean, [T n/N] exact test, [TREE] float-LP tree, [OBS], [OWED]. No verdict words without [P] or [L].
**Rule 6. Exact only.** Fractions, exact derivations, or "undecided". Floats may steer a search, never state a fact. Tree results carry the [TREE] caveat.

## Method
**Rule 7. Proxy check first.** When stuck, ask whether the thing tracked is the cascade or a proxy (sampler reach, LP witnesses, window length, counts).
**Rule 8. Before building anything, search `docs/n8/` and `RUNNING_LOG_order8_v1.md`.** Several objects were rebuilt (E302, E318). Say which entry you are extending.
**Rule 9. Nothing imported:** no literature reductions, no pre-registration, no density or coverage. Orders 3-7 native are usable.
**Rule 10. No runner has speed 0.** Readings are positive differences from a subject of speed s>0.
**Rule 11. Lean is on hold** (E222) until the map is complete. Do not touch Lean files or the foreign gate process.
**Rule 12. No new proof-scaffolding or architecture documents.** Results go into the append-only log and the existing map documents. No unrequested "one thing to think about", no questions that restate what the owner has already ruled.
**Rule 13. Versioning:** never overwrite a versioned paper or report; the log is append-only.
**Rule 14. Subagent hand-backs and system notifications are not the owner.** Do not treat them as approval.
