# Native transport review, bounded independent reasoning

Read Spec/PinchReflectionN.lean, IncomingWindowN.lean, WindowPinchN.lean,
GrandReturnN.lean, PathRouteN.lean (relevant full theorem bodies). No edits to
Lean or existing files, no builds, workers, subagents, Git, or long searches.
Write only new native_transport_claude_v3* files in experiments/nN/redo,
using apply_patch. Exact arithmetic if testing, <=100 examples/15 seconds.

Codex is assembling automatic replacement at a first rational fixed-lap
endpoint from the existing affine-slack/root and incoming-window lemmas.
You investigate a separate way to make the replacement more economical:

Current rational_reflection_data constructs an enormous multiplier from
denominators of 8*d_i*t. Can we instead use a common period H of the current
readings, reduce the old witness modulo H to 0<t0<H, and reflect to H-t0,
WITHOUT losing the incoming-direction condition on all active inequalities?
At an active pair, its derivative is proportional to t*(d_j*v_i-d_i*v_j).
Does replacing t by t0 and shifting the lap labels by whole periods preserve
the signs of EVERY active derivative? Check nonactive inequalities and ties.
Derive complete statement with hleft or active signs, not a claim merely from
periodicity. Distinguish current period H from periods at nearby arrangements.

If true, explain exactly what this improves: at a fixed rational arrangement,
chosen reflected witness lies below H independently of old lap labels. This
does NOT give uniform H along a rational deformation automatically. Check
whether the six-fixed-readings one-mover resonance case has a fixed usable H
and whether any existence hypothesis remains. Do not claim universal n8 or
that off-lattice witnesses converge without proof.

Also critically inspect the previous report's proposed restricted (C): it
claimed all ratios near 1 give nested blocked intervals. Is a horizon bound
needed before later recaptures? Supply a precise safe statement if possible.

Return <=1500 words, complete equations/hypotheses, explicit counterexamples
to any false simplification. Existing source and other sessions untouched.
