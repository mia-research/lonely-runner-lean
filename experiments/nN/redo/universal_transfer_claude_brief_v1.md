# Priority: universal AP/grid isolation transfer

User requests delegation because Codex tokens are scarce. Focus reasoning on the
actual universal bridge, not another numerical catalogue. Work independently;
write a precise handoff for Codex to verify and formalise later.

Repository: /Users/trentpalelei/Desktop/Math Ex/LonelyRunner
Read completely: LonelyRunner/LRC/Spec/IncomingWindowN.lean,
PinchReflectionN.lean, FiniteWindowContinuationN.lean, PathRouteN.lean,
PathWindowN.lean, SegmentWindowN.lean, TrainCollapseN.lean; relevant
DeformationN definitions. Consult existing records before proposing something
already disproved. The outer docs/n8/RUNNING_LOG_order8_v1.md contains corrections.

Established: rational incoming fixed lap windows have right replacements,
including simultaneous pinches. Earlier feasibility forces active slopes <=0;
period reflection reverses them. IncomingWindowN supplies rational witness time
and earlier inequalities internally. FiniteWindowContinuation handles limits
when a finite label family or bounded witness times is supplied. PathWindowN
already proves WindowBound -> LonelyRunnerAt8; WindowBound is OWED, not a theorem.

Target: show isolation survives an entire AP-to-target deformation, without
assuming future isolation, a finite global catalogue, bounded witness times,
or universal cascade termination. Work in the user's AP/grid displacement
framework. No density/volume argument, brute-force certificates or move-budget
termination strategy. An analytically DERIVED control on witnesses may help,
but do not relabel an assumed bound as a proof.

Investigate three precise avenues:
1. Can period reflections be selected or replaced so their witnesses stay
controlled along a rational-target path? Track denominator growth and prove
any claim; rational individual pinch parameters do NOT exclude an irrational
accumulation point. Compactness of parameter space alone does not give a
finite subcover unless every point is already covered.
2. Can one-runner-at-a-time deformation avoid the limit issue using the fixed
six readings' common period and direct control at lattice points? SegmentWindowN
has a bound that diverges near resonance: distinguish this construction's
divergence from proof that ALL witnesses diverge. Identify exactly what is
needed at resonances and whether another existing theorem supplies it.
3. Can TrainCollapseN or the exact scale update absorb the apparent divergent
label family as one parameterized mechanism? Keep all other readings' clearance
and phases. Distinguish a true scale change of all readings from scaling only
a cluster. Do not require the first cascade landing if another isolation works.

Deliver: (a) strongest actual deduction with line-level theorem references;
(b) complete symbolic proof if found, or the precise unresolved statement and
why proposed shortcuts fail; (c) suggested Lean theorem statements with all
hypotheses; (d) highest-value next action. Never call this universal unless the
limit/endpoint and target quantifiers are fully addressed.

Safety/resource limits: no background jobs, subagents, multiprocessing, heavy
searches, Lean builds, installs, Git actions or edits to existing files. One
Claude foreground process. Prefer reasoning only; any optional exact numerical
check <=100 cases and <=15 seconds, with caps reported as unfinished. Use
apply_patch to write ONLY new files prefixed universal_transfer_claude_v1 under
experiments/nN/redo/. Save a <=2500-word report there and return a <=400-word
summary. This is independent research, not authorization to change proof source.
