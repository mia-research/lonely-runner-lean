# Updated targeted task — 2026-10-05

User has another Claude session mapping transport. Do not overlap its source
edits. Read outer `/Users/trentpalelei/Desktop/Math Ex/docs/n8/RUNNING_LOG_order8_v1.md`
E393-E399 and complete HalfPairParityN.lean, plus existing dead_flank_types_v1.py
and its output (read before importing; avoid unguarded workloads).

Investigate a precise claim needed by E395's proposed transport, not a new
catalogue: (C) a consecutive opening run blocked by at most five walkers must
be blocked by one near-sharer or an exact half-pair. E397 has more general
q=3 etc covers, so distinguish unrestricted (C), a fastest-flank version
(all walker ratios <1), and the actual separated-block/twin-chain hypotheses.

Deliver either a small exact counterexample WITH its complete residue table,
or a precise plausible corrected lemma including necessary run-length and
ratio restrictions. Check existing records before calling a counterexample new.
For a fastest flank e with integer walkers x<e, opening k is blocked iff
((8*k+1)*x) mod (8*e) is outside [e,7*e]. Period e. An explicit cover of the
whole period by <=5 walkers with no single universal blocker and no covering
pair would refute the strongest unrestricted version. Prefer existing examples
and exact bit masks over enumerating all large sets. If no example found, state
the tested bound only. Explain which hypothesis is used by twin-chain transport.

Second deliverable (reasoning only): compare reciprocal ratios e/x and x/e in
such a counterexample. Can the blocking of the fastest flank force a named
clear opening of one of its walkers? Derive any sufficient inequality using
the actual residues; do not claim all flanks cannot be dead without proof.

Limits: <=60 seconds total numerical computation, one foreground Python process,
no multiprocessing, background jobs, subagents, installations, builds, Git
actions or Lean edits. Exact integers/Fractions only. Use apply_patch for new
files prefixed transport_priority_claude_v2 under experiments/nN/redo. Limit
output to 100KB and report to 1500 words. Save results and return concise summary.
Existing files and other sessions remain untouched.
