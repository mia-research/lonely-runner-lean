# Symbolic window checkpoint — 3 October 2026

Resume from `VariableCoreReplacementN.family_isolated`.

Completed: finite-window endpoint continuation under bounded witnesses;
exact single-reading obstruction and its derived finite label bound;
general compatibility of prescribed obstruction labels; fixed-core and then
variable-core replacement families. `MappedCascadeRulesN` carries the earlier
capture product rule with its hypotheses explicit.

The variable-core theorem covers the region tabulated in
`variable_core_replacement_v1.md`, with every inserted speed >=19/3.
The global n=8 proof is NOT complete. Next: neighbouring core regions where
the selected fixed window bounds fail; permit moving endpoints or new labels
and prove exhaustive coverage rather than assuming it.

Targeted builds and axiom audits passed for the recent window modules. No full
Spec gate was run by this session. The exact insertion diagnostic passes.
No worker from this session remains running. Claude access was restored, but
its last delegated compatibility check was declined and supplied no result.

This checkpoint deliberately excludes unrelated dirty source and experiments.
Several older untracked modules remain in the shared checkout; they have not
all been swept into this commit. SymbolicWindowTransportN is included because
FiniteWindowContinuationN imports it. Its SymbolicWindowFamilyN companion and
existing audit are included together to retain a runnable audit dependency.

Publication uses a new `codex/n8-symbolic-window-replacement` branch at origin,
without switching the shared local branch or advancing its existing upstream.
The published branch necessarily includes the existing local ancestor history.
