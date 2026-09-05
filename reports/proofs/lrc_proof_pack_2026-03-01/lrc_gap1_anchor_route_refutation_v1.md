# Gap 1 Candidate Route Check: Anchor One-Bad-Per-Runner Claim (Refutation)

## Candidate route tested
Candidate argument attempted to prove one-divisible prime closure by asserting:
- for nontrivial anchors `b_j=jL/n` (`j=1,...,n-1`), each non-divisible runner contributes only one bad residue,
- hence `|union_bad| <= n-2` and all anchors are safe.

## Result
This claim is false under the current bad-set model used by the certifier/theorem sequence.

Using the exact runner mask rule from the boundary certifier:
- bad iff `q=0` OR (`q=n-1` and `s!=0`) at a fiber,
- at nontrivial anchors, typical non-divisible runners satisfy `s!=0`, so many runners contribute two bad residues.

## Explicit counterexample instance (within canonical one-divisible template class)
- `n=13` (prime)
- `E_fixed=(1,2,3,4,5,6,7,8,9,10)`
- free speed `M=11`
- one divisible speed `13`

At anchors `b_j=jL/n` with `j=2,...,11`, direct exact computation gives `A_{b_j}=0`.
So nontrivial anchors are not uniformly safe.

## Consequence for Gap 1
- The proposed anchor-only analytic closure route is invalid.
- Gap 1 remains open at theorem level in canonical status.
- Existing D.3 certifications (now including `n=13,17,19` boundary batches) remain valid finite evidence.

## Scope guardrail
This note refutes a candidate proof route only. It does not negate existing proved/certified claims.
