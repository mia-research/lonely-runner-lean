# User's EXACT D-recursion — validated + (X,Y) leak test (2026-07-10)

The user supplied the exact recursion (source), ending the guessing:
```
D_i = N // |e_{i-1}| ;  c_i = N // D_i ;  e_i = |e_{i-1}| - c_i ;  stop at 0
```
with **N = 2^P** (full range) applied to the error/key. `d_recursion_exact_v1.py`
reproduces the user's Findings B ([2,41,1722]) and C (6–7-term scaling signatures)
exactly. This is the greedy nearest-unit-fraction ("D-signature") expansion.

## Clarifications (correcting my earlier wrong recursion)
- My earlier "4–5 terms, saturates" used the WRONG input (small residual d−base with
  N=2^{P−1}). With the correct recursion on the full error, **random keys give ~6–8
  terms**: 80-bit→6.0, 160-bit→7.0, 256-bit→7.7 (max 9). Grows slowly with bits.
- **10–11 terms needs deliberate structure** (~9 fraction layers); random/real keys
  don't reach it.
- **Real solved keys look RANDOM** (~5–7 terms), NOT the "few fixed structural terms
  + one big residual" pattern of a sum-of-fractions construction. No evidence the
  real puzzle keys were built from simple fractions.
- The D-signature is an INVERTIBLE encoding of the key (user Finding E); early terms
  = coarse structure, final term = residual scaling with bit size.

## (X,Y) → D-signature terms: NULL (validated)
64,020 cached keys (bits 64–130), D-signature via the exact recursion. Tested (X,Y)
features {X mod ℓ, X·Y mod ℓ, v_ℓ} vs each term D_1…D_5, ℓ∈{7,13}, MI + exclusion,
permutation-validated. Controls (d mod ℓ full + 40% corrupted) fire at floor p=0.005.
**Every term null** (|z| ≤ 2.3, no flag). (X,Y) constrains no D-signature term — so
via reconstruct_error it yields no search reduction on the key. ECDLP holds on the
correct object too.

## The genuinely new direction this unlocks (independent of X,Y)
Because the D-signature is an invertible encoding AND structured keys have tell-tale
signatures (fixed small early terms), the sharp question is now about the KEYS
themselves, not (X,Y): **do the real solved keys share fixed early D-terms** (which
would betray a sum-of-simple-fractions construction / a creator fingerprint)? That is
a property of the 82 keys directly — testable, and the natural next probe. Early
look: real keys' signature lengths (~5–7) sit in the random range, so no obvious
fractional construction — but the shared-early-term test hasn't been run.

## Status
The (X,Y)-leak question is now answered on the user's OWN exact object: null. The
open thread moved: from "does (X,Y) leak the recursion" (answered no) to "do the
keys themselves carry constructive D-signature structure" (untested, low-n but
directly on the real keys).
