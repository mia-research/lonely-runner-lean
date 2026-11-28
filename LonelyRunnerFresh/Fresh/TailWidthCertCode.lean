import Fresh.TailStrip49CertCode

/-!
# Compact certificate codes for the four width checks (E984): definitions only

Written 2026-11-28.  New file; nothing existing is edited.

The four `native_decide` width checks of E927,
`smallSlowWidthCheck` / `slowCap51WidthCheck` (`Fresh/TailSlowWidth.lean:10, 23`) and
`twoFastWidthCheck` / `threeFastWidthCheck` (`Fresh/TailTwoFast.lean:40, 66`), are each
`(List.range' 1 26).all (checkFirstWith accept)` with
`accept = cappedWidthCover cap den` (the first two) and
`accept = paddedWidthCover copies den` (the last two, through `cappedWidthCover 17`).

As in E928/E929 for `stripCheck`, the search is moved out of the kernel: a certificate
records the subdivision tree, and at each leaf the branch of the box test that fired.
The three leaf kinds carry the three disjuncts of the width route's box test:

* padded leaf (`code = 0`, bit 0 = 0, `k = code/2 = 0`): the padded disjunct
  `(List.finRange 5).any fun i => i.val < copies ∧ scale < box.lo i`;
* empty leaf (`code = 2`, bit 0 = 0, `k = 1`): the capped disjunct
  `cap * scale < box.lo 4`;
* width leaf (`k ≥ 2`): one explicit cell, `decodeCell box (k - 2)`, checked against the
  worked box `workBox copies cap box` by `slowCheck` and for width by `wideCell den`.
  The cell is named exactly as in `decodeCell`: a 10-bit low bound code and a 10-bit high
  bound code, each `128·src + j` (a face endpoint `(8j+1)/box.lo src` or `(8j+7)/box.hi src`
  for `src < 5`) or the window endpoint (`1, 9` low, `7, 15` high, over `scale`, `src = 5`).
* split (bit 0 = 1): the next 24 bits are the length `L` in bits of the left child's code;
  then the left code (`L` bits), then the right code (the rest).  Splits follow
  `coverWith`'s `widest`/`left`/`right`, as in `checkCode`.

Soundness is in `Fresh.TailWidthCert`.  The extractor (`experiments/n8/tail_kernel_v1/`)
emits these codes from the same recursion `coverWith` runs; any code that passes
`checkWCode` gives the conclusion, so the extractor is untrusted.
-/

namespace Fresh.TailWidthCert

open Fresh.TailStrip49 Fresh.TailStrip49Cert

/-- The box a width leaf's cell is checked against: `cappedWidthCover`'s clip
applied to `paddedWidthCover`'s pad.  For `copies = 0` this is the clip of
`cappedWidthCover cap den`; for `cap = 17` it is the composed box
`paddedWidthCover copies den` passes to `cappedWidthCover 17`. -/
def workBox (copies cap : Nat) (box : Box) : Box :=
  ⟨box.lo, fun i => min (cap * scale) (if i.val < copies then scale else box.hi i)⟩

/-- The three disjunct leaf kinds of the width route's box test. -/
def widthLeafOK (copies cap den : Nat) (box : Box) (k : Nat) : Bool :=
  if k = 0 then
    (List.finRange 5).any fun i => decide (i.val < copies ∧ scale < box.lo i)
  else if k = 1 then decide (cap * scale < box.lo 4)
  else
    slowCheck (workBox copies cap box) (decodeCell box (k - 2)) &&
      wideCell den (decodeCell box (k - 2))

/-- Check a coded width certificate on a box, with recursion depth `d`. -/
def checkWCode (copies cap den : Nat) : Nat → Box → Nat → Bool
  | 0, _, _ => false
  | d+1, box, code =>
    if code % 2 = 0 then widthLeafOK copies cap den box (code / 2)
    else
      checkWCode copies cap den d (left box (widest box))
        (code / 33554432 % 2 ^ (code / 2 % 16777216)) &&
      checkWCode copies cap den d (right box (widest box))
        (code / 33554432 / 2 ^ (code / 2 % 16777216))

/-- A run of consecutive roots of slice `a`, from index `s`, each with its width code. -/
def wChunkOK (copies cap den a s : Nat) (codes : List Nat) : Bool :=
  let ts := ((rootTuples a).drop s).take codes.length
  decide (ts.length = codes.length) && (ts.zip codes).all fun p =>
    checkWCode copies cap den 40 (rootOf p.1) p.2

end Fresh.TailWidthCert
