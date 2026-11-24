import Fresh.ZoneCover

/-!
# A flat encoding of zone certificate trees (2026-11-22)

New file; nothing existing is edited.

Nested `ZT` term literals exhaust the elaborator's heartbeats at the size of the larger M4
chunks (`C_4_5_6`, 748 KB: deterministic timeout at `isDefEq`).  A certificate is therefore
written as a prefix code in `List ℕ` and decoded by the kernel:

* `0 :: m₀ :: … :: m₆ :: rest` is `.leaf [m₀, …, m₆]`;
* `1 :: r :: s :: p :: q :: rest` is `.cut r s p q a b`, with `a` then `b` decoded from `rest`.

`dec1` is total (a malformed code decodes to `.leaf []`), so no soundness lemma is needed:
`Fresh.M4ZoneAssembly.zchunk v w x cs = true` is sound for every `cs : List ZT`, whatever
produced it.
-/

namespace Fresh.ZoneCover

/-- Prefix decoder with fuel; returns the tree and the unread suffix. -/
def decT : ℕ → List ℕ → Option (ZT × List ℕ)
  | 0, _ => none
  | _ + 1, 0 :: m0 :: m1 :: m2 :: m3 :: m4 :: m5 :: m6 :: rest =>
      some (.leaf [m0, m1, m2, m3, m4, m5, m6], rest)
  | f + 1, 1 :: r :: s :: p :: q :: rest =>
      match decT f rest with
      | some (a, rest') =>
          match decT f rest' with
          | some (b, rest'') => some (.cut r s p q a b, rest'')
          | none => none
      | none => none
  | _ + 1, _ => none

/-- Decode one certificate (fuel 1000 bounds the depth). -/
def ZT.dec1 (l : List ℕ) : ZT :=
  match decT 1000 l with
  | some (t, _) => t
  | none => .leaf []

example : ZT.dec1 [1, 4, 3, 7, 9, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 1, 1, 2] =
    .cut 4 3 7 9 (.leaf [0, 0, 0, 0, 1, 1, 1]) (.leaf [0, 0, 0, 0, 1, 1, 2]) := rfl

end Fresh.ZoneCover
