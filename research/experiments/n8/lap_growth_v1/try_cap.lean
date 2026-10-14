import LonelyRunner.LRC.Spec.Target
open LRC.Spec

-- Literally: can anything in the tree, or any automation, close it?
example : CascadeCapped := by exact?

example : CascadeCapped := by
  unfold CascadeCapped
  aesop
