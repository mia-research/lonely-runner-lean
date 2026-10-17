#!/usr/bin/env python3
"""Write the Lean module for the exact 3/28 kappa box tree (o7_kbox_exact_v2 serialisation).
Usage: o7_kbox_lean_v1.py tree.txt X1num X1den ModuleName Namespace out.lean"""
import sys
tree, xn, xd, mod, ns, out = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4], sys.argv[5], sys.argv[6]
t = open(tree).read().strip()
src = f'''import LonelyRunner.LRC.Spec.OrderSevenKappaTreeCoreN

/-!
# Order seven: `kappa ≥ 3/28` on the ratio box `x_i = v_i / v5 ∈ [{xn}/{xd}, 1]` (kernel-checked box tree)

Tree from `experiments/n7_native/o7_kbox_exact_v2.py` (exact rationals, sevenths splitting); checker and soundness in
`OrderSevenKappaTreeCoreN`.
-/

namespace {ns}
open LRC.O7KTree LRC.O7KTree.T

noncomputable def tree : T :=
  {t}

theorem tree_ok : check tree (root ({xn} / {xd})) = true := by decide +kernel

end {ns}
'''
open(out, "w").write(src)
