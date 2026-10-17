#!/usr/bin/env python3
"""Split an exact 3/28 kappa tree (o7_kbox_exact_v2 serialisation) into Lean modules: a skeleton (top levels) whose
leaves point into a list of (subtree, box) pairs; each module kernel-checks one batch of pairs; the final module checks
the skeleton's boxes (`skelOK`) and assembles `split_sound`.  Boxes are recomputed with the same sevenths split rule.
Usage: o7_kbox_lean_v2.py tree.txt X1num X1den Tag MAXLEAVES outdir"""
import sys, re
from fractions import Fraction as Fr
sys.setrecursionlimit(100000)
src, xn, xd, tag, MAXL, outdir = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4], int(sys.argv[5]), sys.argv[6]
toks = re.findall(r"\(|\)|[A-Z]|\d+", open(src).read()); pos = 0
def parse():
    global pos
    t = toks[pos]
    if t == "(":
        pos += 1; k = toks[pos]; pos += 1
        if k == "L":
            args = list(map(int, toks[pos:pos + 7])); pos += 7; node = ("L", args)
        elif k == "S":
            d = int(toks[pos]); pos += 1; l = parse(); r = parse(); node = ("S", d, l, r)
        else: raise ValueError(k)
        assert toks[pos] == ")"; pos += 1; return node
    if t == "E": pos += 1; return ("E",)
    raise ValueError(t)
tree = parse()
def leaves(n): return 1 if n[0] != "S" else leaves(n[2]) + leaves(n[3])
def split_pt(a, b):
    m = (a + b) / 2
    ks = [Fr(k, 7) for k in range(1, 7) if a < Fr(k, 7) < b]
    best = ks[0] if ks else m
    for z in ks:
        if abs(z - m) < abs(best - m): best = z
    return best
def lean_tree(n):
    if n[0] == "L": return "(L " + " ".join(map(str, n[1])) + ")"
    if n[0] == "E": return "E"
    return f"(S {n[1]} {lean_tree(n[2])} {lean_tree(n[3])})"
def q(x): return f"({x.numerator}/{x.denominator} : ℚ)"
def lean_box(B): return "⟨" + ", ".join(q(B[i][0]) for i in range(4)) + ", " + ", ".join(q(B[i][1]) for i in range(4)) + "⟩"
subs = []
def skel(n, B):
    if n[0] != "S" or leaves(n) <= MAXL:
        subs.append((n, B)); return f"(Sub {len(subs) - 1})"
    d = n[1]; m = split_pt(*B[d])
    l = list(B); l[d] = (B[d][0], m); r = list(B); r[d] = (m, B[d][1])
    return f"(S {d} {skel(n[2], l)} {skel(n[3], r)})"
X = Fr(xn, xd)
sk = skel(tree, [(X, Fr(1))] * 4)
# group subtrees into modules
groups = []; cur = []; cl = 0
for i, (n, B) in enumerate(subs):
    if cur and cl + leaves(n) > MAXL: groups.append(cur); cur = []; cl = 0
    cur.append(i); cl += leaves(n)
if cur: groups.append(cur)
for g, idx in enumerate(groups):
    body = ",\n  ".join(f"({lean_tree(subs[i][0])}, {lean_box(subs[i][1])})" for i in idx)
    open(f"{outdir}/OrderSevenKappaTree{tag}P{g}N.lean", "w").write(f'''import LonelyRunner.LRC.Spec.OrderSevenKappaTreeCoreN

/-! Order seven, `kappa ≥ 3/28` box tree on `x_i ∈ [{xn}/{xd}, 1]`, part {g} of {len(groups)}
(subtrees {idx[0]}..{idx[-1]}, {sum(leaves(subs[i][0]) for i in idx)} leaves); `experiments/n7_native/o7_kbox_lean_v2.py`. -/

namespace LRC.O7KTree{tag}P{g}
open LRC.O7KTree LRC.O7KTree.T

noncomputable def subs : List (T × Bx) := [
  {body}]

theorem subs_ok : subs.all (fun p => check p.1 p.2) = true := by decide +kernel

end LRC.O7KTree{tag}P{g}
''')
imports = "\n".join(f"import LonelyRunner.LRC.Spec.OrderSevenKappaTree{tag}P{g}N" for g in range(len(groups)))
allexpr = " ++ ".join(f"LRC.O7KTree{tag}P{g}.subs" for g in range(len(groups)))
oks = ", ".join(f"LRC.O7KTree{tag}P{g}.subs_ok" for g in range(len(groups)))
open(f"{outdir}/OrderSevenKappaTree{tag}N.lean", "w").write(f'''{imports}

/-!
# Order seven: `kappa ≥ 3/28` for `v1 ≥ v5 · {xn}/{xd}` (kernel-checked box tree, {len(groups)} parts)

Skeleton and assembly; the subtrees are checked in `OrderSevenKappaTree{tag}P*N`.  Tree from
`experiments/n7_native/o7_kbox_exact_v2.py` ({leaves(tree)} leaves, exact rationals, sevenths splitting).
-/

namespace LRC.O7KTree{tag}
open LRC.O7KTree LRC.O7KTree.TS LRC.O7Split

noncomputable def all : List (T × Bx) := {allexpr}

def skel : TS := {sk}

theorem skel_ok : skelOK skel (root ({xn} / {xd})) all = true := by decide +kernel

theorem all_ok : all.all (fun p => check p.1 p.2) = true := by
  simp only [all, List.all_append, {oks}, Bool.and_self]

theorem win : ∀ x, Mem (root ({xn} / {xd})) x → Win x := split_sound skel_ok all_ok

/-- **`kappa ≥ 3/28` for `{xn}/{xd} · v5 ≤ v1`.** -/
theorem kappa {{v1 v2 v3 v4 v5 : ℕ}} (h0 : 0 < v1) (h12 : v1 < v2) (h23 : v2 < v3) (h34 : v3 < v4) (h45 : v4 < v5)
    (hX : (({xn} / {xd} : ℚ) : ℝ) * v5 ≤ v1) :
    ∃ s₀ : ℝ, InBandOn {{v1, v2, v3, v4, v5}} (Set.Icc s₀ (s₀ + 3 / (28 * v5))) :=
  kappa_of_win win h0 h12 h23 h34 h45 hX

end LRC.O7KTree{tag}
''')
print(f"{leaves(tree)} leaves, {len(subs)} subtrees, {len(groups)} modules: " + ", ".join(str(sum(leaves(subs[i][0]) for i in g)) for g in groups))
