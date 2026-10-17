#!/usr/bin/env python3
"""Assembly modules for the half-unit certificates (o7_half_lean_v1.py writes the parts and piece lists).

OrderSevenHalfAN: chunkAH i2 i2 147 = true for every i2 < 147, joined from its pieces by the split lemma.
OrderSevenHalfBN: the same for chunkBH.
OrderSevenNu2FinalN: instantiates lonely_nu2_of with A, B, C1, C2."""
import sys
outdir = sys.argv[1]

def assemble(tag, name, nmods):
    pieces = [tuple(map(int, l.split())) for l in open(f"o7_half_{tag}_pieces.txt") if l.strip()]
    by_i2 = {}
    for i2, lo3, hi3, _ in pieces:
        by_i2.setdefault(i2, []).append((lo3, hi3))
    lines = []
    for i2 in range(147):
        ps = by_i2[i2]
        assert ps[0][0] == i2 and ps[-1][1] == 147
        assert all(ps[t][1] == ps[t + 1][0] for t in range(len(ps) - 1))
        if len(ps) == 1:
            lines.append(f"theorem {name}_full_{i2} : {name} {i2} {i2} 147 = true := {name}_{i2}_{i2}")
            continue
        st = [f"theorem {name}_full_{i2} : {name} {i2} {i2} 147 = true := by",
              f"  have h0 : {name} {i2} {i2} {ps[0][1]} = true := {name}_{i2}_{i2}"]
        for t, (lo3, hi3) in enumerate(ps[1:], 1):
            st.append(f"  have h{t} : {name} {i2} {i2} {hi3} = true := by")
            st.append(f"    rw [{name}_split (by norm_num : {i2} ≤ {lo3}) (by norm_num : {lo3} ≤ {hi3}), h{t - 1}, "
                      f"{name}_{i2}_{lo3}]; rfl")
        st.append(f"  exact h{len(ps) - 1}")
        lines.append("\n".join(st))
    cases = "\n".join(f"  · exact {name}_full_{i2}" for i2 in range(147))
    letter = tag.upper()
    imports = "\n".join(f"import LonelyRunner.LRC.Spec.OrderSevenHalf{letter}P{g}N" for g in range(nmods))
    src = f'''{imports}

/-!
# Order seven, half-unit certificate {letter} assembled

`{name}_all`: `{name} i2 i2 147 = true` for every `i2 < 147`, joined from the {len(pieces)} kernel-checked pieces in
`OrderSevenHalf{letter}P*N` by `{name}_split`.  Generator: `experiments/n7_native/cascade/o7_half_assemble_v1.py`.
-/

namespace LRC.O7L3

theorem {name}_split {{i2 lo mid hi : ℕ}} (h1 : lo ≤ mid) (h2 : mid ≤ hi) :
    {name} i2 lo hi = ({name} i2 lo mid && {name} i2 mid hi) := by
  unfold {name}
  rw [show hi - lo = (mid - lo) + (hi - mid) by omega, allR_append, show lo + (mid - lo) = mid by omega]

{chr(10).join(lines)}

theorem {name}_all : ∀ i2, i2 < 147 → {name} i2 i2 147 = true := by
  intro i2 hi2
  interval_cases i2
{cases}

end LRC.O7L3
'''
    open(f"{outdir}/OrderSevenHalf{letter}N.lean", "w").write(src)
    return len(pieces)

nA = assemble("A", "chunkAH", 72)
nB = assemble("B", "chunkBH", 36)
c2cases = "\n".join(f"  · exact chunkC2_{p}" for p in range(15))
final = f'''import LonelyRunner.LRC.Spec.OrderSevenHalfAN
import LonelyRunner.LRC.Spec.OrderSevenHalfBN
import LonelyRunner.LRC.Spec.OrderSevenHalfC1N
import LonelyRunner.LRC.Spec.OrderSevenHalfCP0N
import LonelyRunner.LRC.Spec.OrderSevenHalfCP1N
import LonelyRunner.LRC.Spec.OrderSevenHalfCP2N
import LonelyRunner.LRC.Spec.OrderSevenNu2N

/-!
# Order seven: every set of at most six speeds with none divisible by 343 is lonely

`lonely_nu2` instantiates `lonely_nu2_of` with the four certificates.  The instant is a 7-adic grid point
`k / 7^a`, `a ≤ 4`.
-/

namespace LRC.O7L3
open LRC.O7Grid

theorem chunkC2_all : ∀ p, p < 15 → chunkC2 p = true := by
  intro p hp
  interval_cases p
{c2cases}

theorem lonely_nu2 {{S : Finset ℕ}} (hS : S.card ≤ 6) (h343 : ∀ d ∈ S, ¬ 343 ∣ d) :
    ∃ t : ℝ, ∀ d ∈ S, (1 : ℝ) / 7 ≤ circDist ((d : ℝ) * t) :=
  lonely_nu2_of chunkAH_all chunkBH_all chunkC1_ok chunkC2_all hS h343

end LRC.O7L3
'''
open(f"{outdir}/OrderSevenNu2FinalN.lean", "w").write(final)
print("A pieces", nA, "B pieces", nB)
