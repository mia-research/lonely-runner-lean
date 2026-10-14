"""Emit Lean for a batch of census families through Flanks.lonely_of_flank_unkillable.

Input: experiments/n8/census_families_v1.json (recomputed, cross-checked against the batch machine).
Selection: s = 5 covers (one free parameter), a flank with K empty on BOTH our count and the machine's,
and q = e/P = 1 so the on-lattice values of x are exactly the integers.

Distinct work is per (difference set, flank), not per cover -- many covers scale to the same family.

Every clearance fact reduces to Flanks.circDist_ge_of_band: the phase is written p/(8e) + c with
e <= p <= 7e. Membership in U guarantees the decomposition lands in the band, so the plan is validated
before a line is written and a failure is a bug, not a proof obligation.
"""
import json, ast, os, sys
from fractions import Fraction as F

n = 8; INV = F(1, n)
def fract(z): return z - (z.numerator // z.denominator)
def cd(z):    return min(fract(z), 1 - fract(z))
def clear(d, e, k): return cd(F(d) * ((F(k) + INV) / e)) >= INV
def dec(d, r, e):
    M8 = n * e; num = d * (n * r + 1); c = num // M8; p = num - M8 * c
    assert e <= p <= (n - 1) * e, f"band fail d={d} r={r} e={e} p={p}"
    return p, c

def instances():
    fams = json.load(open('experiments/n8/census_families_v1.json'))
    SRC = os.path.expanduser('~/ZCodeProject/lrc-n8/results/batch_machine_v1.out')
    mach = {}
    for l in open(SRC):
        if not l.strip().startswith('((('): continue
        cover, rep = ast.literal_eval(l.strip())
        mach[tuple(map(tuple, cover))] = rep
    seen = {}
    for f in fams:
        if len(f['cover']) != 5: continue
        rep = mach[tuple(map(tuple, f['cover']))]
        for fl in f['flanks']:
            if not fl['always_free'] or fl['q'] != 1: continue
            m = rep['flanks'].get(fl['e_frac'])
            if not (m and m[0] != 'DEAD' and m[3] == []): continue
            key = (tuple(f['differences']), fl['e'], fl['P'], tuple(fl['U']))
            seen.setdefault(key, 0); seen[key] += 1; break
    return sorted(seen.items(), key=lambda kv: (max(kv[0][0]), kv[0]))

def emit(idx, diffs, e, P, U, ncov):
    M = max(diffs); fixed = list(diffs)
    body = fixed[:-1] + ['x'] + [fixed[-1]]
    setlit = "{" + ", ".join(str(b) for b in body) + "}"
    kill = {}
    for x in range(1, M):
        for r in U:
            for j in range(3):
                if clear(x, e, r + j * P):
                    kill[x] = (r, j, dec(x, r + j * P, e)); break
            if x in kill: break
        assert x in kill, f"family {idx}: on-lattice x = {x} not cleared"
    L = []
    L.append(f"/-- **Family {idx}**: differences `{setlit}`, flank `{e}`, period `{P}`, "
             f"uncovered residues `{{{', '.join(map(str,U))}}}`.  Covers {ncov} census rows. -/")
    L.append(f"theorem family{idx}_lonely (x : ℝ) (hx0 : 0 < x) (hxM : x < {M}) :")
    L.append(f"    ∃ k : ℕ, Lonely 8 ({setlit} : Finset ℝ) (Flanks.flankOpening 8 {e} k) := by")
    L.append(f"  have hq : (({e} : ℕ) : ℝ) * (x / {e}) = x := by push_cast; ring")
    L.append(f"  refine Flanks.lonely_of_flank_unkillable (n := 8) (x := x) (by norm_num) (by norm_num)"
             f" {P}")
    L.append(f"    {{{', '.join(map(str,U))}}} ⟨{U[0]}, by decide⟩ ?_ ?_ ?_")
    # hlat
    L.append("  · intro d hd hdx")
    L.append("    simp only [Finset.mem_insert, Finset.mem_singleton] at hd")
    L.append(f"    have hc : (({P} : ℕ) : ℝ) * (d / {e}) = d * {P} / {e} := by push_cast; ring")
    L.append("    rw [hc]")
    L.append("    rcases hd with " + " | ".join(["h"] * len(body)) + " <;> rw [h]")
    for b in body:
        if b == 'x':
            L.append("    · exact absurd h hdx")
        else:
            v = F(b * P, e); assert v.denominator == 1, f"not on lattice: {b}"
            L.append(f"    · rw [show ({b} : ℝ) * {P} / {e} = (({v.numerator} : ℤ) : ℝ) by norm_num]")
            L.append(f"      exact Int.fract_intCast {v.numerator}")
    # hU
    L.append("  · intro r hr d hd hdx")
    L.append("    simp only [Finset.mem_insert, Finset.mem_singleton] at hd hr")
    L.append("    rcases hr with " + " | ".join(["hr"] * len(U)) + " <;> subst hr")
    for r in U:
        L.append("    · rcases hd with " + " | ".join(["h"] * len(body)))
        for b in body:
            if b == 'x':
                L.append("      · exact absurd h hdx")
            else:
                p, c = dec(b, r, e)
                L.append(f"      · rw [h, show ({b} : ℝ) * Flanks.flankOpening 8 {e} {r}"
                         f" = ({p} : ℝ)/{n*e} + (({c} : ℤ) : ℝ) by")
                L.append("          unfold Flanks.flankOpening; push_cast; ring]")
                L.append(f"        exact Flanks.circDist_ge_of_band (n := 8) {c} (by norm_num) (by norm_num)")
    # hkill
    L.append("  · intro hlat")
    L.append("    rw [hq] at hlat")
    L.append("    have hxi : x = ((⌊x⌋ : ℤ) : ℝ) := by")
    L.append("      have hh : Int.fract x = x - (⌊x⌋ : ℝ) := rfl")
    L.append("      rw [hlat] at hh; linarith")
    L.append("    have hm1 : 1 ≤ ⌊x⌋ := by")
    L.append("      have hh : (0 : ℝ) < ((⌊x⌋ : ℤ) : ℝ) := by rw [← hxi]; exact hx0")
    L.append("      have hh' : (0 : ℤ) < ⌊x⌋ := by exact_mod_cast hh")
    L.append("      omega")
    L.append(f"    have hm2 : ⌊x⌋ ≤ {M-1} := by")
    L.append(f"      have hh : ((⌊x⌋ : ℤ) : ℝ) < {M} := by rw [← hxi]; exact hxM")
    L.append(f"      have hh' : (⌊x⌋ : ℤ) < {M} := by exact_mod_cast hh")
    L.append("      omega")
    L.append("    rw [hxi]")
    L.append("    interval_cases h : ⌊x⌋")
    for xv in range(1, M):
        r, j, (p, c) = kill[xv]; k = r + j * P
        L.append(f"    · refine ⟨{r}, by decide, {j}, ?_⟩")
        L.append(f"      rw [show ({r} : ℕ) + {j} * {P} = {k} from rfl,")
        L.append(f"        show ((({xv} : ℤ)) : ℝ) * Flanks.flankOpening 8 {e} {k}"
                 f" = ({p} : ℝ)/{n*e} + (({c} : ℤ) : ℝ) by")
        L.append("          unfold Flanks.flankOpening; push_cast; ring]")
        L.append(f"      exact Flanks.circDist_ge_of_band (n := 8) {c} (by norm_num) (by norm_num)")
    L.append("")
    return L

if __name__ == '__main__':
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 12
    SKIP = int(sys.argv[2]) if len(sys.argv) > 2 else 0
    inst = instances()
    print(f"distinct instances available: {len(inst)}", file=sys.stderr)
    out = ["import LonelyRunner.LRC.Cascade.EighthFamily", "",
           "/-!", "# Census families, emitted", "",
           "Part of the cascade artefact (`LRC/Cascade/`).  Threshold `1/8`.", "",
           "Each theorem below takes one census family through `Flanks.lonely_of_flank_unkillable`.",
           "The family data — flank, period, uncovered residues — is the batch machine's own, recomputed",
           "and cross-checked in `experiments/n8/census_export_v1.py`; the Lean is emitted by",
           "`experiments/n8/gen_census_batch_v1.py`.  Every clearance fact reduces to",
           "`Flanks.circDist_ge_of_band`.", "",
           "Selection: covers with one free parameter, a flank whose killer set is empty on both counts,",
           "and `e/P = 1` so the on-lattice values of the free parameter are the integers.", "-/", "",
           "set_option linter.unusedVariables false", "set_option maxHeartbeats 1000000", "",
           "namespace CensusBatch", "",
           "open ConstructionN MomentIterationN Flanks EighthFamily", ""]
    used = 0
    for i, ((diffs, e, P, U), ncov) in enumerate(inst[SKIP:SKIP+N]):
        out += emit(SKIP + i + 1, diffs, e, P, list(U), ncov); used += 1
    out += ["end CensusBatch", ""]
    open('LonelyRunner/LonelyRunner/LRC/Cascade/CensusBatch.lean', 'w').write("\n".join(out))
    print(f"emitted {used} families, {len(out)} lines", file=sys.stderr)
