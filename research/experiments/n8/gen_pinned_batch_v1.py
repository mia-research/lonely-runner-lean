"""Emit Lean for the fully-pinned census families (s = 6 covers: seven differences, no free parameter).

For these the U/K calculus is not needed: the arrangement is concrete, so Existence for the runner is
just "some flank has a lonely opening". The framework's clearing test makes that decidable arithmetic
(Prop 2.1, formalised as Flanks.clear_of_residue_band), so each family is one `decide`.

Selection: every distinct seven-difference set arising from an s = 6 cover. Distinct work is per
difference set, not per cover -- 6,759 covers collapse to 4,413 sets.
"""
import json, sys
from fractions import Fraction as F

n = 8; INV = F(1, n)
def fract(z): return z - (z.numerator // z.denominator)
def cd(z):    return min(fract(z), 1 - fract(z))
def band_ok(m, e, k): 
    r = (m * (n * k + 1)) % (n * e)
    return e <= r <= (n - 1) * e

def sets_and_witness():
    fams = json.load(open('experiments/n8/census_families_v1.json'))
    sets = {}
    for f in fams:
        if len(f['cover']) != 6: continue
        sets.setdefault(tuple(f['differences']), 0)
        sets[tuple(f['differences'])] += 1
    out = []
    for d, ncov in sorted(sets.items()):
        hit = None
        for e in d:
            for k in range(0, 8 * max(d) + 2):
                if all(band_ok(m, e, k) for m in d): hit = (e, k); break
            if hit: break
        assert hit, f"no flank opening for {d}"
        out.append((list(d), hit[0], hit[1], ncov))
    return out

if __name__ == '__main__':
    NPER = int(sys.argv[1]) if len(sys.argv) > 1 else 1200
    data = sets_and_witness()
    print(f"distinct fully-pinned difference sets: {len(data)}", file=sys.stderr)
    ks = [k for _, _, k, _ in data]
    print(f"opening index used: min {min(ks)} median {sorted(ks)[len(ks)//2]} max {max(ks)}", file=sys.stderr)
    chunks = [data[i:i+NPER] for i in range(0, len(data), NPER)]
    names = []
    for ci, ch in enumerate(chunks, 1):
        nm = f"PinnedBatch{ci}"
        names.append(nm)
        L = ["import LonelyRunner.LRC.Cascade.Flanks", "",
             "/-!", f"# Fully-pinned census families, part {ci} of {len(chunks)}", "",
             "Part of the cascade artefact (`LRC/Cascade/`).  Threshold `1/8`.", "",
             "Each theorem is one seven-difference arrangement from an `s = 6` census cover — fully pinned,",
             "so there is no free parameter and Existence for the runner is just that some flank has a lonely",
             "opening.  The framework's clearing test (`Flanks.clear_of_residue_band`, Proposition 2.1) makes",
             "that decidable arithmetic, so each family closes by `decide` on the residue band.", "",
             "Emitted by `experiments/n8/gen_pinned_batch_v1.py`; data recomputed and cross-checked in",
             "`experiments/n8/census_export_v1.py`.", "-/", "",
             "set_option maxHeartbeats 1000000", "",
             f"namespace {nm}", "", "open MomentIterationN Flanks", ""]
        for i, (d, e, k, ncov) in enumerate(ch, 1):
            lst = "[" + ", ".join(map(str, d)) + "]"
            L.append(f"/-- Differences `{lst}`, flank `{e}`, opening `{k}`.  Covers {ncov} census rows. -/")
            L.append(f"theorem fam_{ci}_{i} : ∃ k : ℕ, Lonely 8 (({lst}.map "
                     f"(Nat.cast : ℕ → ℝ)).toFinset) (Flanks.flankOpening 8 (({e} : ℕ) : ℝ) k) :=")
            L.append(f"  ⟨{k}, Flanks.lonely_of_band_list (n := 8) (L := {lst}) (e := {e}) (k := {k})")
            L.append(f"    (by norm_num) (by decide)⟩")
            L.append("")
        L.append(f"end {nm}")
        L.append("")
        open(f'LonelyRunner/LonelyRunner/LRC/Cascade/{nm}.lean', 'w').write("\n".join(L))
        print(f"  wrote {nm}.lean: {len(ch)} families, {len(L)} lines", file=sys.stderr)
    print("MODULES " + " ".join(names))
