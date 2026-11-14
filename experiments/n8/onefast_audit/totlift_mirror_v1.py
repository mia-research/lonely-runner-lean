# totlift_mirror_v1.py -- builds the standalone-Mathlib bridge mirror of the one-sided
# sections of Fresh/TotalityLifts.lean (compfam_bridge_mirror.lean pattern, batched).
#
# Per batch (10 boxes): the banked Fresh bodies pasted VERBATIM with (a) `import Fresh.*`
# lines stripped, (b) the declarations UNUSED by the one-sided template dropped (to fit the
# bridge's 120s server cap -- every dropped theorem is ./check.sh-verified inside its own
# Fresh file), and (c) the batch's compFam record blocks verbatim + a BATCH-LOCAL
# coveredSet / compFamOf / oneSidedTotalData regenerated over exactly those boxes (the real
# 68-element versions are verbatim in Fresh/ComposedFamData.lean; their 68-deep membership
# walks are ./check.sh-verified).  The Fresh.TotalityLifts body is totlift_gen_v1.py
# --mirror's output (one-sided sections + retargetings + totals, verbatim).  The D-variants
# (Fresh.DumpDomData) and the 5 pairwise instances (Fresh.SpineTotalData) are NOT mirrored --
# they add no new wiring and are ./check.sh-verified.
#
# NEW files only; nothing existing is modified.  Nothing committed.
import os, re, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
FRESH = os.path.abspath(os.path.join(HERE, '..', '..', '..', 'LonelyRunnerFresh', 'Fresh'))
OUT = os.path.join(HERE, 'totlift_bridge_mirror_v1.lean')
OUT_BATCH = os.path.join(HERE, 'totlift_bridge_mirror_v1_batch.lean')

def body_of(fn, first_ns):
    """Everything after the imports, from the first given top-level declaration on."""
    src = open(os.path.join(FRESH, fn)).read()
    i = src.find(first_ns)
    assert i >= 0, (fn, first_ns)
    return src[i:].rstrip() + '\n'

def drop_decls(body, names):
    # line-based removal of `theorem|def <name> ...` blocks: the declaration (from its
    # header line to its own `#print axioms <name>` line, or to the next declaration /
    # `end` for defs) plus any immediately-preceding contiguous docstring (whose orphaning
    # would break the parse: a docstring must precede a declaration)
    for nm in sorted(names):
        lines = body.split('\n')
        out = []
        i = 0
        removed = False
        hdr = re.compile(r'(?:noncomputable )?(?:theorem|def) ' + re.escape(nm) + r'(?:\s|$)')
        nxt = re.compile(r'(?:noncomputable )?(?:theorem|def) |end Fresh|namespace Fresh|-- STANDING')
        while i < len(lines):
            if hdr.match(lines[i]):
                removed = True
                # consume forward to the own #print line (inclusive) or the next decl
                j = i
                own_print = '#print axioms ' + nm
                while j < len(lines) and j - i < 400:
                    if lines[j].strip() == own_print:
                        j += 1
                        break
                    if j > i and nxt.match(lines[j]):
                        break
                    j += 1
                # remove the preceding contiguous docstring: pop blank lines, then the
                # block of lines from the '/--' opener through the '-/' closer
                while out and out[-1].strip() == '':
                    out.pop()
                if out and out[-1].strip().endswith('-/'):
                    out.pop()
                    while out and not out[-1].lstrip().startswith('/--'):
                        out.pop()
                    if out:
                        out.pop()
                i = j
                continue
            out.append(lines[i])
            i += 1
        assert removed, 'drop missed: ' + nm
        body = '\n'.join(out)
    return body

MIN_DISTINT = '''namespace Fresh

noncomputable def distInt (x : ℝ) : ℝ := |x - (round x : ℝ)|

end Fresh
'''

MIN_FILTERASSEMBLY = '''namespace Fresh.FilterAssembly

noncomputable def FaceLo (n : Fin 7 → ℤ) (i : Fin 7) : ℝ := ((max (2 * n i - 1) 2 : ℤ) : ℝ) / 2

noncomputable def FaceHi (n : Fin 7 → ℤ) (i : Fin 7) : ℝ := ((2 * n i + 1 : ℤ) : ℝ) / 2

/-- A raw-edge conflict datum (verbatim from Fresh/FilterAssembly.lean). -/
structure JoinEdge where
  x : Fin 7
  y : Fin 7
  A : ℤ
  B : ℤ
  C : ℤ
  D : ℤ
deriving DecidableEq

/-- The covering hypothesis's range check (verbatim). -/
def InRange17 (n : Fin 7 → ℤ) : Prop := ∀ i, 1 ≤ n i ∧ n i ≤ 17

instance (n : Fin 7 → ℤ) : Decidable (InRange17 n) := Fintype.decidableForallFintype

end Fresh.FilterAssembly
'''

MIN_FRONTIER = '''namespace Fresh.FrontierFamilyCap

/-- A carve of `[1,7]` (verbatim from Fresh/FrontierFamilyCap.lean). -/
def CarvesOneSeven (rs : Finset ℝ) : Prop :=
  ∀ R : ℝ, 1 ≤ R → R ≤ 7 → ∃ ρ ∈ rs, ∃ j : ℤ,
    ((j : ℝ)) * 8 - 1 < ρ * R ∧ ρ * R < ((j : ℝ)) * 8 + 1

end Fresh.FrontierFamilyCap
'''

MIN_SPINESOUND = '''namespace Fresh.SpineSound

open Fresh.FilterAssembly

/-- The box faces are positive (verbatim from Fresh/SpineSound.lean). -/
theorem faceLo_pos (n : Fin 7 → ℤ) (i : Fin 7) : 0 < FaceLo n i := by
  unfold FaceLo
  have h3 : (0 : ℤ) < max (2 * n i - 1) 2 :=
    lt_of_lt_of_le (by norm_num : (0 : ℤ) < 2) (le_max_right _ _)
  exact div_pos (by exact_mod_cast h3) (by norm_num : (0 : ℝ) < 2)

/-- Every arrangement in a box has positive readings (verbatim). -/
theorem face_pos {n : Fin 7 → ℤ} {g : Fin 7 → ℝ}
    (hface : ∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i) (i : Fin 7) : 0 < g i :=
  lt_of_lt_of_le (faceLo_pos n i) (hface i).1

end Fresh.SpineSound
'''

HEADER = '''import Mathlib

/-!
## BRIDGE MIRROR (artifact: totlift_bridge_mirror_v1[_batch].lean, built by
totlift_mirror_v1.py)

Standalone-Mathlib mirror of Fresh/TotalityLifts.lean's one-sided sections (the
compfam_bridge_mirror.lean pattern, batched).  Per batch: the banked Fresh bodies pasted
VERBATIM -- `import Fresh.*` lines stripped, the declarations UNUSED by the one-sided
template dropped (each dropped theorem is ./check.sh-verified inside its own Fresh file),
every namespace the pasted bodies open present in the mirror -- plus the batch's compFam
record blocks VERBATIM from Fresh/ComposedFamData.lean with a BATCH-LOCAL coveredSet /
compFamOf / oneSidedTotalData regenerated over exactly those boxes (the real 68-element
versions are verbatim in Fresh/ComposedFamData.lean; their 68-deep membership walks are
./check.sh-verified).  The Fresh.TotalityLifts body at the end is totlift_gen_v1.py
--mirror's output (the one-sided sections + retargetings + totals of
Fresh/TotalityLifts.lean verbatim, at the batch's coveredSet).  The D-variants
(Fresh.DumpDomData) and the 5 pairwise instances (Fresh.SpineTotalData) are NOT mirrored --
they add no new wiring and are ./check.sh-verified.  The #print axioms outputs of the
mirrored theorems apply verbatim to the real file.  The bridge's `lake env lean` search
path lacks LonelyRunnerFresh/build, hence the mirror (gate on verified/return_code, never
`success`).
-/

'''

def batch_boxes(cli):
    # the generator's ordering: the 11 strict boxes first, then the remaining 57
    def finset_boxes(src, defname):
        m = re.search(r'def\s+' + defname + r'\b[^:]*:\s*Finset[^:]*:=\s*\{(.*?)\}\s*\n', src, re.S)
        assert m, defname
        return [tuple(int(x) for x in t.strip().split(','))
                for t in re.findall(r'!\[\s*([0-9,\s]+?)\]', m.group(1))]
    src_comp = open(os.path.join(FRESH, 'ComposedFamData.lean')).read()
    src_dump = open(os.path.join(FRESH, 'DumpDomData.lean')).read()
    covered = finset_boxes(src_comp, 'coveredSet')
    strict = finset_boxes(src_dump, 'strictBoxes')
    sset = set(strict)
    one_sided = strict + [b for b in covered if b not in sset]
    skip = n = 0
    for a in cli:
        if a.startswith('--skip='):
            skip = int(a.split('=')[1])
        if a.startswith('--n='):
            n = int(a.split('=')[1])
    boxes = one_sided[skip:]
    if n:
        boxes = boxes[:n]
    return boxes

def compfam_section(boxes):
    # the batch's compFam record blocks VERBATIM (docstring + def + datum theorem + print,
    # sliced from Fresh/ComposedFamData.lean), plus a BATCH-LOCAL coveredSet / compFamOf /
    # oneSidedTotalData regenerated over exactly those boxes
    src = open(os.path.join(FRESH, 'ComposedFamData.lean')).read()
    def nm_of(b):
        return '_'.join(str(v) for v in b)
    out = ['namespace Fresh.OneSidedComposed', '', 'open Fresh.JoinFamComposed', '']
    for b in boxes:
        nm = nm_of(b)
        m = re.search(r'(?:/--[^\n]*\n)?noncomputable def compFam_' + re.escape(nm) +
                      r'\b.*?#print axioms compFamData_' + re.escape(nm), src, re.S)
        assert m, nm
        out.append(m.group(0))
        out.append('')
    lits = ['![' + ', '.join(str(v) for v in b) + ']' for b in boxes]
    out.append('/-- batch-local coveredSet: the ' + str(len(boxes)) + ' boxes of this bridge batch. -/')
    out.append('def coveredSet : Finset (Fin 7 → ℤ) :=')
    out.append('  {' + (',\n   '.join(lits)) + '}')
    out.append('')
    out.append('/-- batch-local `compFamOf` dispatch (the real 68-branch dispatch is verbatim in')
    out.append('Fresh/ComposedFamData.lean). -/')
    out.append('noncomputable def compFamOf (b : Fin 7 → ℤ) : ComposedFam :=')
    out.append('  if b = (' + lits[0] + ' : Fin 7 → ℤ) then compFam_' + nm_of(boxes[0]))
    for b, lx in zip(boxes[1:], lits[1:]):
        out.append('  else if b = (' + lx + ' : Fin 7 → ℤ) then compFam_' + nm_of(b))
    out.append('  else ⟨[]⟩')
    out.append('')
    out.append("/-- batch-local `oneSidedTotalData` (the real [T 68/68] theorem is verbatim in")
    out.append("Fresh/ComposedFamData.lean; same proof shape over the batch's boxes). -/")
    out.append('theorem oneSidedTotalData : ∀ b ∈ coveredSet, ComposedFamData (compFamOf b) := by')
    out.append('  intro b hb')
    out.append('  simp only [coveredSet, Finset.mem_insert, Finset.mem_singleton] at hb')
    out.append('  rcases hb with ' + ' | '.join(['rfl'] * len(boxes)))
    for b in boxes:
        out.append('  · simp [compFamOf, compFamData_' + nm_of(b) + ']')
    out.append('')
    out.append('#print axioms oneSidedTotalData')
    out.append('')
    out.append('end Fresh.OneSidedComposed')
    return '\n'.join(out) + '\n'

def main():
    cli = [x for a in sys.argv[1:] for x in a.split()]  # allow "--skip=0 --n=10" as one arg
    gen_args = ['python3', '-I', os.path.join(HERE, 'totlift_gen_v1.py'), '--mirror']
    for a in cli:
        if a.startswith('--n=') or a.startswith('--skip='):
            gen_args.append(a)
    body = subprocess.run(gen_args, cwd=HERE, capture_output=True, text=True, check=True).stdout

    parts = [HEADER]
    parts.append(MIN_DISTINT)
    parts.append('\n')
    parts.append(MIN_FILTERASSEMBLY)
    parts.append('\n')
    parts.append(MIN_FRONTIER)
    parts.append('\n')
    parts.append(MIN_SPINESOUND)
    parts.append('\n')
    parts.append(drop_decls(
        body_of('JoinFamComposed.lean', 'namespace Fresh.JoinFamComposed'),
        {'joinEdge_n1_composed', 'compFam12568', 'composedFamData_12568',
         'composedRefute_box_12568', 'composedRefute_box_12568_fam'}))
    parts.append('\n')
    parts.append(compfam_section(batch_boxes(cli)))
    parts.append('\n')
    parts.append(drop_decls(
        body_of('OneSidedGlue.lean', 'namespace Fresh.OneSidedGlue'),
        {'chainReal_singleton', 'capChainsRealized_of_rawCaps', 'composedEdge_pos',
         'oneSidedKill_of_composedData', 'oneSidedKill_allEdges',
         "oneSidedSound_of_composedData'", 'glue_conclusion_shape'}))
    parts.append('\n')
    parts.append(drop_decls(
        body_of('WordCoverSide.lean', 'namespace Fresh.WordCoverSide'),
        {'oneSidedSound_of_wordCover'}))
    parts.append('\n')
    parts.append(body)
    out = OUT_BATCH if any(a.startswith(('--n=', '--skip=')) for a in cli) else OUT
    open(out, 'w').write('\n'.join(parts))
    n_lines = len(open(out).read().split('\n'))
    print('wrote %s (%d lines)' % (out, n_lines))

if __name__ == '__main__':
    main()
