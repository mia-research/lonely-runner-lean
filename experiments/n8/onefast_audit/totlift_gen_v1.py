# totlift_gen_v1.py -- generator for Fresh/TotalityLifts.lean (the mechanical per-box
# totality lift instantiations: 68 one-sided boxes + 5 pairwise boxes, mirroring the
# spineFamData pattern).
#
# Chain per box (all banked pieces, no new mathematics):
#   ComposedFamData (compFam_<box>, [T 68/68], Fresh.ComposedFamData)
#     -> composedConflict_<box>   (the word-cover kill: oneSidedTotalData consumed through
#        the composed-cap engine wordCover_demands -> composedFamRefutes -> composedCap_conflict)
#     -> totalLift_<box>          (ComposedTotalOneSided instance, from the two data-side
#        OWEDs NoClearPointWordRealized + FamilyCoversWordEdges)
#     -> oneSidedSound_<box>      (the consumption: oneSidedSound_of_composedData, verbatim
#        Fresh.FilterAssembly.OneSidedSound's conclusion shape).
# Strict boxes (11, dump v2 census section 7) additionally get D-variants at the
# strict-class dumpFam families (Fresh.DumpDomData) through family-general retargetings.
# Pairwise boxes (5) get pairwiseSound_<box> with the banked spineFamData datum discharged.
#
# Sources parsed (never invented): Fresh/ComposedFamData.lean (coveredSet 68 + compFamData
# names), Fresh/DumpDomData.lean (strictBoxes 11 + dumpFamData names), Fresh/SpineTotalData.lean
# (the 5 pairwise fam/spineFamData names + box tuples).
# NEW files only; nothing existing is modified.  Nothing committed.
import os, re, sys, argparse

HERE = os.path.dirname(os.path.abspath(__file__))
FRESH = os.path.abspath(os.path.join(HERE, '..', '..', '..', 'LonelyRunnerFresh', 'Fresh'))

def read(fn):
    return open(os.path.join(FRESH, fn)).read()

def finset_boxes(src, defname):
    """Parse the box tuples out of a `def <defname> : Finset (Fin 7 -> Z) := {...}` block."""
    m = re.search(r'def\s+' + defname + r'\b[^:]*:\s*Finset[^:]*:=\s*\{(.*?)\}\s*\n', src, re.S)
    if not m:
        raise SystemExit('could not locate def ' + defname)
    body = m.group(1)
    boxes = []
    for t in re.findall(r'!\[\s*([0-9,\s]+?)\]', body):
        vals = [int(x) for x in t.strip().split(',')]
        assert len(vals) == 7, vals
        boxes.append(tuple(vals))
    return boxes

def name_of(box):
    return '_'.join(str(v) for v in box)

def lit(box):
    return '(![' + ', '.join(str(v) for v in box) + '] : Fin 7 → ℤ)'

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--n', type=int, default=0, help='emit only the first K one-sided boxes (probe mode)')
    ap.add_argument('--skip', type=int, default=0, help='skip the first K one-sided boxes (batch mode: --skip S --n K emits boxes S..S+K)')
    ap.add_argument('--out', default=os.path.abspath(os.path.join(FRESH, 'TotalityLifts.lean')))
    ap.add_argument('--mirror', action='store_true',
                    help='emit the bridge-mirror body: one-sided sections only, opens '
                         'restricted to the namespaces the mirror carries, no D/pairwise')
    args = ap.parse_args()

    src_comp = read('ComposedFamData.lean')
    src_dump = read('DumpDomData.lean')
    src_st = read('SpineTotalData.lean')

    covered = finset_boxes(src_comp, 'coveredSet')
    assert len(covered) == 68, len(covered)
    assert len(set(covered)) == 68

    strict = finset_boxes(src_dump, 'strictBoxes')
    assert len(strict) == 11, len(strict)
    for b in strict:
        assert b in covered, b

    # the 5 pairwise: parse spineFamData theorem names + their box literals + fam names
    pairwise = []  # (box, famname, theoremname)
    seen_fam = set()
    for m in re.finditer(r'theorem\s+(spineFamData_\S+)\s*:\s*\n?\s*InRange17\s*\(!\[([0-9,\s]+?)\]',
                         src_st):
        tname = m.group(1)
        vals = tuple(int(x) for x in m.group(2).strip().split(','))
        assert len(vals) == 7
        # the matching fam name appears in the same theorem block (JoinFam ... fam<id> :=)
        blk = src_st[m.start():m.start() + 800]
        fm = re.search(r'JoinFam\s*\(\s*!\[[^\]]*\]\s*:\s*Fin 7 → ℤ\s*\)\s*(fam\S+?)\s*:=', blk)
        assert fm, tname
        fam = fm.group(1)
        # sanity: the fam def exists
        assert re.search(r'def\s+' + fam + r'\s*:\s*Finset JoinEdge', src_st), fam
        assert fam not in seen_fam
        pairwise.append((vals, fam, tname))
        seen_fam.add(fam)
    assert len(pairwise) == 5, pairwise

    # compFamData / dumpFamData names exist for every box we will instantiate
    for b in covered:
        assert re.search(r'theorem\s+compFamData_' + re.escape(name_of(b)) + r'\b', src_comp), b
    for b in strict:
        assert re.search(r'theorem\s+dumpFamData_' + re.escape(name_of(b)) + r'\b', src_dump), b

    # ordering: the 11 strict boxes first (dump v2 richest), then the remaining 57
    strict_set = set(strict)
    one_sided = strict + [b for b in covered if b not in strict_set]
    if args.skip:
        one_sided = one_sided[args.skip:]
    if args.n:
        one_sided = one_sided[:args.n]
    strict_here = [b for b in one_sided if b in strict_set]
    assert strict_here == strict or args.skip or args.n, 'strict boxes must lead'

    M = args.mirror
    L = []
    w = L.append

    # ---------------- header (imports first -- Lean 4 requires imports before any
    # command, including the module docstring) ----------------
    if not M:
        w('import Fresh.WordCoverSide')
        w('import Fresh.SpineSound')
        w('import Fresh.SpineTotalData')
        w('import Fresh.DumpDomData')
        w('')
        w('/-!')
        w('# TotalityLifts: the mechanical per-box totality lift instantiations — 68 one-sided + 5 pairwise')
        w('')
        w('Written 2026-11-15.  New file; nothing existing is edited.  This file instantiates, box by box,')
        w('the per-box totality lifts that feed the assembly chain')
        w('')
        w('  `ComposedFamData → ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`')
        w('')
        w('mirroring the `spineFamData` pattern of `Fresh.SpineTotalData` (per-box banked datum +')
        w('per-box consumption theorem).  NO new mathematics: every per-box theorem is a one-line')
        w('application of a banked lemma; the box-specific content is (i) the `coveredSet` membership')
        w('(the 68-deep insert walk), (ii) the `compFamOf` dispatch, (iii) the wiring.')
        w('')
        w('Per one-sided box `b` (all 68 of `Fresh.OneSidedComposed.coveredSet`), five theorems:')
        w('')
        w('* `covered_<box>` — membership, so the banked data `oneSidedTotalData b hb` is available;');
        w('* `spineFamDataOS_<box>` — the `spineFamData` mirror: `InRange17 b ∧ ComposedFamData')
        w('  (compFamOf b)`, the two data-side engine hypotheses DISCHARGED (no hypotheses);');
        w('* `composedConflict_<box>` — the word-cover KILL at the box: the banked `ComposedFamData`')
        w('  record consumed through the composed-cap engine (`wordCover_demands` →')
        w('  `composedFamRefutes` → `composedCap_conflict`) — realized word + realized chains +')
        w('  family exhaustiveness ⟹ False;');
        w('* `totalLift_<box>` — THE TOTALITY INSTANCE: `ComposedTotalOneSided b (compFamOf b)`,');
        w('  from the two named data-side OWEDs (`NoClearPointWordRealized` — box-independent, and')
        w('  `FamilyCoversWordEdges b (compFamOf b)` — the per-box exhaustiveness datum);');
        w('* `oneSidedSound_<box>` — THE CONSUMPTION: the totality instance through THE GLUE')
        w('  (`oneSidedSound_of_composedData`) to `Fresh.FilterAssembly.OneSidedSound`\'s exact')
        w('  conclusion shape (a `W₁` clear point over the faces).')
        w('')
        w('The 11 STRICT boxes (every death row strict-complete in `joinedge2_perbox_v1.jsonl`,')
        w('census section 7; the dump v2 data is richest there) additionally get the D-variants')
        w('`composedConflictD_/totalLiftD_/oneSidedSoundD_<box>` at the strict-class `dumpFam_<box>`')
        w('families of `Fresh.DumpDomData`, through this file\'s family-general retargetings')
        w('(`composedConflict_fam`, `composedTotal_of_wordCover_fam`, `oneSidedSound_of_total_fam`)')
        w('— the same lifts at the dump v2 families, consuming `dumpFamData_<box>`.')
        w('')
        w('The 5 pairwise (two-sided) boxes get `pairwiseSound_<box>`: the banked `spineFamData_<id>`')
        w('datum (`InRange17` + `JoinFam` of the artifact `c-raw` family, `Fresh.SpineTotalData`) is')
        w('DISCHARGED — no longer a hypothesis — and `Fresh.FilterAssembly.PairwiseSound`\'s exact')
        w('conclusion shape reduces to the pairwise totality OWED `SpineTotalPairwise` (`Fresh.SpineSound`).')
        w('')
        w('Totals: `totalLifts_of_exhaustiveness` (all 68 lifts from the two OWEDs),')
        w('`oneSidedSounds_of_totals` (all 68 consumptions), `oneSidedSound_of_exhaustiveness`')
        w('(the full chain in one theorem), `pairwiseSound_of_total` (the pairwise shape).')
        w('')
        w('OWED (named, data-side, honestly carried as HYPOTHESES, per the banked files\' accounting):')
        w('* `Fresh.WordCoverSide.NoClearPointWordRealized` — the `W₁`-word covering direction (the')
        w('  finite closed-interval covering argument; direction (b)\'s word side), box-independent.')
        w('  NOTE: `Fin 7` contains `0`, so the probe proposition `∀ i : Fin 7, 1 ≤ i.val` is FALSE —')
        w('  the assembly\'s `InRange17` is about the box tuple\'s values, not the index.')
        w('* `FamilyCoversWordEdges b (compFamOf b)` — the per-box family exhaustiveness (the dump\'s')
        w('  word-edge totality).  Honest residual: the banked `compFam_<box>` families carry the TOP')
        w('  records by death count (4, or 8 on the three census-fully-covered boxes), not the full')
        w('  dump families (e.g. 551 chain-side family edges for box (1,2,3,4,4,5,7)); the')
        w('  exhaustiveness OWED at the banked families is therefore a SHARPENING target (a full-dump')
        w('  family instantiation), not a consequence of the banked data.  The D-variants carry the')
        w('  same OWED at the strict-class `dumpFam` families (same top-record shape).')
        w('* The verbatim `Fresh.FilterAssembly.OneSidedSound` HYPOTHESIS shape additionally needs the')
        w('  per-box `JoinFam` conversion of the composed records (the `8m±1` numerator bookkeeping) —')
        w('  the named residual of `Fresh.OneSidedGlue`; the consumptions here are in the glue\'s')
        w('  W₀-chain-conditional shape (`capChainsRealized`), with the conclusion shape verbatim.')
        w('')
        w('No-go context (proved in `Fresh.SpineTotalData`): the totality is NOT interval-reducible')
        w('(`capDerivedDemand_unsat`, `intervalForcedDemand_capUnsat`, `intervalForcedPair_invalid`),')
        w('which is exactly why the lifts enter through the W₀-conditional bridge and the word-cover')
        w('side, not through `FaceLo`/`FaceHi` forcing.')
        w('')
        w('All arithmetic is exact (`decide`/banked `norm_num`; floats nowhere).  Every theorem carries')
        w('`#print axioms`; the accepted profile is the standard three (propext, Classical.choice,')
        w('Quot.sound) — `sorryAx` is failure.')
        w('-/')
        w('')
        w('namespace Fresh.TotalityLifts')
        w('')
        w('open Fresh.FilterAssembly Fresh.SpineSound Fresh.SpineTotalData Fresh.JoinFamComposed')
        w('  Fresh.OneSidedComposed Fresh.OneSidedGlue Fresh.WordCoverSide Fresh.DumpDomData')
        w('  Fresh.FrontierFamilyCap')
    else:
        w('/-!')
        w('## BRIDGE MIRROR BODY (artifact: totlift_bridge_mirror_v1.lean, built by totlift_mirror_v1.py)')
        w('')
        w('The one-sided sections of Fresh/TotalityLifts.lean VERBATIM (this text is emitted by the')
        w('same generator, totlift_gen_v1.py --mirror), pasted into the mirror after the verbatim')
        w('Fresh bodies (Framework-min, FilterAssembly-min, FrontierFamilyCap-min, SpineSound-min,')
        w('JoinFamComposed, OneSidedGlue, WordCoverSide, ComposedFamData full).  The D-variants and')
        w('the 5 pairwise instances are NOT in the mirror (they need Fresh.DumpDomData /')
        w('Fresh.SpineTotalData bodies; they add no new wiring and are ./check.sh-verified).')
        w('-/')
        w('')
        w('namespace Fresh.TotalityLifts')
        w('')
        w('open Fresh.FilterAssembly Fresh.SpineSound Fresh.JoinFamComposed Fresh.OneSidedComposed')
        w('  Fresh.OneSidedGlue Fresh.WordCoverSide Fresh.FrontierFamilyCap')

    # ---------------- section 1: family-general retargetings ----------------
    w('')
    w('/-! ## 1. Family-general retargetings (the banked lemmas are fixed at the `compFamOf`')
    w('dispatch; the strict-class `dumpFam` lifts consume these general forms) -/')
    w('')
    w('/-- **Family-general word-cover kill** (`Fresh.WordCoverSide.wordCover_demands` at an')
    w('arbitrary family `f` with its exhaustiveness datum `FamilyCoversWordEdges b f`). -/')
    w('theorem composedConflict_fam {b : Fin 7 → ℤ} {f : ComposedFam} (hdata : ComposedFamData f)')
    w('    (hexh : FamilyCoversWordEdges b f)')
    w('    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}')
    w('    (hface : ∀ i, FaceLo b i ≤ g i ∧ g i ≤ FaceHi b i)')
    w('    (hchains : capChainsRealized g f)')
    w('    (hw : WordRealized g w) : False :=')
    w('  wordCover_demands hdata hchains hw (hexh g w hface hw)')
    w('')
    w('#print axioms composedConflict_fam')
    w('')
    w('/-- **Family-general totality lift** (`Fresh.WordCoverSide.composedTotal_of_wordCover` is')
    w('fixed at the `compFamOf` dispatch; the same derivation at an arbitrary family — the')
    w('two data-side OWEDs reduce to `ComposedTotalOneSided b f`). -/')
    w('theorem composedTotal_of_wordCover_fam {b : Fin 7 → ℤ} {f : ComposedFam}')
    w('    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)')
    w('    (hexh : FamilyCoversWordEdges b f) :')
    w('    ComposedTotalOneSided b f := by')
    w('  intro g hface hchains hcarve hnoc')
    w('  obtain ⟨w, hw⟩ := hword g hnoc')
    w('  obtain ⟨e, he, hxpos, hypos, hdem, _⟩ :=')
    w('    wordCover_realizes hchains hw (hexh g w hface hw)')
    w('  exact ⟨e, he, hxpos, hypos, hdem⟩')
    w('')
    w('#print axioms composedTotal_of_wordCover_fam')
    w('')
    w('/-- **Family-general consumption** (`Fresh.OneSidedGlue.oneSidedSound_of_composedData` is')
    w('fixed at the `compFamOf` dispatch and the `coveredSet` membership; the same glue at an')
    w('arbitrary family with its `ComposedFamData` datum). -/')
    w('theorem oneSidedSound_of_total_fam {b : Fin 7 → ℤ} {f : ComposedFam}')
    w('    (hdata : ComposedFamData f) (htotal : ComposedTotalOneSided b f)')
    w('    (g : Fin 7 → ℝ) (hface : ∀ i, FaceLo b i ≤ g i ∧ g i ≤ FaceHi b i)')
    w('    (hchains : capChainsRealized g f)')
    w('    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :')
    w('    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) := by')
    w('  by_contra hnoc')
    w('  obtain ⟨e, he, hxpos, hypos, hdem⟩ := htotal g hface hchains hcarve hnoc')
    w('  exact composedEdge_kill hdata hchains he hxpos hypos hdem')
    w('')
    w('#print axioms oneSidedSound_of_total_fam')
    w('')

    # ---------------- section 2: the 68 one-sided boxes ----------------
    w('')
    w('/-! ## 2. The 68 one-sided boxes: per-box data + word-cover kill + totality lift + consumption')
    w('')
    w('Order: the 11 strict-complete boxes first (dump v2 census section 7, the richest data),')
    w('then the remaining 57 in `coveredSet` order. -/')

    # the singleton closer: for the real file the LAST coveredSet box (its walk's terminal
    # goal is the Finset singleton); for --mirror batches, the LAST EMITTED box (the
    # batch-local coveredSet ends there)
    last_box = covered[-1] if not M else one_sided[-1]
    for idx, b in enumerate(one_sided):
        N = name_of(b)
        V = lit(b)
        is_strict = b in strict_set
        is_last = (b == last_box)
        w('')
        if is_strict:
            w('/-! ### Box (' + ', '.join(str(v) for v in b) + ') — strict-complete (joinedge2 census §7) -/')
        else:
            w('/-! ### Box (' + ', '.join(str(v) for v in b) + ') -/')
        w('')
        w('/-- coveredSet membership: box (' + ', '.join(str(v) for v in b) + ') carries the banked family')
        w('`compFam_' + N + '` of `Fresh.ComposedFamData` ([T 68/68]). -/')
        w('theorem covered_' + N + ' :')
        w('    ' + V + ' ∈ coveredSet := by')
        w('  rw [coveredSet]')
        w('  repeat\' first')
        w('    | apply Finset.mem_insert_self')
        w('    | apply Finset.mem_insert_of_mem')
        if is_last:
            # the LAST element of the Finset literal: the walk's terminal goal is the
            # singleton `x \u2208 {x}` (elaborated through the Singleton instance, not
            # reducibly an insert), closed by mem_singleton
            w('  exact Finset.mem_singleton.mpr rfl')
        w('')
        w('#print axioms covered_' + N)
        w('')
        w('/-- **The per-box data datum (the `spineFamData` mirror), box (' + ', '.join(str(v) for v in b) + ')**: `InRange17`')
        w('and the banked `ComposedFamData` record at the `compFamOf` dispatch — the two data-side')
        w('engine hypotheses, DISCHARGED (no hypotheses; cf. `Fresh.SpineTotalData.spineFamData_*`). -/')
        w('theorem spineFamDataOS_' + N + ' :')
        w('    InRange17 ' + V + ' ∧')
        w('      ComposedFamData (compFamOf ' + V + ') :=')
        w('  ⟨by decide, oneSidedTotalData _ covered_' + N + '⟩')
        w('')
        w('#print axioms spineFamDataOS_' + N)
        w('')
        w('/-- **The per-box composed conflict (the word-cover kill), box (' + ', '.join(str(v) for v in b) + ')**: the banked')
        w('datum `oneSidedTotalData` (the record `compFamData_' + N + '`) consumed through the')
        w('composed-cap engine (`wordCover_demands` → `composedFamRefutes` → `composedCap_conflict`):')
        w('a realized `W₁` word + the realized chains (the W₀-conditional bridge) + the')
        w('family-exhaustiveness OWED ⟹ False. -/')
        w('theorem composedConflict_' + N)
        w('    (hexh : FamilyCoversWordEdges ' + V)
        w('      (compFamOf ' + V + '))')
        w('    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}')
        w('    (hface : ∀ i, FaceLo ' + V + ' i ≤ g i ∧')
        w('      g i ≤ FaceHi ' + V + ' i)')
        w('    (hchains : capChainsRealized g (compFamOf ' + V + '))')
        w('    (hw : WordRealized g w) : False :=')
        w('  composedConflict_fam (oneSidedTotalData _ covered_' + N + ') hexh hface hchains hw')
        w('')
        w('#print axioms composedConflict_' + N)
        w('')
        w('/-- **The per-box totality lift, box (' + ', '.join(str(v) for v in b) + ')**: `ComposedTotalOneSided` at the box\'s')
        w('banked family — the two data-side OWEDs (`NoClearPointWordRealized`,')
        w('`FamilyCoversWordEdges`) reduce to the totality instance.  Chain: `ComposedFamData →')
        w('ComposedTotalOneSided → oneSidedSound_of_composedData → OneSidedSound`. -/')
        w('theorem totalLift_' + N)
        w('    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)')
        w('    (hexh : FamilyCoversWordEdges ' + V)
        w('      (compFamOf ' + V + ')) :')
        w('    ComposedTotalOneSided ' + V)
        w('      (compFamOf ' + V + ') :=')
        w('  composedTotal_of_wordCover _ covered_' + N + ' hword hexh')
        w('')
        w('#print axioms totalLift_' + N)
        w('')
        w('/-- **The per-box consumption, box (' + ', '.join(str(v) for v in b) + ')**: the totality instance through THE GLUE')
        w('(`oneSidedSound_of_composedData`) — `Fresh.FilterAssembly.OneSidedSound`\'s exact')
        w('conclusion shape: an arrangement in the box whose chains are realized (the')
        w('W₀-conditional) and which carves `[1,7]` admits a `W₁` clear point over its faces. -/')
        w('theorem oneSidedSound_' + N)
        w('    (htotal : ComposedTotalOneSided ' + V)
        w('      (compFamOf ' + V + '))')
        w('    (g : Fin 7 → ℝ)')
        w('    (hface : ∀ i, FaceLo ' + V + ' i ≤ g i ∧')
        w('      g i ≤ FaceHi ' + V + ' i)')
        w('    (hchains : capChainsRealized g (compFamOf ' + V + '))')
        w('    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :')
        w('    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=')
        w('  oneSidedSound_of_composedData _ covered_' + N + ' htotal g hface hchains hcarve')
        w('')
        w('#print axioms oneSidedSound_' + N)
        if is_strict and not M:
            w('')
            w('/-- **The strict-class conflict, box (' + ', '.join(str(v) for v in b) + ')**: the word-cover kill at the strict-class')
            w('family `dumpFam_' + N + '` (`Fresh.DumpDomData`; every death row of the box is')
            w('strict-complete in `joinedge2_perbox_v1.jsonl`), consuming the banked')
            w('`dumpFamData_' + N + '` datum. -/')
            w('theorem composedConflictD_' + N)
            w('    (hexh : FamilyCoversWordEdges ' + V + ' dumpFam_' + N + ')')
            w('    {g : Fin 7 → ℝ} {w : List (Fin 7 × ℕ)}')
            w('    (hface : ∀ i, FaceLo ' + V + ' i ≤ g i ∧')
            w('      g i ≤ FaceHi ' + V + ' i)')
            w('    (hchains : capChainsRealized g dumpFam_' + N + ')')
            w('    (hw : WordRealized g w) : False :=')
            w('  composedConflict_fam dumpFamData_' + N + ' hexh hface hchains hw')
            w('')
            w('#print axioms composedConflictD_' + N)
            w('')
            w('/-- **The strict-class totality lift, box (' + ', '.join(str(v) for v in b) + ')**: `ComposedTotalOneSided` at the strict-class')
            w('family `dumpFam_' + N + '` — the same reduction at the dump v2 family, through the')
            w('family-general retargeting. -/')
            w('theorem totalLiftD_' + N)
            w('    (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)')
            w('    (hexh : FamilyCoversWordEdges ' + V + ' dumpFam_' + N + ') :')
            w('    ComposedTotalOneSided ' + V + ' dumpFam_' + N + ' :=')
            w('  composedTotal_of_wordCover_fam hword hexh')
            w('')
            w('#print axioms totalLiftD_' + N)
            w('')
            w('/-- **The strict-class consumption, box (' + ', '.join(str(v) for v in b) + ')**: the strict-class totality instance through')
            w('the family-general glue — the same conclusion shape at the dump v2 family. -/')
            w('theorem oneSidedSoundD_' + N)
            w('    (htotal : ComposedTotalOneSided ' + V + ' dumpFam_' + N + ')')
            w('    (g : Fin 7 → ℝ)')
            w('    (hface : ∀ i, FaceLo ' + V + ' i ≤ g i ∧')
            w('      g i ≤ FaceHi ' + V + ' i)')
            w('    (hchains : capChainsRealized g dumpFam_' + N + ')')
            w('    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :')
            w('    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=')
            w('  oneSidedSound_of_total_fam dumpFamData_' + N + ' htotal g hface hchains hcarve')
            w('')
            w('#print axioms oneSidedSoundD_' + N)

    if M:
        # the four totals, at the batch's coveredSet (same statements as the real file)
        w('')
        w('/-! ## 4. The totals (at the batch coveredSet; the real file states them over the')
        w('full 68-element coveredSet -- same proofs, verbatim) -/')
        w('')
        w('theorem totalLifts_of_exhaustiveness (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)')
        w('    (hexh : ∀ b ∈ coveredSet, FamilyCoversWordEdges b (compFamOf b)) :')
        w('    ∀ b ∈ coveredSet, ComposedTotalOneSided b (compFamOf b) :=')
        w('  fun b hb => composedTotal_of_wordCover b hb hword (hexh b hb)')
        w('')
        w('#print axioms totalLifts_of_exhaustiveness')
        w('')
        w('theorem oneSidedSounds_of_totals')
        w('    (htotal : ∀ b ∈ coveredSet, ComposedTotalOneSided b (compFamOf b))')
        w('    (b : Fin 7 → ℤ) (hb : b ∈ coveredSet)')
        w('    (g : Fin 7 → ℝ) (hface : ∀ i, FaceLo b i ≤ g i ∧ g i ≤ FaceHi b i)')
        w('    (hchains : capChainsRealized g (compFamOf b))')
        w('    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :')
        w('    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=')
        w('  oneSidedSound_of_composedData b hb (htotal b hb) g hface hchains hcarve')
        w('')
        w('#print axioms oneSidedSounds_of_totals')
        w('')
        w('theorem oneSidedSound_of_exhaustiveness (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)')
        w('    (hexh : ∀ b ∈ coveredSet, FamilyCoversWordEdges b (compFamOf b))')
        w('    (b : Fin 7 → ℤ) (hb : b ∈ coveredSet)')
        w('    (g : Fin 7 → ℝ) (hface : ∀ i, FaceLo b i ≤ g i ∧ g i ≤ FaceHi b i)')
        w('    (hchains : capChainsRealized g (compFamOf b))')
        w('    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :')
        w('    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=')
        w('  oneSidedSounds_of_totals (totalLifts_of_exhaustiveness hword hexh) b hb g hface hchains')
        w('    hcarve')
        w('')
        w('#print axioms oneSidedSound_of_exhaustiveness')
        w('')
        w('end Fresh.TotalityLifts')
        out = '\n'.join(L) + '\n'
        sys.stdout.write(out)
        return

    # ---------------- section 3: the 5 pairwise boxes ----------------
    w('')
    w('/-! ## 3. The 5 pairwise (two-sided) boxes: the banked `spineFamData` datum discharged -/')
    w('')
    for b, fam, tname in pairwise:
        N = name_of(b)
        V = lit(b)
        w('')
        w('/-- **The per-box pairwise consumption, box (' + ', '.join(str(v) for v in b) + ')**: the banked `' + tname + '`')
        w('datum (`InRange17` + `JoinFam` of the artifact `c-raw` family `' + fam + '`,')
        w('`Fresh.SpineTotalData`) is DISCHARGED — no longer a hypothesis — and')
        w('`Fresh.FilterAssembly.PairwiseSound`\'s exact conclusion shape reduces to the pairwise')
        w('totality OWED `SpineTotalPairwise` (`Fresh.SpineSound`) at that family. -/')
        w('theorem pairwiseSound_' + N)
        w('    (htotal : SpineTotalPairwise ' + V + ' ' + fam + ')')
        w('    (g : Fin 7 → ℝ)')
        w('    (hface : ∀ i, FaceLo ' + V + ' i ≤ g i ∧')
        w('      g i ≤ FaceHi ' + V + ' i) :')
        w('    Fresh.Certs.NoCarve g ∨')
        w('      (∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8))) :=')
        w('  pairwiseSound_at _ _ ' + tname + '.1 ' + tname + '.2 htotal g hface')
        w('')
        w('#print axioms pairwiseSound_' + N)

    # ---------------- section 4: the totals ----------------
    w('')
    w('/-! ## 4. The totals -/')
    w('')
    w('/-- **THE TOTAL (the one-sided lift)**: for EVERY covered box, the two data-side OWEDs give')
    w('the composed totality — the per-box instances `totalLift_<box>` are this theorem\'s per-box')
    w('unfoldings (each of whose downstream kills consumed the banked `ComposedFamData` record')
    w('through the composed-cap engine). -/')
    w('theorem totalLifts_of_exhaustiveness (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)')
    w('    (hexh : ∀ b ∈ coveredSet, FamilyCoversWordEdges b (compFamOf b)) :')
    w('    ∀ b ∈ coveredSet, ComposedTotalOneSided b (compFamOf b) :=')
    w('  fun b hb => composedTotal_of_wordCover b hb hword (hexh b hb)')
    w('')
    w('#print axioms totalLifts_of_exhaustiveness')
    w('')
    w('/-- **THE TOTAL (the consumption)**: the per-box totality through the glue to')
    w('`Fresh.FilterAssembly.OneSidedSound`\'s conclusion shape, for every covered box. -/')
    w('theorem oneSidedSounds_of_totals')
    w('    (htotal : ∀ b ∈ coveredSet, ComposedTotalOneSided b (compFamOf b))')
    w('    (b : Fin 7 → ℤ) (hb : b ∈ coveredSet)')
    w('    (g : Fin 7 → ℝ) (hface : ∀ i, FaceLo b i ≤ g i ∧ g i ≤ FaceHi b i)')
    w('    (hchains : capChainsRealized g (compFamOf b))')
    w('    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :')
    w('    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=')
    w('  oneSidedSound_of_composedData b hb (htotal b hb) g hface hchains hcarve')
    w('')
    w('#print axioms oneSidedSounds_of_totals')
    w('')
    w('/-- **THE TOTAL (the full chain in one theorem)**: `ComposedFamData → ComposedTotalOneSided')
    w('→ oneSidedSound_of_composedData → OneSidedSound`, per covered box, with the two data-side')
    w('OWEDs the only hypotheses.  (Composes this file\'s two totals; equals the banked')
    w('`Fresh.WordCoverSide.oneSidedSound_of_wordCover` shape.) -/')
    w('theorem oneSidedSound_of_exhaustiveness (hword : ∀ g : Fin 7 → ℝ, NoClearPointWordRealized g)')
    w('    (hexh : ∀ b ∈ coveredSet, FamilyCoversWordEdges b (compFamOf b))')
    w('    (b : Fin 7 → ℤ) (hb : b ∈ coveredSet)')
    w('    (g : Fin 7 → ℝ) (hface : ∀ i, FaceLo b i ≤ g i ∧ g i ≤ FaceHi b i)')
    w('    (hchains : capChainsRealized g (compFamOf b))')
    w('    (hcarve : CarvesOneSeven (Finset.image g Finset.univ)) :')
    w('    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8)) :=')
    w('  oneSidedSounds_of_totals (totalLifts_of_exhaustiveness hword hexh) b hb g hface hchains')
    w('    hcarve')
    w('')
    w('#print axioms oneSidedSound_of_exhaustiveness')
    w('')
    w('/-- **THE TOTAL (pairwise)**: the pairwise consumption shape at general box/family — the')
    w('five per-box instances `pairwiseSound_<box>` instantiate it with the banked data')
    w('discharged. -/')
    w('theorem pairwiseSound_of_total (n : Fin 7 → ℤ) (fam : Finset JoinEdge)')
    w('    (hrange : InRange17 n) (hfam : JoinFam n fam) (htotal : SpineTotalPairwise n fam)')
    w('    (g : Fin 7 → ℝ) (hface : ∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i) :')
    w('    Fresh.Certs.NoCarve g ∨')
    w('      (∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ distInt (g i * (s / 8))) :=')
    w('  pairwiseSound_at n fam hrange hfam htotal g hface')
    w('')
    w('#print axioms pairwiseSound_of_total')
    w('')
    w('end Fresh.TotalityLifts')
    out = '\n'.join(L) + '\n'
    open(args.out, 'w').write(out)
    n_one = len(one_sided)
    n_strict = len([b for b in one_sided if b in strict_set])
    print('wrote %s' % args.out)
    print('one-sided boxes: %d (strict %d lead), pairwise: %d' % (n_one, n_strict, len(pairwise)))
    print('theorems: %d one-sided base + %d strict-D + %d pairwise + 3 retarget + 4 totals'
          % (5 * n_one, 3 * n_strict, len(pairwise)))

if __name__ == '__main__':
    main()
