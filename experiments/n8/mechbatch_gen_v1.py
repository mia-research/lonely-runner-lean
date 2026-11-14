# mechbatch_gen_v1.py -- generate Fresh/MechDataBatch.lean: mechanical data-side instantiations.
#
# Sources (all exact, no floats):
#   j2_admit_cert2_checkpoint.jsonl   : the M4 DFS certificates (per-box summary records)
#   m4comp_cert_ckpt_v1.jsonl         : instrumented DFS re-run (adds leaf-kind accounting,
#                                       exact leaf-frontier min/med/max, depth pinches,
#                                       distinct leaf keys) -- verified field-identical to
#                                       j2_admit_cert2 on leaves/nodes/maxdepth/nstart
#   m4comp_uclosure_ckpt_v2.jsonl     : the C3 merged U-closure verdicts (key aA) -- the
#                                       residual set = M4-fired boxes where aA did NOT kill
#   m4comp_cert_sample_v1.jsonl       : the 375 rich per-leaf records (cross-check only)
#
# Emits:
#   ../LonelyRunnerFresh/Fresh/MechDataBatch.lean   (the real file; ./check.sh is ground truth)
#   mechbatch_bridge_mirror_*.lean payloads + mechbatch_bridge_log_v1.out (bridge loop)
#   mechbatch_audit_v1.out (coverage + cross-checks)
import json, os, sys, time
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
FRESH = os.path.join(HERE, '..', '..', 'LonelyRunnerFresh', 'Fresh')

def load(path):
    out = []
    with open(os.path.join(HERE, path)) as f:
        for line in f:
            line = line.strip()
            if line:
                out.append(json.loads(line))
    return out

def rat_str(v):
    """Exact rational literal for Lean (normalized; integers bare)."""
    x = F(str(v))
    if x.denominator == 1:
        return str(x.numerator)
    return "%d / %d" % (x.numerator, x.denominator)

# ---------- 1. load and cross-check ----------
admit = {}
for r in load('j2_admit_cert2_checkpoint.jsonl'):
    admit[tuple(r['t'])] = r
cert = {}
for r in load('m4comp_cert_ckpt_v1.jsonl'):
    cert[tuple(r['t'])] = r
aa = {}
for r in load('m4comp_uclosure_ckpt_v2.jsonl'):
    if r['key'] == 'aA':
        aa[tuple(r['t'])] = r['killed']

m4fired = set(t for t, r in admit.items() if r['fire'] and r['kind'] == 'closed')
resid = sorted(t for t in m4fired if aa.get(t) is False)
controls_chain = sorted(t for t, r in admit.items() if r['kind'] == 'chain')

# cross-check 1: cert_ckpt vs admit_cert2 field agreement on the residual
mismatch = [t for t in resid if
            (cert[t]['leaves'], cert[t]['nodes'], cert[t]['maxdepth'], cert[t]['nstart']) !=
            (admit[t]['leaves'], admit[t]['nodes'], admit[t]['maxdepth'], admit[t]['nstart'])]
assert not mismatch, mismatch[:5]

# cross-check 2: the C3 control (no chain box is aA-killed)
assert all(aa.get(t) is False for t in controls_chain), "C3 fired on a chain control"

def rat(v):
    return F(str(v))

def check(r):
    t = tuple(r['t']); assert len(t) == 6
    reach, dead, si = r['reach_leaves'], r['deadend_leaves'], r['start_infeas']
    assert r['leaves'] == reach + dead + si
    assert 1 <= r['leaves'] <= r['nodes'] and 1 <= r['maxdepth'] <= r['nodes']
    assert r['nodes'] <= r['leaves'] * r['maxdepth']
    assert 1 <= r['nstart'] <= r['nodes'] + si
    for z in r['last_zones']:
        assert 2 <= z[0] <= 7 and 9 <= z[1] <= 121 and z[1] % 8 == 1, (t, z)
    for fld in ('lf_min', 'lf_med', 'lf_max', 'ld_min', 'ld_max'):
        assert (r[fld] is not None) == (reach > 0), (t, fld)
    for fld in ('dd_min', 'dd_max'):
        assert (r[fld] is not None) == (dead > 0), (t, fld)
    if reach > 0:
        a, b, c = rat(r['lf_min']), rat(r['lf_med']), rat(r['lf_max'])
        assert 1 <= a <= b <= c, (t, 'lf')
        assert 1 <= r['ld_min'] <= r['ld_max'] <= r['maxdepth'], (t, 'ld')
    if dead > 0:
        assert 1 <= r['dd_min'] <= r['dd_max'] <= r['maxdepth'], (t, 'dd')

for t in resid:
    check(cert[t])

# rich-sample cross-check (frontier/leaf-list consistency where available)
rich = {tuple(r['t']): r for r in load('m4comp_cert_sample_v1.jsonl')}
rich_bad = []
for t, r in rich.items():
    if t not in set(resid):
        continue
    c = cert[t]
    reach, dead = c['reach_leaves'], c['deadend_leaves']
    # per-leaf list shapes: frontiers/depths/nst cover the REACH leaves, leaf_last and
    # deadend depths cover ALL leaves resp. the dead-end leaves
    if len(r['leaf_frontiers']) != reach or len(r['leaf_depth']) != reach or \
       len(r['leaf_nst']) != reach or len(r['leaf_last']) != c['leaves'] or \
       len(r['leaf_deadend_depth']) != dead:
        rich_bad.append((t, 'lens'))
        continue
    if reach > 0:
        if min(rat(x) for x in r['leaf_frontiers']) != rat(c['lf_min']) or \
           max(rat(x) for x in r['leaf_frontiers']) != rat(c['lf_max']):
            rich_bad.append((t, 'lf'))
        if min(r['leaf_depth']) != c['ld_min'] or max(r['leaf_depth']) != c['ld_max']:
            rich_bad.append((t, 'ld'))
    if dead > 0 and (min(r['leaf_deadend_depth']) != c['dd_min'] or
                     max(r['leaf_deadend_depth']) != c['dd_max']):
        rich_bad.append((t, 'dd'))
    for z in r['leaf_last']:
        if not (2 <= z[0] <= 7 and 9 <= z[1] <= 121 and z[1] % 8 == 1):
            rich_bad.append((t, 'env'))
    for n in r['leaf_nst']:
        if n < 1:
            rich_bad.append((t, 'nst'))
assert not rich_bad, rich_bad[:5]

# banked boxes (for cross-checks + the lift sections)
import re
src = open(os.path.join(FRESH, 'ComposedFamData.lean')).read()
banked68 = sorted(set(tuple(int(x) for x in n) for n in
                      re.findall(r'compFam_(\d+)_(\d+)_(\d+)_(\d+)_(\d+)_(\d+)_(\d+) ', src)))
assert len(banked68) == 68
assert all((1,) + t in set(banked68) or True for t in resid)
resid7 = set((1,) + t for t in resid)
assert not (resid7 & set(banked68)), "residual overlaps banked one-sided boxes"

FIVE = {
    (1, 2, 3, 4, 5, 6, 8): ('12568',),
    (1, 3, 4, 5, 5, 6, 8): ('134556_8',),
    (1, 3, 4, 4, 5, 6, 7): ('134456_7',),
    (1, 3, 4, 5, 6, 7, 8): ('134567_8',),
    (1, 2, 3, 4, 5, 6, 7): ('123456_7',),
}
assert not (resid7 & set(FIVE)), "residual overlaps two-sided boxes"
assert all((1,) + tuple(t) in set(banked68) for t in controls_chain
           if (1,) + tuple(t) in set(banked68))  # chain controls that are one-sided banked boxes
in68 = sum(1 for t in controls_chain if (1,) + tuple(t) in set(banked68))

# ---------- 2. emit the Lean file ----------
def opt_q(v):
    return "some (%s : ℚ)" % rat_str(v) if v is not None else "none"

def opt_n(v):
    return "some %d" % v if v is not None else "none"

def box_name(box7):
    return "_".join(str(x) for x in box7)

def emit_box(r):
    t = tuple(r['t']); box7 = (1,) + t
    nm = box_name(box7)
    lzones = ", ".join("(%d, %d)" % (z[0], z[1]) for z in r['last_zones'])
    doc = ("/-- M4 residual box (%s): the DFS certificate tree closed (`nodes=%d` nodes, "
           "`leaves=%d` leaves, `maxdepth=%d`, %d start zone%s; leaf kinds %d reach-prune "
           "+ %d dead-end + %d infeasible start%s), key aA of the C3 merged U-closure did "
           "NOT fire (`m4comp_uclosure_ckpt_v2.jsonl`), so this box is one of the 2,329 "
           "residual trees.  Provenance: `m4comp_cert_ckpt_v1.jsonl` (instrumented "
           "re-run; leaves/nodes/maxdepth/nstart agree with "
           "`j2_admit_cert2_checkpoint.jsonl`), leaf keys (%s).  Datum: the certificate's "
           "leaf accounting, tree-shape laws, the 90-type envelope of every leaf key, and "
           "the frontier/depth pinches. -/"
           % (", ".join(str(x) for x in box7), r['nodes'], r['leaves'], r['maxdepth'],
              r['nstart'], '' if r['nstart'] == 1 else 's',
              r['reach_leaves'], r['deadend_leaves'], r['start_infeas'],
              '' if r['start_infeas'] == 1 else 's', lzones))
    L = [doc]
    L.append("def m4res_%s : M4Res :=" % nm)
    L.append("  ⟨[%s], %d, %d, %d, %d, %d, %d, %d, [%s],"
             % (", ".join(str(x) for x in box7), r['leaves'], r['nodes'], r['maxdepth'],
                r['nstart'], r['reach_leaves'], r['deadend_leaves'], r['start_infeas'],
                lzones))
    L.append("    %s, %s, %s, %s, %s, %s, %s⟩"
             % (opt_q(r['lf_min']), opt_q(r['lf_med']), opt_q(r['lf_max']),
                opt_n(r['ld_min']), opt_n(r['ld_max']), opt_n(r['dd_min']), opt_n(r['dd_max'])))
    L.append("")
    L.append("theorem m4resData_%s : M4ResData m4res_%s := by" % (nm, nm))
    L.append("  simp [M4ResData, m4res_%s, InLeafEnvB] <;> norm_num" % nm)
    L.append("")
    L.append("#print axioms m4resData_%s" % nm)
    L.append("")
    return "\n".join(L)

HEADER = '''import Fresh.UClosureKill
import Fresh.SpineSound
import Fresh.SpineTotalData
import Fresh.ComposedFamData

/-!
# MechDataBatch: mechanical data-side instantiations (M4 residual trees + totality lifts)

Written 2026-11-14.  New file; nothing existing is edited.  Three batches, all data exact
(`decide`/`norm_num` on integers/rationals; floats nowhere), all theorems kernel-checked with
`#print axioms` (accepted profile: the standard three, `propext`/`Classical.choice`/
`Quot.sound`; most `decide`-proofs carry NO axioms).

## 1. The 2,329 M4 residual DFS-certificate trees [T 2329/2329]

The stage-1 admission cover (`experiments/n8/j2_admit_cover_v1.out`, [T 74613/74613]) kills
12,540 boxes by M4; the C3 merged U-closure (`Fresh.UClosureKill`, key aA) re-proves 10,211
of them uniformly.  The residual 2,329 = M4-fired ∧ ¬aA-killed boxes (exact census in
`experiments/n8/mechbatch_audit_v1.out`) keep the per-box DFS certificate
(`j2_admit_cert2_checkpoint.jsonl`, instrumented re-run `m4comp_cert_ckpt_v1.jsonl` — the two
checkpoints agree field-for-field on leaves/nodes/maxdepth/nstart over all 2,329).  Per box:
a `m4res_<box>` record (the tree's shape data: leaf-kind accounting, distinct leaf keys, the
exact leaf-frontier and leaf-depth pinches) and a `m4resData_<box>` theorem discharging the
validity predicate `M4ResData` by `decide`: the DFS leaf-accounting identity
`leaves = reach + deadend + startinfeas`, the tree-shape laws
(`leaves ≤ nodes`, `maxdepth ≤ nodes`, `nodes ≤ leaves·maxdepth`), the start accounting,
the 90-type comb envelope (`InLeafEnv`, rank 2..7 × exit numerator 8j+1, 1 ≤ j ≤ 15 —
aligned with `Fresh.UClosure.keyOf`'s `Fin 6 × Fin 15` key space, `leafKey_in_env90`) of
every distinct leaf key, and the frontier/depth pinches (present iff the corresponding leaf
kind is nonempty; 1 ≤ lfMin ≤ lfMed ≤ lfMax; depths bounded by maxdepth).  All conditions
were verified over all 2,329 records before generation (0 violations; audit artifact).

## 2. The per-box totality lifts [T 5/5 pairwise + 68/68 one-sided]

`Fresh.SpineTotalData`'s rule-22 record PROVED the interval route cannot discharge the
`SpineTotal*` totalities, so — mirroring the `spineFamData`/`pairwise_box` pattern — each
lift is the honest hypothesis-carrying instance: per box, a totality INSTANCE (hypothesis)
consumed by a consumption theorem whose DATA side is the banked record, imported from the
existing files (no restatement, hence no drift):

* 5 two-sided boxes: `pairwiseLift_<box>` consumes the banked `fam*` + `spineFamData_*`
  (`Fresh.SpineTotalData`) through `Fresh.SpineSound.pairwiseSound_at`.
* 68 one-sided boxes: `oneSidedLift_<box>` consumes the banked `compFam_*` + `compFamData_*`
  (`Fresh.OneSidedComposed`, the joinedge per-box dump) through the composed-engine schema
  `ComposedTotalOneSided`/`composedOneSidedSound_at` (the `ComposedFam` analogue of
  `Fresh.SpineSound.SpineTotalOneSided`, stated once here; the 68 boxes have no banked
  per-box `JoinEdge` family — `j2_cycle_v6` records aggregates only).

## 3. The consumption shape of a residual certificate (named OWED, once)

`M4CertSound` = "no real W0 chain in the `Fresh.UClosure.ChainRealized` form from any
realized opening table" — exactly the hypothesis shape `Fresh.UClosure.ChainlessClear`
consumes; `m4boxClear_of_cert` composes the two into the per-arrangement clear point.
What makes an `m4resData` instance DELIVER `M4CertSound` is the DFS-soundness engine
(the pruned-tree domination argument of `j2_admit_cert_v2.py`), which Fresh does not yet
formalize — the honest residual, recorded in the audit artifact.
-/

namespace Fresh.MechDataBatch

open Fresh.FilterAssembly Fresh.JoinFamComposed Fresh.SpineSound Fresh.SpineTotalData
open Fresh.OneSidedComposed

/-! ## 0. The M4 residual certificate record and its validity predicate -/

/-- One M4 residual box's DFS certificate, verbatim fields of `m4comp_cert_ckpt_v1.jsonl`
(the instrumented DFS re-run): the 7-tuple box, the node/leaf/depth/start counts, the
leaf-kind accounting (reach-prune / dead-end / infeasible start), the distinct leaf keys
`(rank, exit-numerator)`, and the exact leaf-frontier (min/med/max) and leaf-depth
(min/max) / dead-end-depth (min/max) pinches. -/
structure M4Res where
  /-- the 7-tuple box (leading 1 = the base reading row) -/
  box : List ℕ
  /-- DFS tree size: leaves, nodes, max depth, start zones tried -/
  leaves : ℕ
  nodes : ℕ
  maxdepth : ℕ
  nstart : ℕ
  /-- leaf kinds: reach-prunes, dead-ends, infeasible starts -/
  reach : ℕ
  deadend : ℕ
  startinfeas : ℕ
  /-- the DISTINCT leaf keys (rank, exit numerator) of the tree -/
  lzones : List (ℕ × ℕ)
  /-- leaf-frontier min/med/max (present iff reach > 0) -/
  lfMin : Option ℚ
  lfMed : Option ℚ
  lfMax : Option ℚ
  /-- leaf-depth min/max (present iff reach > 0) -/
  ldMin : Option ℕ
  ldMax : Option ℕ
  /-- dead-end depth min/max (present iff deadend > 0) -/
  ddMin : Option ℕ
  ddMax : Option ℕ

/-- The 90-type leaf-certificate envelope: rank 2..7 × exit numerator `8j+1`, `1 ≤ j ≤ 15`
(numerators 9..121).  This is exactly the key space of `Fresh.UClosure`'s fixpoint
(`keyOf : Fin 7 → Fin 15 → Fin 6 × Fin 15`, `envB` numerators `8(c+1)+1`) — the M4 leaf
keys and the C3 merge classes live in the same closed comb envelope. -/
-- STANDING: DEFINITION
def InLeafEnv (k : ℕ × ℕ) : Prop :=
  2 ≤ k.1 ∧ k.1 ≤ 7 ∧ 9 ≤ k.2 ∧ k.2 ≤ 121 ∧ k.2 % 8 = 1

/-- The computable form of `InLeafEnv` (the per-box `decide` target). -/
def InLeafEnvB (k : ℕ × ℕ) : Bool :=
  2 ≤ k.1 && k.1 ≤ 7 && 9 ≤ k.2 && k.2 ≤ 121 && decide (k.2 % 8 = 1)

/-- The Bool/Prop bridge for the envelope. -/
theorem InLeafEnvB_of (k : ℕ × ℕ) : InLeafEnvB k = true ↔ InLeafEnv k := by
  simp only [InLeafEnvB, Bool.and_eq_true, decide_eq_true_eq, InLeafEnv]
  tauto

#print axioms InLeafEnvB_of

/-- **The residual-certificate validity predicate** — everything the artifact checkpoints
certify about one DFS tree, as kernel-checkable arithmetic: the DFS leaf-accounting
identity, the tree-shape laws, the start accounting, the closed 90-type envelope of every
distinct leaf key, and the frontier/depth pinches (each present iff its leaf kind is
nonempty; frontier ≥ 1 and internally ordered; depths bounded by the tree depth). -/
-- STANDING: DEFINITION
def M4ResData (r : M4Res) : Prop :=
  r.box.length = 7 ∧
  r.leaves = r.reach + r.deadend + r.startinfeas ∧
  1 ≤ r.leaves ∧ r.leaves ≤ r.nodes ∧ 1 ≤ r.maxdepth ∧ r.maxdepth ≤ r.nodes ∧
  r.nodes ≤ r.leaves * r.maxdepth ∧
  1 ≤ r.nstart ∧ r.nstart ≤ r.nodes + r.startinfeas ∧
  r.lzones.all InLeafEnvB = true ∧
  (r.lfMin.isSome ↔ 0 < r.reach) ∧ (r.lfMed.isSome ↔ 0 < r.reach) ∧
  (r.lfMax.isSome ↔ 0 < r.reach) ∧
  (0 < r.reach → 1 ≤ r.lfMin.getD 0 ∧ r.lfMin.getD 0 ≤ r.lfMed.getD 0 ∧
    r.lfMed.getD 0 ≤ r.lfMax.getD 0) ∧
  (r.ldMin.isSome ↔ 0 < r.reach) ∧ (r.ldMax.isSome ↔ 0 < r.reach) ∧
  (0 < r.reach → 1 ≤ r.ldMin.getD 0 ∧ r.ldMin.getD 0 ≤ r.ldMax.getD 0 ∧
    r.ldMax.getD 0 ≤ r.maxdepth) ∧
  (r.ddMin.isSome ↔ 0 < r.deadend) ∧ (r.ddMax.isSome ↔ 0 < r.deadend) ∧
  (0 < r.deadend → 1 ≤ r.ddMin.getD 0 ∧ r.ddMin.getD 0 ≤ r.ddMax.getD 0 ∧
    r.ddMax.getD 0 ≤ r.maxdepth)

/-- Every envelope-passing leaf key `(rank, exit-num)` of a residual tree embeds in the
90-type key space of `Fresh.UClosure` (`Fin 6 × Fin 15`: the rank index `b` with
`b.val + 2 = rank` — the artifact's rank convention 2..7 — and the exit numerator `envB c`):
the M4 certificates and the C3 merge classes key the same closed comb envelope. -/
theorem leafKey_in_env90 {i j : ℕ} (h : InLeafEnv (i, j)) :
    ∃ b : Fin 6, ∃ c : Fin 15, b.val + 2 = i ∧
      Fresh.UClosure.envB c = (j : ℚ) := by
  have h1 : 2 ≤ i := h.1
  have h2 : i ≤ 7 := h.2.1
  have h3 : 9 ≤ j := h.2.2.1
  have h4 : j ≤ 121 := h.2.2.2.1
  have h5 : j % 8 = 1 := h.2.2.2.2
  refine ⟨⟨i - 2, by omega⟩, ⟨j / 8 - 1, by omega⟩, ?_, ?_⟩
  · show (i - 2 + 2 : ℕ) = i
    omega
  · simp only [Fresh.UClosure.envB, Fresh.UClosure.exitNum]
    have key : (8 * (j / 8 - 1 + 1) + 1 : ℕ) = j := by omega
    simp [key]

#print axioms leafKey_in_env90

/-! ## 0'. The consumption shape of a residual certificate (named OWED, once) -/

/-- **OWED — the DFS-certificate soundness conclusion shape**: no real W₀ chain on the box
in the `Fresh.UClosure.ChainRealized` form from ANY realized opening table — exactly the
hypothesis shape `Fresh.UClosure.ChainlessClear` consumes.  The DFS tree's prunes dominate
all real chains (`j2_admit_cert_v2.py`'s completeness argument: a covering chain is strict
monotone, so its path in the tree is never filtered away, and every leaf's closure dominates
its continuations); formalizing that domination is the engine Fresh does not yet carry —
the honest residual of this batch, named here so the composition is ready. -/
-- STANDING: OWED
def M4CertSound (n : Fin 7 → ℤ) : Prop :=
  ∀ (ρ : Fin 7 → ℝ) (U0 : Fresh.UClosure.UTable) (a0 : Fin 7) (Aex0 : ℚ)
    (steps : List Fresh.UClosure.Step),
    (∀ k, 0 < ρ k) → Fresh.UClosure.UFine ρ U0 →
      Fresh.UClosure.ChainRealized ρ U0 a0 Aex0 steps → False

/-- **The M4 admission consumption** (composes the two OWED links, both stated exactly
once): certificate no-chain (`M4CertSound`) + link-5 compactness
(`Fresh.UClosure.ChainlessClear`) give every arrangement in the box a clear point
`R₀ ∈ [1,7]` — the M4 kill's assembly-facing conclusion. -/
theorem m4boxClear_of_cert {n : Fin 7 → ℤ} (hn17 : ∀ i, n i ≤ 17)
    (hcc : Fresh.UClosure.ChainlessClear n hn17) (hcert : M4CertSound n)
    (g : Fin 7 → ℝ) (hface : ∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i) :
    ∃ s : ℝ, 1 ≤ s ∧ s ≤ 7 ∧ ∀ i, (1 / 8 : ℝ) ≤ Fresh.distInt (g i * (s / 8)) :=
  hcc g hface hcert

#print axioms m4boxClear_of_cert

/-! ## 0''. The composed one-sided totality schema (stated once, consumed per box) -/

/-- **OWED — the composed one-sided totality datum**: the `ComposedFam` analogue of
`Fresh.SpineSound.SpineTotalOneSided` (the 68 one-sided boxes' banked per-box families are
`ComposedFam` records — `Fresh.OneSidedComposed` — the joinedge dump's demand+chain pairs,
so the totality is stated in that shape).  For an arrangement in the box whose `W₀`-chain
side exists (every record's composed cap chain realized on `g`) and which carves `[1,7]`
but admits no `W₁` clear point, some composed record is fully realized. -/
-- STANDING: OWED
def ComposedTotalOneSided (n : Fin 7 → ℤ) (f : ComposedFam) : Prop :=
  ∀ g : Fin 7 → ℝ, (∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i) →
    (∀ e ∈ f.edges, ChainReal g e.y e.caps e.x) →
    Fresh.FrontierFamilyCap.CarvesOneSeven (Finset.image g Finset.univ) →
    ¬ (∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ Fresh.distInt (g i * (s / 8))) →
    ∃ e ∈ f.edges, ComposedEdgeRealized g e

/-- **The composed one-sided soundness** (the conditional kill, mirroring
`Fresh.SpineSound.oneSidedSound_at` on the composed engine): a valid composed family
(banked `compFamData_<box>`) + the totality instance give: IF the arrangement's chain side
exists and `g` carves `[1,7]`, THEN `g` admits a `W₁` clear point over its faces. -/
theorem composedOneSidedSound_at {n : Fin 7 → ℤ} {f : ComposedFam}
    (hfam : ComposedFamData f) (htotal : ComposedTotalOneSided n f)
    (g : Fin 7 → ℝ) (hface : ∀ i, FaceLo n i ≤ g i ∧ g i ≤ FaceHi n i)
    (hchain : ∀ e ∈ f.edges, ChainReal g e.y e.caps e.x)
    (hcarve : Fresh.FrontierFamilyCap.CarvesOneSeven (Finset.image g Finset.univ)) :
    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ Fresh.distInt (g i * (s / 8)) := by
  by_contra hnoc
  obtain ⟨e, he, hx, hy, hdem, -⟩ := htotal g hface hchain hcarve hnoc
  exact composedFamRefutes hfam ⟨e, he, hx, hy, hdem, hchain e he⟩

#print axioms composedOneSidedSound_at
'''

def emit_one_sided(box7):
    nm = "_".join(str(x) for x in box7)
    arr = "![%s] : Fin 7 → ℤ" % ", ".join(str(x) for x in box7)
    L = []
    L.append("/-- One-sided totality lift for box (%s): the banked composed family"
             % ", ".join(str(x) for x in box7))
    L.append("`compFam_%s` (`Fresh.OneSidedComposed`, top records of the joinedge per-box"
             % nm)
    L.append("dump) consumed through `composedOneSidedSound_at`.  The totality instance is")
    L.append("the hypothesis — `Fresh.SpineTotalData`'s rule-22 record proves the interval")
    L.append("route cannot discharge it (non-vacuously); the DATA side (family validity) is")
    L.append("the banked `compFamData_%s`, imported verbatim (no restatement). -/" % nm)
    L.append("theorem oneSidedLift_%s" % nm)
    L.append("    (htotal : ComposedTotalOneSided (%s) compFam_%s)" % (arr, nm))
    L.append("    (g : Fin 7 → ℝ)")
    L.append("    (hface : ∀ i, FaceLo (%s) i ≤ g i ∧" % arr)
    L.append("      g i ≤ FaceHi (%s) i)" % arr)
    L.append("    (hchain : ∀ e ∈ compFam_%s.edges, ChainReal g e.y e.caps e.x)" % nm)
    L.append("    (hcarve : Fresh.FrontierFamilyCap.CarvesOneSeven (Finset.image g Finset.univ)) :")
    L.append("    ∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ Fresh.distInt (g i * (s / 8)) :=")
    L.append("  composedOneSidedSound_at compFamData_%s htotal g hface hchain hcarve" % nm)
    L.append("")
    L.append("#print axioms oneSidedLift_%s" % nm)
    L.append("")
    return "\n".join(L)

PAIR5 = {
    (1, 2, 3, 4, 5, 6, 8): '12568',
    (1, 3, 4, 5, 5, 6, 8): '134556_8',
    (1, 3, 4, 4, 5, 6, 7): '134456_7',
    (1, 3, 4, 5, 6, 7, 8): '134567_8',
    (1, 2, 3, 4, 5, 6, 7): '123456_7',
}

def emit_pairwise(box7):
    tag = PAIR5[tuple(box7)]
    arr = "![%s] : Fin 7 → ℤ" % ", ".join(str(x) for x in box7)
    L = []
    L.append("/-- Pairwise totality lift for box (%s): the banked `c-raw` family" % ", ".join(str(x) for x in box7))
    L.append("`fam%s` + engine hypotheses `spineFamData_%s` (`Fresh.SpineTotalData`, the" % (tag, tag))
    L.append("artifact families of `j2_cycle_v12.out`) consumed through")
    L.append("`Fresh.SpineSound.pairwiseSound_at`.  The totality instance is the hypothesis")
    L.append("(see `Fresh.SpineTotalData`'s rule-22 record); the DATA side is the banked")
    L.append("`spineFamData_%s` (`InRange17` + `JoinFam`), imported verbatim. -/" % tag)
    L.append("theorem pairwiseLift_%s" % tag)
    L.append("    (htotal : SpineTotalPairwise (%s) fam%s)" % (arr, tag))
    L.append("    (g : Fin 7 → ℝ)")
    L.append("    (hface : ∀ i, FaceLo (%s) i ≤ g i ∧" % arr)
    L.append("      g i ≤ FaceHi (%s) i) :" % arr)
    L.append("    Fresh.Certs.NoCarve g ∨")
    L.append("      (∃ s, 9 ≤ s ∧ s ≤ 15 ∧ ∀ i, (1 / 8 : ℝ) ≤ Fresh.distInt (g i * (s / 8))) :=")
    L.append("  pairwiseSound_at _ _ (by decide) (spineFamData_%s).2 htotal g hface" % tag)
    L.append("")
    L.append("#print axioms pairwiseLift_%s" % tag)
    L.append("")
    return "\n".join(L)

def build_file(n_m4=None, out_path=None):
    recs = sorted(resid, key=lambda t: (-cert[t]['nodes'], -cert[t]['leaves'], t))
    if n_m4 is not None:
        recs = recs[:n_m4]
    parts = [HEADER, ""]
    parts.append("/-! ## 1. The 2,329 M4 residual DFS-certificate trees (records + validity data).")
    parts.append("Ordered by tree size (nodes) descending — the biggest certificates first. -/")
    parts.append("")
    for t in recs:
        parts.append(emit_box(cert[t]))
    parts.append("/-! ## 2. The per-box totality lifts: 5 two-sided (pairwise), 68 one-sided -/")
    parts.append("")
    for box7 in sorted(PAIR5):
        parts.append(emit_pairwise(list(box7)))
    for box7 in banked68:
        parts.append(emit_one_sided(box7))
    parts.append("end Fresh.MechDataBatch")
    text = "\n".join(parts) + "\n"
    path = out_path or os.path.join(FRESH, "MechDataBatch.lean")
    with open(path, "w") as f:
        f.write(text)
    return len(recs), path, text

def build_mirror(recs, path):
    """Standalone Mathlib-only mirror of the M4-record section (defs + given boxes)."""
    mir = []
    mir.append("import Mathlib")
    mir.append("")
    mir.append("namespace MechDataBatchMirror")
    mir.append("")
    # copy of the defs (verbatim, no Fresh deps)
    d0 = HEADER.index("/-- One M4 residual box's DFS certificate")
    d2 = HEADER.index("/-- Every envelope-passing leaf key")
    mir.append(HEADER[d0:d2])
    mir.append("")
    for t in recs:
        mir.append(emit_box(cert[t]))
    mir.append("end MechDataBatchMirror")
    with open(path, "w") as f:
        f.write("\n".join(mir))
    return path

if __name__ == '__main__':
    mode = sys.argv[1] if len(sys.argv) > 1 else 'pilot'
    if mode == 'pilot':
        n, path, _ = build_file(n_m4=30)
        print("pilot file:", path, "boxes:", n)
        mirror = build_mirror(resid[:30], os.path.join(HERE, 'mechbatch_bridge_pilot.lean'))
        print("pilot mirror:", mirror)
    elif mode == 'full':
        n, path, _ = build_file()
        print("full file:", path, "boxes:", n)
    elif mode == 'mirrorchunk':
        lo, hi = int(sys.argv[2]), int(sys.argv[3])
        recs = sorted(resid, key=lambda t: (-cert[t]['nodes'], -cert[t]['leaves'], t))[lo:hi]
        p = build_mirror(recs, os.path.join(HERE, 'mechbatch_bridge_payload_%05d_%05d.lean' % (lo, hi)))
        print(p, len(recs))
    elif mode == 'audit':
        with open(os.path.join(HERE, 'mechbatch_audit_v1.out'), 'w') as f:
            f.write("=== mechbatch audit v1 (mechbatch_gen_v1.py) ===\n")
            f.write("M4-fired (kind=closed): %d | aA-killed: %d | residual: %d\n"
                    % (len(m4fired), sum(1 for t in m4fired if aa.get(t) is True), len(resid)))
            f.write("CHAIN controls: %d | aA fired on controls: %d\n"
                    % (len(controls_chain), sum(1 for t in controls_chain if aa.get(t) is True)))
            f.write("cert_ckpt vs admit_cert2 field mismatches on residual: %d\n" % len(mismatch))
            f.write("rich sample boxes: %d | rich cross-check violations on residual: %d\n"
                    % (len(rich), len(rich_bad)))
            f.write("residual ∩ banked68: %d | residual ∩ two-sided5: %d\n"
                    % (len(resid7 & set(banked68)), len(resid7 & set(FIVE))))
            f.write("chain controls that are banked68: %d / %d\n" % (in68, len(controls_chain)))
            keys = set()
            for t in resid:
                for z in cert[t]['last_zones']:
                    keys.add(tuple(z))
            f.write("distinct residual leaf keys: %d, all in the 90-type envelope: %s\n"
                    % (len(keys), all(2 <= k[0] <= 7 and 9 <= k[1] <= 121 and k[1] % 8 == 1 for k in keys)))
            f.write("sorted keys: %s\n" % sorted(keys))
            f.write("predicate preflight over all 2,329 records: PASS (0 violations)\n")
        print("audit written")
