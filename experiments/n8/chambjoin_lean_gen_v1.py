# chambjoin_lean_gen_v1.py -- generate Fresh/ChamberJoin.lean from chambjoin_classes_v1.json
# (produced by chambjoin_verify_v1.py).  Structure:
#   1. the class-match definitions (ChamberClass / InBox / InClass / InClassSub) -- gamma's
#      InClass predicate per the Track T task: rho's K6Comps contains the class's certifying
#      component (A, B) EXACTLY and rho lies in the class's closed skeleton cell-box;
#   2. the join theorem shapes: join50 (exact-component join; consumes beta's
#      band_union50_via_datasheet with the real-cast atom) and join50_sub (containment
#      join; consumes beta's band_union50_subset + colDead50_imp);
#   3. the per-class emitted instances (BandCertDataExt pattern), ordered NO-ALIVE-ON-GRID
#      first, then GRID-TOO-COARSE, then SKELETON-UNPROBED, then -n_cases; capped by
#      argv[1] (0 = no cap).  Per class SIX declarations:
#        cls_<i>     the class record (kL, kR, A, B, per-position closed cell bounds)
#        rho_<i>     the recorded representative 5-tuple (exact Q literals)
#        castAB_<i>  the real-cast bridge for the edges (norm_num)
#        inclass_<i> InClass rho_i cls_i PROVED: the exact K6 join by kernel decide
#                    (mirrors the data-side verification; decide FAILS if the mirror
#                    disagreed -- compile-gated) + the cell-box by fin_cases/norm_num
#        chjoin_<i>  gamma AT CLASS i for an ARBITRARY tuple: InClass rho cls_i ->
#                    (the datasheet atom chds_i) -> not TupleLonely rho s for s in [25,50)
#        dead_<i>    the recorded representative's death: chjoin_i rho_i + inclass_i
#   4. #print axioms lines (templates + first/mid/last instances).
# Honest counts (emitted/total) are written into the header.  New file only; nothing
# existing is edited.
import json, sys

DIR = '/Users/trentpalelei/Desktop/Math Ex/experiments/n8/'
MANIFEST = DIR + 'chambjoin_classes_v1.json'
LEAN = '/Users/trentpalelei/Desktop/Math Ex/LonelyRunnerFresh/Fresh/ChamberJoin.lean'

HEAD = '''import Mathlib.Tactic
import Fresh.K6BandUnion

/-!
# ChamberJoin: bridge gamma -- the class-match predicate and the datasheet-to-bridge join

New file (2026-11-21); nothing existing is edited.  Imports `Fresh.K6BandUnion` (bridge
beta: `TupleLonely` / `Feasible` / `band_union50` / `band_union50_via_datasheet` /
`band_union50_subset` / `colDead50_imp`, over bridge alpha's `K6Comps`) and, through it,
`Fresh.ChamberDatasheet` (the per-class atoms `chds_i : ColDead50 A B`, all 7,797 classes).

## The class-match predicate (gamma's InClass)

A chamber class is the probe's dedupe key: (skeleton cells, kL, kR, cellL, cellR, a, b),
where (a, b) are the EXACT edges of the instrument's COMP-DEAD kill component for every
recorded tuple of the class (verified data-side: `experiments/n8/chambjoin_verify_v1.out`,
three-way match dump <-> datasheet <-> stream 7,797/7,797, and the exact K6 join
`(a,b) in k6_components(rho)` re-verified on every class representative).  `ChamberClass`
carries the record (kL, kR, the edges A B as rationals, the skeleton's per-position CLOSED
cell bounds); `InClass rho cls` says: `rho`'s K6 decomposition contains `(cls.A, cls.B)` as
an EXACT component and `rho` lies in the class's closed cell-box.  `InClassSub` is the
containment variant (some component of `rho` CONTAINS `[A, B]` -- the [1, 7]-clipping
shape for boundary components).

## The join theorem shapes (gamma's instantiation of beta)

* `join50` -- exact-component join: the datasheet atom at the real-cast edges + the
  component membership give `not TupleLonely rho s` for every tail `s` in [25, 50).
  Consumes beta's `band_union50_via_datasheet` verbatim; gamma's work is exactly the
  InClass wiring (the membership is `hIn.1`; the cell-box half is carried for the
  partition step and is not needed by beta, which has no hypothesis on the other
  components).
* `join50_sub` -- containment join: consumes beta's `band_union50_subset` +
  `colDead50_imp`.

## What is emitted here, honestly

Per class (first tranche, cap `{CAP}` of {TOTAL} classes; order NO-ALIVE-ON-GRID first,
then -n_cases): the class record `cls_i`, the recorded representative `rho_i` (exact
rationals from the probe's own dump), the cast bridge `castAB_i`, the PROVED join
`inclass_i : InClass rho_i cls_i` (the exact component membership by KERNEL DECIDE -- a
mirror discrepancy would fail the compile -- and the cell-box by fin_cases), the per-class
gamma instance `chjoin_i` for an ARBITRARY tuple matching the class, and the recorded
representative's column death `dead_i` (atom + exact join + gamma, the full
datasheet-to-beta-to-gamma loop per recorded tuple).  Emitted here: {EMIT} of {TOTAL}
classes ({NAG} NO-ALIVE-ON-GRID, {GTC} GRID-TOO-COARSE, {SU} SKELETON-UNPROBED).

## Honest scope (what gamma does NOT yet carry)

* The atoms are component-level (S2 scope) at the FIXED edges (A, B); the S1
  chamber-window-uniform claim (the two-line at the q-window endpoints) fires on ZERO of
  the 7,797 census classes -- verified, not assumed (see Fresh.ChamberDatasheet's header).
  Within a chamber the certifying component's edges vary with the readings
  (`a_t = (8kL+1)/rho_L`), and the far tuples of the chamber defeat the two-line: the
  deaths there are interlacing (the RUNNING INTERSECTION of the components' band unions).
* `InClass` is proved here only for the RECORDED representatives (kernel decide, one per
  class).  The partition step -- carrying the deaths to EVERY tuple of the cell-box -- is
  the remaining hyperplane-partition work: for a general cell-box tuple the class's
  component edges vary, and the match is not the exact-component join.  The consumption
  shape for that step is landed in `Fresh.K6Gamma` (`partition_principle`: the cover
  hypothesis `EXISTS cls in classes, InClass rho cls OR InClassSub rho cls` is exactly
  what the assembly needs; gamma dispatches it).  The probe's no-alive-on-grid evidence
  (6,569 classes) is the data-side support; no Lean proof of the cover is faked here.
* A [25,50)-column death is the conclusion everywhere (the atoms' window).  The unbounded
  closed-band form is `Fresh.K6Gamma.gamma_joinC` (consumes beta's `band_union`).

Data side: `experiments/n8/chambjoin_verify_v1.py` (+ `chambjoin_verify_v1.out`,
`chambjoin_classes_v1.json`); generator of this file: `chambjoin_lean_gen_v1.py`.
-/

set_option allowUnsafeReducibility true
attribute [local reducible] Rat.mul Rat.inv

namespace Fresh.ChamberJoin

/-! ## §1 The class-match definitions -/

/-- STANDING: DEFINITION -- a chamber class record: the certifying component's lap
indices (`kL` the L reading's lap / exit side, `kR` the R reading's lap / entry side),
its exact edges `A B : ℚ`, and the skeleton's per-position closed cell bounds
(the cell-box). -/
structure ChamberClass where
  /-- the L reading's lap (exit side of the certifying component) -/
  kL : ℕ
  /-- the R reading's lap (entry side of the certifying component) -/
  kR : ℕ
  /-- the certifying component's left edge (an exact K6 component of the recorded tuples) -/
  A : ℚ
  /-- the certifying component's right edge -/
  B : ℚ
  /-- per-position cell lower bound (closed box) -/
  lo : Fin 5 → ℚ
  /-- per-position cell upper bound (closed box) -/
  hi : Fin 5 → ℚ

/-- STANDING: DEFINITION -- the cell-box: every reading in its skeleton cell's closed
bounds. -/
def InBox (rho : Fin 5 → ℚ) (cls : ChamberClass) : Prop :=
  ∀ i : Fin 5, cls.lo i ≤ rho i ∧ rho i ≤ cls.hi i

/-- STANDING: DEFINITION -- gamma's class match: `rho`'s K6 decomposition contains the
class's certifying component `(A, B)` EXACTLY, and `rho` lies in the class's cell-box. -/
def InClass (rho : Fin 5 → ℚ) (cls : ChamberClass) : Prop :=
  (cls.A, cls.B) ∈ K6Comps rho ∧ InBox rho cls

/-- STANDING: DEFINITION -- the containment variant of the class match: some component of
`rho` CONTAINS the class's dead interval `[A, B]` (the [1, 7]-clipping shape; consumes
beta's `band_union50_subset`). -/
def InClassSub (rho : Fin 5 → ℚ) (cls : ChamberClass) : Prop :=
  ∃ q ∈ K6Comps rho, q.1 ≤ cls.A ∧ cls.B ≤ q.2 ∧ InBox rho cls

/-! ## §2 The join theorem shapes (gamma's instantiation of beta) -/

/-- **The join theorem shape (exact-component join, datasheet atom).**  The class atom at
the real-cast edges + the exact component membership (from `InClass`, `hIn.1`) give the
tuple's column death over [25, 50) -- beta's `band_union50_via_datasheet` verbatim; no
hypothesis on the other components, and the list may be empty (vacuous). -/
theorem join50 (rho : Fin 5 → ℚ) (cls : ChamberClass) (A B : ℝ)
    (hAB : ((cls.A : ℚ) : ℝ) = A ∧ ((cls.B : ℚ) : ℝ) = B)
    (hp : (cls.A, cls.B) ∈ K6Comps rho)
    (hcd : Fresh.ChamberDatasheet.ColDead50 A B)
    (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  Fresh.K6BandUnion.band_union50_via_datasheet rho cls.A cls.B A B hAB.1 hAB.2 hp hcd s hs h50

/-- **The containment join shape.**  A class atom whose interval `[A, B]` lies INSIDE some
component of `rho` kills the tuple over [25, 50) (the [1, 7]-clipping shape; consumes
beta's `band_union50_subset` via the real-to-rational transport `colDead50_imp`). -/
theorem join50_sub (rho : Fin 5 → ℚ) (cls : ChamberClass)
    (hp : ∃ q ∈ K6Comps rho, q.1 ≤ cls.A ∧ cls.B ≤ q.2)
    (hB1 : (1:ℚ) ≤ cls.B)
    (hcd : Fresh.ChamberDatasheet.ColDead50 ((cls.A : ℚ) : ℝ) ((cls.B : ℚ) : ℝ))
    (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) : ¬ Fresh.K6BandUnion.TupleLonely rho s := by
  obtain ⟨q, hq, h1, h2⟩ := hp
  exact Fresh.K6BandUnion.band_union50_subset rho q hq cls.A cls.B ⟨h1, h2⟩ hB1
    (Fresh.K6BandUnion.colDead50_imp cls.A cls.B ((cls.A : ℚ) : ℝ) ((cls.B : ℚ) : ℝ) rfl rfl
      hcd) s hs h50

/-! ## §3 The per-class instances (the emitted join tranche)

One class record + representative + proved join + gamma instance + recorded death per
census class (the emission is capped only by compile budget; the order is
NO-ALIVE-ON-GRID first, then GRID-TOO-COARSE, then SKELETON-UNPROBED, then -n_cases).
The atom `chds_<i>` is `Fresh.ChamberDatasheet`'s own theorem at the same class index
(the datasheet's idx order equals this order -- verified data-side, all 7,797). -/

'''

INST = '''/-- jj#{idx} | {skel} | kL={kL} kR={kR} | cL={cL} cR={cR} | a={a} b={b} | {kind} | {nc} cases | {verdict} -/
def cls_{idx} : ChamberClass :=
  {{ kL := {kL}, kR := {kR}, A := ({a} : ℚ), B := ({b} : ℚ),
    lo := ![{lo}], hi := ![{hi}] }}

/-- The recorded representative 5-tuple of class {idx} (exact rationals, the probe's own
case dump). -/
def rho_{idx} : Fin 5 → ℚ := ![{rho}]

theorem castAB_{idx} : ((cls_{idx}.A : ℚ) : ℝ) = ({a} : ℝ) ∧ ((cls_{idx}.B : ℚ) : ℝ) = ({b} : ℝ) := by
  norm_num [cls_{idx}]

/-- **The proved class match for the recorded representative** (the join): the exact K6
component membership by kernel decide (the emitted `rho_{idx}`/`cls_{idx}` literals make
this a closed computation; a mirror discrepancy would fail the compile) and the cell-box
positionwise. -/
theorem inclass_{idx} : InClass rho_{idx} cls_{idx} :=
  ⟨by decide, by
    intro i
    fin_cases i <;> simp [cls_{idx}, rho_{idx}] <;> norm_num⟩

/-- **gamma at class {idx}, for an ARBITRARY tuple**: any `rho` matching the class (exact
component + cell-box) is dead over the [25, 50) column -- the datasheet atom `chds_{idx}`
consumed through `join50`. -/
theorem chjoin_{idx} (rho : Fin 5 → ℚ) (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50)
    (hIn : InClass rho cls_{idx}) : ¬ Fresh.K6BandUnion.TupleLonely rho s :=
  join50 rho cls_{idx} ({a} : ℝ) ({b} : ℝ) castAB_{idx} hIn.1 Fresh.ChamberDatasheet.chds_{idx} s hs h50

/-- **The recorded representative's column death**: the full datasheet-to-beta-to-gamma
loop for class {idx}'s own tuple (atom `chds_{idx}` + proved join `inclass_{idx}` +
`chjoin_{idx}`). -/
theorem dead_{idx} (s : ℚ) (hs : (25:ℚ) ≤ s) (h50 : s < 50) :
    ¬ Fresh.K6BandUnion.TupleLonely rho_{idx} s :=
  chjoin_{idx} rho_{idx} s hs h50 inclass_{idx}

'''

TAIL = '''/-! ## §4 The tranche as a list (the assembly's queryable cover data) -/

/-- The tranche's class records, in emission order (the cover candidates for the
partition step; `Fresh.K6Gamma.partition_principle` consumes a cover from such a list). -/
def trancheClasses : List ChamberClass :=
  [{CLS_LIST}]

/-- The tranche's recorded representative tuples, in emission order. -/
def trancheRhos : List (Fin 5 → ℚ) :=
  [{RHO_LIST}]

/-! ## §5 The axiom footprint -/

#print axioms Fresh.ChamberJoin.join50
#print axioms Fresh.ChamberJoin.join50_sub
{axioms_inst}

end Fresh.ChamberJoin
'''

def main():
    cap = int(sys.argv[1]) if len(sys.argv) > 1 else 0   # 0 = no cap
    d = json.load(open(MANIFEST))
    cls = d['classes']
    order = {'NO-ALIVE-ON-GRID': 0, 'GRID-TOO-COARSE': 1, 'SKELETON-UNPROBED': 2}
    cls.sort(key=lambda x: (order.get(x['verdict'], 3), -x['n_cases'], x['idx']))
    n_emit = len(cls) if cap <= 0 else min(cap, len(cls))
    tranche = cls[:n_emit]
    parts = [HEAD.format(CAP=n_emit, TOTAL=len(cls), EMIT=n_emit,
                         NAG=sum(1 for x in tranche if x['verdict'] == 'NO-ALIVE-ON-GRID'),
                         GTC=sum(1 for x in tranche if x['verdict'] == 'GRID-TOO-COARSE'),
                         SU=sum(1 for x in tranche if x['verdict'] == 'SKELETON-UNPROBED'))]
    for x in tranche:
        rho = ', '.join(x['rho'])
        lo = ', '.join(x['boxLo'])
        hi = ', '.join(x['boxHi'])
        parts.append(INST.format(idx=x['idx'], skel=x['skel'], kL=x['kL'], kR=x['kR'],
                                 cL=x['cL'], cR=x['cR'], a=x['a'], b=x['b'],
                                 kind=x['kind'], nc=x['n_cases'], verdict=x['verdict'],
                                 rho=rho, lo=lo, hi=hi))
    cls_list = ', '.join('cls_%d' % x['idx'] for x in tranche) or '[]'
    rho_list = ', '.join('rho_%d' % x['idx'] for x in tranche) or '[]'
    axioms_inst = ''
    if n_emit > 0:
        first = tranche[0]['idx']; last = tranche[n_emit - 1]['idx']
        mids = sorted(set([tranche[n_emit // 4]['idx'], tranche[n_emit // 2]['idx'],
                           tranche[3 * n_emit // 4]['idx']]))
        lines = ['#print axioms Fresh.ChamberJoin.inclass_%d' % first]
        lines += ['#print axioms Fresh.ChamberJoin.chjoin_%d' % m for m in mids]
        lines += ['#print axioms Fresh.ChamberJoin.dead_%d' % last]
        axioms_inst = '\n'.join(lines)
    src = ''.join(parts) + TAIL.format(CLS_LIST=cls_list, RHO_LIST=rho_list,
                                       axioms_inst=axioms_inst)
    open(LEAN, 'w').write(src)
    kinds = {}
    for x in tranche:
        kinds[x['kind']] = kinds.get(x['kind'], 0) + 1
    verdicts = {}
    for x in tranche:
        verdicts[x['verdict']] = verdicts.get(x['verdict'], 0) + 1
    print('wrote %s: %d instances of %d classes | verdicts %s | kinds %s'
          % (LEAN, n_emit, len(cls), verdicts, kinds))

if __name__ == '__main__':
    main()
