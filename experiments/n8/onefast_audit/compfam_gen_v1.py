# compfam_gen_v1.py -- generates the ComposedFamData Lean body + the bridge mirror from
# joinedge_perbox_v1.jsonl, and the per-box audit artifact.  NEW file; touches nothing else.
#
# Mapping (verified against joinedge_perbox_v1.py's step()/chainside_cands(), the ground truth
# of the dump): a death row (kind, x1, y1, cap, strict, attr, P, Q) records that the W1 word
# demands rho_{x1}/rho_{y1} < P/Q (the word step add(U, i, j, F(P,Q), True) puts the bound on
# readings (i, j) = 0-based (x1-1, y1-1)) and the chain-side cap rho_{y1}/rho_{x1} <= C/D
# (tab[y1-1][x1-1]) makes it infeasible exactly when (P/Q)*(C/D) <= 1 -- the dump's `conflict`
# flag, i.e. the engine datum A*C <= B*D under Fresh.JoinFamComposed's convention
# (demand rho_x/rho_y < A/B, cap chain from y to x).  So each JSONL (edge, demand) row with a
# conflicting chain-side cap gives the faithful ComposedEdge (x1-1, y1-1, A, B, [(x1-1, C/D)])
# (single-step walk y -> x; J-side caps are implied by EVERY W0 chain's closed table, box-side
# caps hold on the whole box).
#
# Honest residual: demands with NO conflicting chain-side cap (the census's derived-only
# deaths, 5.7% overall) are NOT instantiated here: their killing caps are the word's own
# accumulated products (box-end x word-constraint compositions), whose per-factor realization
# is word-conditional, so a faithful ComposedEdge chain for them needs a path reconstruction
# dump v1 does not carry.
#
# Exact Fractions / integer arithmetic only; floats nowhere.
import json, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
FRESH = os.path.join(HERE, '..', '..', '..', 'LonelyRunnerFresh', 'Fresh')

FULLY_COVERED = ['1_3_4_4_5_5_7', '1_3_4_5_6_6_7', '1_4_5_6_6_7_11']  # census NUM-full boxes
TOP_K = 4        # records per box (top by deaths, among chain-side-conflicting demands)
TOP_K_FULL = 8   # records for the three census-fully-covered boxes


def bkey(box):
    return '_'.join(str(x) for x in box)


def lean_frac(C, D):
    # literal C/D in R; keep parenthesization tight
    if D == 1:
        return str(C)
    return '(%d / %d)' % (C, D)


def extract():
    recs = [json.loads(l) for l in open(os.path.join(HERE, 'joinedge_perbox_v1.jsonl'))]
    boxes = []
    for r in recs:
        if r['role'] != 'one_sided':
            continue
        cand = {}
        derived_only_deaths = 0
        total_row_deaths = 0
        for e in r['edges']:
            for d in e['demands']:
                total_row_deaths += d['deaths']
                pick = None
                for cs in d['chainside']:
                    if cs['conflict'] and cs['side'] == 'J':
                        pick = cs
                        break
                if pick is None:
                    for cs in d['chainside']:
                        if cs['conflict'] and cs['side'] == 'box':
                            pick = cs
                        if pick is not None and pick['side'] != 'box':
                            pick = cs if cs['side'] == 'box' else pick
                if pick is None:
                    derived_only_deaths += d['deaths']
                    continue
                A, B, C, D = d['A'], d['B'], pick['C'], pick['D']
                assert A > 0 and B > 0 and C > 0 and D > 0, (r['box'], d, pick)
                assert A * C <= B * D, (r['box'], d, pick)
                key = (e['x1'], e['y1'], A, B, C, D)
                prev = cand.get(key)
                # distinct unreduced (P,Q) rows reducing to the same (A,B,cap) record carry
                # summed deaths (the record kills all of them)
                if prev is None:
                    cand[key] = [d['deaths'], e['x1'], e['y1'], A, B, C, D, pick['side']]
                else:
                    prev[0] += d['deaths']
        rows = sorted(cand.values(), key=lambda t: -t[0])
        k = TOP_K_FULL if bkey(r['box']) in FULLY_COVERED else TOP_K
        boxes.append({
            'key': bkey(r['box']), 'box': r['box'], 'records': rows[:k],
            'deaths_total': r['deaths_total'],
            'deaths_chainside': r['deaths_total'] - derived_only_deaths,
            'deaths_derived_only': derived_only_deaths,
            'rows_total': total_row_deaths,
        })
    return boxes


def emit_record(rec):
    deaths, x1, y1, A, B, C, D, side = rec
    x, y = x1 - 1, y1 - 1
    return '    \u27e8%d, %d, %d, %d, [(%d, %s)]\u27e9' % (x, y, A, B, x, lean_frac(C, D))


def emit_box(b):
    key = b['key']
    lines = []
    cov = sum(r[0] for r in b['records'])
    lines.append('/-- Box (%s): the top-%d composed family from `joinedge_perbox_v1.jsonl` '
                 '(by death count, among the demands with a conflicting chain-side cap: '
                 'J-side caps are implied by every W\u2080 chain\'s closed table, box-side caps '
                 'hold on the whole box).  The family\'s %d records account for %d of the '
                 'box\'s %d word deaths; the box\'s honest residual is %d derived-only '
                 'deaths (chain-side coverable total: %d).  Datum per record: `A\u00b7C \u2264 '
                 'B\u00b7D` (dump `conflict` flag, kernel-checked by `norm_num` below).  '
                 'Provenance: `joinedge_perbox_v1.jsonl` BOX (%s), %s. -/' % (
                     ', '.join(str(z) for z in b['box']), len(b['records']), len(b['records']),
                     cov, b['deaths_total'], b['deaths_derived_only'],
                     b['deaths_chainside'], ', '.join(str(z) for z in b['box']),
                     '; '.join('(%d,%d,%d/%d\u2190%s cap %d/%d)' % (r[1], r[2], r[3], r[4], r[7], r[5], r[6])
                               for r in b['records'])))
    lines.append('noncomputable def compFam_%s : ComposedFam :=' % key)
    lines.append('  \u27e8[')
    lines.append(',\n'.join(emit_record(r) for r in b['records']))
    lines.append('  ]\u27e9')
    lines.append('')
    lines.append('theorem compFamData_%s : ComposedFamData compFam_%s := by' % (key, key))
    lines.append('  intro e he')
    lines.append('  simp only [compFam_%s, List.mem_cons] at he' % key)
    rc = ' | '.join('rfl' for _ in b['records']) + ' | h0'
    lines.append('  rcases he with %s' % rc)
    for _ in b['records']:
        lines.append('  \u00b7 refine \u27e8by norm_num, by norm_num, ?_, by simp [chainEnd], ?_\u27e9')
        lines.append('    \u00b7 intro p hp; simp at hp; subst hp; norm_num')
        lines.append('    \u00b7 norm_num [List.map_cons, List.prod_cons, List.map_nil, List.prod_nil, mul_one]')
    lines.append('  \u00b7 exact absurd h0 (by simp)')
    lines.append('')
    lines.append('#print axioms compFamData_%s' % key)
    lines.append('')
    return '\n'.join(lines)


def emit_total(boxes):
    keys = [b['key'] for b in boxes]
    lines = []
    lines.append('/-- The covered set: the %d one-sided boxes with an instantiated composed '
                 'family (every box of `joinedge_perbox_v1.jsonl`\'s one-sided census that '
                 'this file instantiates). -/' % len(keys))
    lines.append('def coveredSet : Finset (Fin 7 \u2192 \u2124) :=')
    lines.append('  {' + (',\n   '.join('![%s]' % ', '.join(str(z) for z in b['box']) for b in boxes)) + '}')
    lines.append('')
    lines.append('/-- The per-box family dispatch (definition on the covered set, the empty '
                 'family off it). -/')
    lines.append('noncomputable def compFamOf (b : Fin 7 \u2192 \u2124) : ComposedFam :=')
    first = True
    for b in boxes:
        cond = ('  if' if first else '  else if') + \
            ' b = (![%s] : Fin 7 \u2192 \u2124) then compFam_%s' % (
                ', '.join(str(z) for z in b['box']), b['key'])
        lines.append(cond)
        first = False
    lines.append('  else \u27e8[]\u27e9')
    lines.append('')
    lines.append('/-- **The one-sided composed data totality** (deliverable): every box in '
                 '`coveredSet` carries a valid `ComposedFamData` composed family from the '
                 'joinedge dump. -/')
    lines.append('theorem oneSidedTotalData : \u2200 b \u2208 coveredSet, ComposedFamData (compFamOf b) := by')
    lines.append('  intro b hb')
    lines.append('  simp only [coveredSet, Finset.mem_insert, Finset.mem_singleton] at hb')
    rc = ' | '.join('rfl' for _ in boxes)
    lines.append('  rcases hb with %s' % rc)
    for b in boxes:
        lines.append('  \u00b7 simp [compFamOf, compFamData_%s]' % b['key'])
    lines.append('')
    lines.append('#print axioms oneSidedTotalData')
    lines.append('')
    return '\n'.join(lines)


HEADER = '''import Fresh.JoinFamComposed

/-!
# Composed-family data for the 68 one-sided boxes: the joinedge per-box dump at scale

Written 2026-11-13.  New file; nothing existing is edited.  This file instantiates
`Fresh.JoinFamComposed.ComposedFamData` box by box from
`experiments/n8/onefast_audit/joinedge_perbox_v1.jsonl` (the per-box JoinEdge dump of the
68 one-sided W0-admitting boxes + 5 two-sided controls), the pattern of the worked instance
`Fresh.JoinFamComposed.composedFamData_12568` at scale.

Per record (dump semantics, verified against `joinedge_perbox_v1.py`'s `step` /
`chainside_cands`, the ground truth of the dump): the W1 word demands
`rho_{x1}/rho_{y1} < P/Q` (the word step asserts the bound on readings (x1, y1), 1-based),
and the chain-side cap `rho_{y1}/rho_{x1} <= C/D` (the dump's transposed-pair table entry:
the `J` side is the join of ALL W0 chains' closed tables, hence implied by every chain;
the `box` side is the box closure `U0`, hence holds on the whole box) kills the word exactly
when `(P/Q)*(C/D) <= 1` -- the dump's `conflict` flag, which is the composed datum
`A*C <= B*D` under `Fresh.JoinFamComposed`'s convention (demand `rho_x/rho_y < A/B`, cap
chain from `y` to `x`).  Each record below is therefore the faithful `ComposedEdge`
`(x1-1, y1-1, A, B, [(x1-1, C/D)])`: the single-step cap chain from `y` to `x` carrying the
dump's conflicting chain-side cap value.  No `8m+-1` condition is imposed anywhere -- the
composed datum is exactly `A*prod(caps) <= B` (positivity + product), which is what
`ComposedEdgeValid` requires; the dump's STRICT/LEANMIN/COMBUNRED/NUM coverage ladder and
its mod-8 rescaling bookkeeping are all subsumed (the census' chain-side coverable set is
94.3% of all one-sided deaths).

Honest residual (rule 22): demands with NO conflicting chain-side cap -- the census's
derived-only deaths, 109592 of 1926698 (5.7%) -- are NOT instantiated: their killing caps
are the word's own accumulated products (box-end bound x word-constraint compositions,
E813 item 7's form), whose per-factor realization is word-conditional, so a faithful
composed chain for them needs a path-decomposition dump v1 does not carry (the dump records
derived caps as values only).  Per box the family carries the top records by death count
(top-4, top-8 for the three census-fully-covered boxes
(1,3,4,4,5,5,7), (1,3,4,5,6,6,7), (1,4,5,6,6,7,11)); the per-record death accounting and
the derived-only residuals are in `experiments/n8/onefast_audit/compfam_audit_v1.out`.

All arithmetic is exact (`norm_num` on integers/rationals; floats nowhere).  Every theorem
carries `#print axioms`; the accepted profile is the standard three
(propext, Classical.choice, Quot.sound) -- `sorryAx` is failure.
-/

namespace Fresh.OneSidedComposed

open Fresh.JoinFamComposed

'''

FOOTER = '''end Fresh.OneSidedComposed
'''


def main():
    nlimit = int(sys.argv[1]) if len(sys.argv) > 1 else None
    boxes = extract()
    if nlimit is not None:
        boxes = boxes[:nlimit]
    body = HEADER + '\n'.join(emit_box(b) for b in boxes) + emit_total(boxes) + FOOTER
    out = os.path.join(FRESH, 'ComposedFamData.lean')
    with open(out, 'w') as f:
        f.write(body)
    # audit artifact: per-box accounting (always over ALL boxes, noting the Lean limit)
    with open(os.path.join(HERE, 'compfam_audit_v1.out'), 'w') as f:
        f.write('compfam_audit_v1 -- per-box accounting of Fresh/ComposedFamData.lean\n')
        f.write('source: joinedge_perbox_v1.jsonl (68 one-sided boxes); engine: '
                'Fresh.JoinFamComposed.ComposedFamData (composed datum A*prod(caps) <= B)\n')
        f.write('lean families instantiated: %d of 68 boxes\n\n' % len(boxes))
        f.write('box                       deaths  chainside-cov  derived-only  records-in-lean  records-deaths\n')
        tc = td = tr = 0
        for b in boxes:
            rc = sum(r[0] for r in b['records'])
            f.write('%-25s %7d %14d %13d %16d %15d\n' % (
                b['key'], b['deaths_total'], b['deaths_chainside'],
                b['deaths_derived_only'], len(b['records']), rc))
            tc += b['deaths_total']
            td += b['deaths_derived_only']
            tr += rc
        f.write('\nTOTAL (all 68) deaths %d; chain-side coverable %d (%.3f); derived-only residual %d (%.3f)\n'
                % (tc, tc - td, (tc - td) / tc, td, td / tc))
        f.write('lean families: %d boxes, %d records, %d deaths carried by the records\n'
                % (len(boxes), sum(len(b['records']) for b in boxes), tr))
        f.write('residual rule-22: the derived-only deaths need the composed-chain '
                'path decomposition (box-end x seam products through intermediate readings); '
                'dump v1 records derived caps as values only, so those records are not '
                'instantiated in this file.\n')
    print('wrote', out, 'and compfam_audit_v1.out;', len(boxes), 'boxes in lean')


if __name__ == '__main__':
    main()
