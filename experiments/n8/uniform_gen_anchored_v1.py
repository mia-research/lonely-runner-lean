# uniform_gen_anchored_v1.py -- E907-sibling emission: the ANCHORED family's 58 killing
# shapes of the v3 uniformity lemma as Lean 4 lemmas (the per-base-instance forms).
#
# INPUT (read-only): v3_uniformity_lemma_v1.py (the instrument, imported as a module) and
#   the census artifacts it reads (v3_march_census_v2_y<y>k<k>.out for the nonvacuous
#   members y6k15/y6k17/y6k25, v3_march_census_table_v1.out for the 9 irred corrections).
# OUTPUT:
#   uniform_gen_anchored_v1.json -- per-shape per-(pattern, base) record: skeleton, roles,
#                            cycle length, the exact edge factors, the deficit polynomial
#                            D_tau(k) = B_tau(k) - A_tau(k), the killing-set kind, all
#                            exact Fractions.
#   Fresh/UniformAnchored_R<len>.lean -- per-cycle-length group files; per shape and
#                            realized (offset pattern, base) ONE theorem
#                            shape_a<id>_pat<j>_k<base> : <product of literal row
#                            factors> < 1   (an unconditional Q fact; the kill criterion
#                            P <= 1 with the strict candidate edge is met as P < 1).
#                            Shapes with NO free slots (all laps pinned by region/base
#                            rows -- the low-zone cycles) emit ONE base-independent
#                            theorem shape_a<id>_const each.
#
# The ANCHORED verification was done AT THE REALIZED BASES {15, 17, 25} (the regime beyond
# is vacuous -- E892: k=48 admits no hinge word), so the emission is per-base-instance
# theorems, NOT forall-m half-line forms: every lap is a realized integer literal, the
# cycle product is a closed rational, and the theorem is the exact statement that the
# word's row instances force product < 1.  Every emitted arithmetic fact is re-verified
# here in exact Fraction arithmetic before emission:
#   (1) replay validation against the recorded rejections (rejection multiset per death
#       node; entry/progress products vs recorded; irred products vs the 9 table
#       corrections) -- the instrument's own build_all anchored branch, verbatim;
#   (2) symbolic self-check: every realized instance reproduces its recorded product from
#       the symbolic (A_tau, B_tau) layer (pattern_polys at the instance's base);
#   (3) factor cross-check: the literal (num, den) rendered from each edge's (kind, laps)
#       via the row grammar equals the edge's recorded weight exactly;
#   (4) statement check: the rendered Lean product expression evaluates (in Fractions) to
#       the recorded product, and product < 1 (abort if any realized instance has
#       product >= 1: those would need the "= 1 with strict edge" emission form).
# python3 -I.
import importlib.util
import json
import os
import sys
from fractions import Fraction as F
from collections import Counter

HERE = os.path.dirname(os.path.abspath(__file__))
EX = HERE
FRESH = os.path.join(os.path.dirname(os.path.dirname(EX)), 'LonelyRunnerFresh')

# ---------------------------------------------------------------- the instrument

spec = importlib.util.spec_from_file_location(
    'v3_uniformity_lemma_v1', os.path.join(EX, 'v3_uniformity_lemma_v1.py'))
vul = importlib.util.module_from_spec(spec)
spec.loader.exec_module(vul)


def poly_sub(a, b):
    n = max(len(a), len(b))
    r = [F(0)] * n
    for i, x in enumerate(a):
        r[i] += x
    for i, x in enumerate(b):
        r[i] -= x
    while len(r) > 1 and r[-1] == 0:
        r.pop()
    return r


def poly_trim(a):
    a = list(a)
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


# ---------------------------------------------------------------- anchored replay
# (build_all's anchored branch, verbatim; the self family is NOT touched here)

def build_anchored():
    corr = vul.load_irred_corrections()
    anchored = vul.load_anchored()
    val = dict(rej_ok=0, rej_bad=0, prod_ok=0, prod_bad=0, irred_corr_ok=0, irred_corr_bad=0)
    cycles = []
    for (y, k), d in sorted(anchored.items()):
        if not d.get('deaths'):
            continue
        j, B = vul.member_params(y, k)
        fam_rows = vul.anchored_base_rows(k, j, y, B)
        for di, (word, rejs_recorded) in enumerate(d['deaths']):
            replay = vul.replay_death(word, fam_rows)
            rec = Counter((r[0], r[1], r[2]) for r in rejs_recorded)
            rep = Counter((r['cand'][0], r['cand'][1], r['why']) for r in replay)
            if rec == rep:
                val['rej_ok'] += 1
            else:
                val['rej_bad'] += 1
                if val['rej_bad'] <= 5:
                    print('REJ-MISMATCH', (y, k, di), 'recorded', sorted(rec.items()),
                          'replayed', sorted(rep.items()))
            recmap = {(r[0], r[1], r[2]): r for r in rejs_recorded}
            for r in replay:
                key = (r['cand'][0], r['cand'][1], r['why'])
                rr = recmap[key]
                prod_rec = F(rr[3]) if rr[3] is not None else None
                if r['why'] == 'irred':
                    cc = corr.get((k, di, key[0], word[-2][0]))
                    ok = (cc is not None and r['product'] == cc)
                    if cc is not None:
                        if ok:
                            val['irred_corr_ok'] += 1
                        else:
                            val['irred_corr_bad'] += 1
                            if val['irred_corr_bad'] <= 5:
                                print('IRRED-CORR-MISMATCH', (y, k, di, key),
                                      'replayed', r['product'], 'table', cc)
                else:
                    ok = (r['product'] is not None and prod_rec == r['product'])
                val['prod_ok' if ok else 'prod_bad'] += 1
                if not ok and val['prod_bad'] <= 5:
                    print('PROD-MISMATCH', (y, k, di, key), 'replayed', r['product'],
                          'recorded', prod_rec)
                cyc = [r['candedge']] + list(r['path'])
                cycles.append(dict(member=('anchored', y, k, j), base=k, why=r['why'],
                                   cand=r['cand'], window=r['window'], word=word, cycle=cyc,
                                   product=r['product'], verified=ok,
                                   readings=tuple([cyc[0][0]] + [e[1] for e in cyc]),
                                   strict=all(e[3] for e in cyc)))
    return cycles, val


# ---------------------------------------------------------------- factor rendering

def edge_factor_lit(kind, laps):
    """The exact (num, den) of one edge's weight from (kind, laps), by the row grammar
    (v3_uniformity_lemma_v1.word_rows / anchored_base_rows / replay_death)."""
    if kind in ('z_entry', 'cand_entry'):
        if kind == 'z_entry' and len(laps) == 1:      # word's first zone: entry vs ROOT
            return (1, 8 * laps[0] - 1)
        return (8 * laps[1] + 1, 8 * laps[0] - 1)     # frontier lap in the numerator
    if kind in ('z_progress', 'cand_progress'):
        if kind == 'z_progress' and len(laps) == 1:   # word's first zone: progress vs ROOT
            return (8 * laps[0] + 1, 1)
        return (8 * laps[0] + 1, 8 * laps[1] + 1)
    if kind in ('z_irred', 'cand_irred'):
        return (8 * laps[0] - 1, 8 * laps[1] + 1)     # den uses pe = 8*lg+1 (lg=0: den 1)
    if kind == 'apex':
        return (33, 7 * (8 * laps[0] - 1))
    if kind == 'cover_floor':
        return (8 * laps[0] + 1, 7)
    if kind == 'cover_entry':
        return (7, 8 * laps[0] - 1)
    if kind == 'weak':
        return (1, 1)
    if kind in ('region6', 'front_lo'):
        return (1, 17 if kind == 'region6' else 7)
    if kind == 'region7':
        return (1, 25)
    if kind == 'front_hi':
        return (5841, 833)
    if kind == 'Bcap':
        return (8 * laps[0] + 1, 7)                   # anchored B-cap (u_0 <= B u_6)
    raise ValueError('unknown edge kind ' + kind)


# ---------------------------------------------------------------- Lean emission

HEADER_TMPL = """import Mathlib

/-!
# UniformAnchored_{group}: per-base-instance killing-shape lemmas for the {group}-edge
anchored cycles

GENERATED FILE (uniform_gen_anchored_v1.py, {n} theorems; regenerate, do not edit).  The
per-base-instance forms of the uniformity lemma for the ANCHORED family's killing shapes
of the v3 uniformity lemma: per shape and realized (offset pattern tau, orbit base k)
occurrence, the shape's cycle product P_tau(k) = A_tau(k)/B_tau(k) -- the product of the
cycle's literal row factors at the realized laps -- is strictly below 1.  Each theorem is
an UNCONDITIONAL Q fact (the laps are realized integer literals; the kill criterion
"P <= 1 with a strict edge" is met as P < 1, the strict candidate edge carried on every
cycle).  Shapes with no free slots (every lap pinned by region/base rows -- the low-zone
cycles) emit one base-independent theorem `shape_a<id>_const` each; the multi-base ones
among them are the verbatim absolute low-zone cycles (89/95 at (12,11), 267/299, 81/89).

Provenance: experiments/n8/uniform_gen_anchored_v1.py replays the nonvacuous anchored
members (y6k15/y6k17/y6k25 -- the realized bases {{15, 17, 25}}; the regime beyond the base
period is vacuous, E892) through the instrument module (import of
v3_uniformity_lemma_v1.py), validates the replay exactly (rejection multisets
{rejok}/{rejtot}, products {prodok}/{prodtot}, irred corrections {irrok}/{irrtot}),
clusters the {ncyc} killing cycles into {nshape} shapes (greedy clique cover, role rule:
abs / tied-to-base / free on window-determined slots -- candidate lap, death-frontier lap,
anchored reading-6 laps), and for each realized (pattern, base) occurrence emits the
product inequality with the deficit D_tau(k) = B_tau(k) - A_tau(k) recorded in the
docstring (exact Fractions; the pattern's killing-set kind over k >= 13 noted for
provenance -- ALL means the pattern kills on the whole realized-regime half-line, SEGMENTS
means only on the stated intervals, which always contain the occurrence base).
Every proof is a constant `norm_num` evaluation -- no folds, no new axioms.  Every theorem
carries #print axioms; the accepted profile is the standard three (propext,
Classical.choice, Quot.sound).
-/

namespace Fresh.UniformAnchored

"""


def factor_str(num, den):
    return f'(({num}:\u211a) / ({den}:\u211a))'


def product_str(edges):
    parts = [factor_str(n, d) for (n, d, _, _) in edges]
    return ' * '.join(parts)


def emit_main():
    print('== uniform_gen_anchored_v1: replay + dump the ANCHORED killing shapes ==')
    cycles, val = build_anchored()
    rejtot = val['rej_ok'] + val['rej_bad']
    prodtot = val['prod_ok'] + val['prod_bad']
    irrtot = val['irred_corr_ok'] + val['irred_corr_bad']
    print(f"replay validation: rej {val['rej_ok']}/{rejtot}, "
          f"prod {val['prod_ok']}/{prodtot}, "
          f"irred-corr {val['irred_corr_ok']}/{irrtot}")
    if val['rej_bad'] or val['prod_bad'] or val['irred_corr_bad']:
        print('ABORT: replay validation failure')
        return 1
    print(f'anchored killing cycles: {len(cycles)}')
    if any(c['product'] is None for c in cycles):
        print('ABORT: a replayed rejection has no killing cycle (product None)')
        return 1
    if any(c['product'] >= 1 for c in cycles):
        bad = [c for c in cycles if c['product'] >= 1]
        print(f'ABORT: {len(bad)} realized instances have product >= 1 '
              f'(they kill only as "= 1 with strict edge"; emission form not prepared)')
        return 1
    if any(not c['strict'] for c in cycles):
        print('note: cycles not all-strict:',
              sum(1 for c in cycles if not c['strict']))

    shapes = vul.cluster_shapes(cycles)
    print(f'anchored shapes: {len(shapes)}')

    ordered = []
    for sh in shapes:
        inst0 = sh['insts'][0]
        roles = vul.resolve_roles(sh)
        ordered.append(dict(sh=sh, roles=roles, inst0=inst0,
                            clen=len(inst0['cycle']),
                            skeleton=vul.skeleton_of(inst0),
                            sk_str=vul.fmt_readings(inst0['readings']),
                            kinds='+'.join(e[4] for e in inst0['cycle']),
                            roles_str=vul.fmt_roles(roles)))
    ordered.sort(key=lambda r: (r['clen'], r['skeleton'], r['kinds'], r['roles_str']))

    recs = []
    files = {}
    counts = Counter()
    occ_total = 0
    const_shapes = 0
    occ_counter = Counter()
    kind_counter = Counter()
    resisted = []
    for idx, r in enumerate(ordered, start=1):
        sid = f'a{idx:03d}'
        sh, roles, inst0 = r['sh'], r['roles'], r['inst0']
        insts = sh['insts']
        frees = [i for i, ro in enumerate(roles) if ro[0] == 'free']
        # realized (pattern, base) occurrences, with a representative instance each
        occs = {}
        for c in insts:
            slots = vul.slots_of(c)
            tau = tuple(slots[i] - c['base'] for i in frees)
            occs.setdefault((tau, c['base']), c)
        occs = sorted(occs.items(), key=lambda t: (t[0][0], t[0][1]))
        # symbolic self-check over EVERY instance (not just representatives)
        for c in insts:
            slots = vul.slots_of(c)
            tau = tuple(slots[i] - c['base'] for i in frees)
            A, B = vul.pattern_polys(sh, tau)
            lhs = vul.poly_eval(A, F(c['base'])) / vul.poly_eval(B, F(c['base']))
            if lhs != c['product']:
                print(f'SYMBOLIC MISMATCH shape {r["sk_str"]} pattern {tau} '
                      f'at base {c["base"]}: symbolic {lhs} vs recorded {c["product"]}')
                return 1
        # per-pattern provenance: deficit polynomial + killing set over k >= 13
        pat_info = {}
        for (tau, _b), _c in occs:
            A, B = vul.pattern_polys(sh, tau)
            D = poly_sub(B, A)
            vd = vul.killing_set(D, 13)
            st_ok, st_why = vul.pos_on_halfline(D, 13)
            pat_info[tau] = dict(A=A, B=B, D=D, kind=vd['kind'],
                                 intervals=vd['intervals'], minval=vd['minval'],
                                 argmin=vd['argmin'], sturm=st_ok, sturm_why=st_why)
            kind_counter[vd['kind']] += 1
        # the occurrence base must lie in the pattern's killing set (the instrument's
        # realized-bases verdict, re-checked here per occurrence)
        for (tau, b), c in occs:
            vd = vul.killing_set(pat_info[tau]['D'], 13)
            ink = any(b >= x and (y2 is None or b <= y2) for (x, y2) in vd['intervals'])
            if not ink:
                print(f'OCCURRENCE OUTSIDE KILLING SET shape {r["sk_str"]} pattern {tau} '
                      f'base {b}')
                return 1

        is_const = not frees
        thms = []
        if is_const:
            const_shapes += 1
            # one base-independent theorem from inst0 (all laps absolute; the product is
            # the same closed rational at every realized base -- checked)
            prods = set(str(c['product']) for c in insts)
            if len(prods) != 1:
                print(f'ABORT: const shape {r["sk_str"]} has divergent products {prods}')
                return 1
            name = f'shape_{sid}_const'
            thm = emit_theorem(name, r, inst0, (), None, pat_info[()])
            if thm is None:
                resisted.append(dict(sid=sid, skeleton=r['sk_str'], kinds=r['kinds']))
            else:
                thms.append(thm)
                occ_total += 1
                occ_counter['const'] += 1
        else:
            for j, ((tau, b), c) in enumerate(occs, start=1):
                name = f'shape_{sid}_pat{j}_k{b}'
                thm = emit_theorem(name, r, c, tau, b, pat_info[tau])
                if thm is None:
                    resisted.append(dict(sid=sid, skeleton=r['sk_str'], kinds=r['kinds'],
                                         tau=[str(x) for x in tau], base=b))
                else:
                    thms.append(thm)
                    occ_total += 1
                    occ_counter[f'k{b}'] += 1
        if not thms:
            continue
        group = f'R{r["clen"]}'
        out = files.setdefault(group, [])
        out.append(f'-- {sid} [{r["clen"]}-edge cycle] {r["sk_str"]} | {r["kinds"]}')
        out.append(f'--   roles: {r["roles_str"]}; {len(insts)} instances at bases '
                   f'{sorted(sh["bases"])}; worst realized '
                   f'{max(c["product"] for c in insts)}')
        out.extend(ln for thm in thms for ln in thm)

    # ---- per-pattern killing-set coverage double-check (over all occurrences) ----
    # (done above per occurrence; nothing further)

    # ---- write files ----
    header_stats = dict(rejok=val['rej_ok'], rejtot=rejtot, prodok=val['prod_ok'],
                        prodtot=prodtot, irrok=val['irred_corr_ok'], irrtot=irrtot,
                        ncyc=len(cycles), nshape=len(ordered))
    total = 0
    for group in sorted(files):
        path = os.path.join(FRESH, 'Fresh', f'UniformAnchored_{group}.lean')
        n = counts[group] = sum(1 for ln in files[group]
                                if ln.startswith('theorem '))
        total += n
        with open(path, 'w') as f:
            f.write(HEADER_TMPL.format(group=group, n=n, **header_stats))
            f.write('\n'.join(files[group]))
            f.write('\n')
        print(f'emitted Fresh/UniformAnchored_{group}.lean: {n} theorems')
    print(f'total emitted theorems: {total} over {len(ordered)} anchored shapes '
          f'({const_shapes} const shapes, {len(ordered) - const_shapes} free-slot '
          f'shapes; occurrences by base {dict(occ_counter)})')
    print(f'pattern killing-set kinds (provenance, k >= 13): {dict(kind_counter)}')
    if resisted:
        print(f'RESISTED: {len(resisted)}')
        for x in resisted:
            print('  ', x)
    with open(os.path.join(EX, 'uniform_gen_anchored_v1.json'), 'w') as f:
        json.dump(dict(stats=dict(header_stats, kinds=dict(kind_counter),
                                  occ=dict(occ_counter),
                                  n_theorems=total,
                                  n_shapes=len(ordered),
                                  const_shapes=const_shapes)),
                  f, default=str, indent=1)
    print('wrote uniform_gen_anchored_v1.json')
    return 0


def emit_theorem(name, r, inst, tau, base, pinfo):
    """One theorem: the shape's cycle product at the realized laps < 1, factors rendered
    literally from the row grammar, cross-checked against the recorded weights.  Returns
    the list of lines, or None if the instance resists rendering."""
    edges = []
    for e in inst['cycle']:
        p, q, w, st, kind, laps = e
        try:
            n, d = edge_factor_lit(kind, laps)
        except ValueError:
            return None
        if F(n, d) != w:
            print(f'FACTOR MISMATCH kind {kind} laps {laps}: rendered {n}/{d} '
                  f'vs recorded {w}')
            return None
        edges.append((n, d, kind, laps))
    prod = F(1)
    for (n, d, _, _) in edges:
        prod *= F(n, d)
    if prod != inst['product']:
        print(f'PRODUCT MISMATCH shape {r["sk_str"]}: rendered {prod} vs recorded '
              f'{inst["product"]}')
        return None
    A, B, D = pinfo['A'], pinfo['B'], pinfo['D']
    dk = vul.poly_eval(D, F(base)) if base is not None else D[0]
    iv = ', '.join((f'[{a},inf)' if bb is None else f'[{a},{bb}]')
                   for (a, bb) in pinfo['intervals'])
    tau_s = ','.join(str(x) for x in tau)
    lines = []
    laps_s = '; '.join(f'{e[2]}@{e[3]}' for e in edges)
    lines.append(f'/-- {r["sk_str"]} | {r["kinds"]} | pattern tau=({tau_s})'
                 + (f' at base k={base}' if base is not None else ' (all laps absolute)')
                 + f': the cycle\'s row factors ({laps_s}) have product '
                 f'{inst["product"].numerator}/{inst["product"].denominator} < 1, i.e. the '
                 f'deficit D_tau = B_tau - A_tau at the realized base is {dk} > 0 '
                 f'(kind {pinfo["kind"]} over k >= 13: {iv}; Sturm real-half-line: '
                 + ('D > 0' if pinfo['sturm'] else pinfo['sturm_why'])
                 + ').  Unconditional Q fact. -/')
    lines.append(f'theorem {name} : {product_str(edges)} < 1 := by')
    lines.append('  norm_num')
    lines.append(f'#print axioms {name}')
    lines.append('')
    return lines


if __name__ == '__main__':
    sys.exit(emit_main())
