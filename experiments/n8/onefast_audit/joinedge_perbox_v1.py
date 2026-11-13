# joinedge_perbox_v1.py -- per-box JoinEdge dump for the SpineTotal one-sided lift
# (HANDOVER_2026_11_09_v1.md open item 3; SpineTotalData.lean section 5 (iii) data gap).
#
# Reruns j2_cycle_v6.py's one-sided enumeration (verbatim machinery: exec of j2_cycle_v2.py's
# pre-main, join_tables, w0chains, and w1_kill_families with the death record extended by the
# cap's strict flag) over all 73 W0-admitting boxes (the 68 one-sided chain boxes + the 5
# two-sided controls), dumping PER BOX:
#   - the raw word-edge deaths: per (kind, x, y) edge, per unreduced (P, Q) demand, the cap-side
#     pairs observed (value, strict, attribution box/J/derived) with counts;
#   - reduced demand (A, B) with mod-8 residues (A must be 8m+-1 for JoinFam; B recorded too --
#     the comb form wants both, reduction can break it, cf. 9/15 -> 3/5);
#   - CHAIN-SIDE cap candidates (J join value and U0 box-closure value on the transposed pair,
#     both chain-implied: every W0 chain's closed table is <= J there, and U0 holds on the box),
#     with conflict A*C <= B*D and the Lean JoinFam validity flags
#     (B > 0, D > 0, A*C <= B*D, A = 1 or 7 mod 8, C = 1 or 7 mod 8 -- Fresh.FilterAssembly.JoinFam);
#   - per-box family summary: raw edges, JoinFam-valid chain-side family edges (the Lean
#     JoinEdge sets, 0-based x, y), deaths covered by such edges, and the verdict
#     (joinfam_total_ready / needs_composition / residual_pairwise);
#   - for the 5 two-sided controls: the j2_cycle_v12 c-raw family classification rerun
#     (five_box verbatim), checked against the banked spineFamData_* families of
#     Fresh/SpineTotalData.lean (rows AND pair counts from j2_cycle_v12.out) [T 5/5].
#
# Composition (E813 item 7 / E814 item 4 product form): deaths whose conflict is reachable only
# through a derived cap (or a chain-side cap whose numerator is not 8m+-1) are flagged -- they
# need the composed-cap mechanism (products of one start/box-end and seam bounds) instead of a
# single raw JoinEdge datum.
#
# NEW file; nothing existing is modified.  Exact Fractions throughout; floats nowhere.
import os, sys, time, json, re
from fractions import Fraction as F
from collections import Counter, defaultdict

N8 = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(N8)  # the v6 machinery opens its files by relative name (same cwd as the original runs)
AUD = os.path.join(N8, 'onefast_audit')

t00 = time.time()
src = open('j2_cycle_v2.py').read()
exec(src.split("\nif __name__ == '__main__':")[0])
from fractions import Fraction as Fraction

def join_tables(Ts):
    # verbatim j2_cycle_v6.py / j2_cycle_v7.py
    J = [r[:] for r in Ts[0]]
    for W in Ts[1:]:
        for i in range(7):
            for j in range(7):
                a, b = J[i][j], W[i][j]
                if a is None or b is None: J[i][j] = None
                elif b[0] > a[0] or (b[0] == a[0] and a[1] and not b[1]): J[i][j] = b
    return J

PM1 = (1, 7)
def pm1(x): return x % 8 in PM1

FIVE = [(1, 2, 3, 4, 5, 6, 8), (1, 3, 4, 5, 5, 6, 8), (1, 3, 4, 4, 5, 6, 7),
        (1, 3, 4, 5, 6, 7, 8), (1, 2, 3, 4, 5, 6, 7)]

# The banked c-raw families of Fresh/SpineTotalData.lean (provenance lines 42-48), with the
# pair counts printed in j2_cycle_v12.out's top-16 RAW families blocks.
BANKED_CRAW = {
    (1, 2, 3, 4, 5, 6, 8): {('seamE', 2, 6, '17/7', '25/63'): 5742,
                            ('seamE', 2, 6, '41/17', '25/63'): 2820},
    (1, 3, 4, 5, 5, 6, 8): {('seamE', 5, 3, '17/23', '49/39'): 5968},
    (1, 3, 4, 4, 5, 6, 7): {('seamE', 5, 3, '17/23', '49/39'): 19672,
                            ('seamE', 7, 2, '17/47', '73/31'): 11752},
    (1, 3, 4, 5, 6, 7, 8): {('seamM', 7, 3, '17/39', '97/49'): 17428},
    (1, 2, 3, 4, 5, 6, 7): {('seamE', 2, 7, '49/17', '33/103'): 17444},
}

# v6.out per-box regression data (deaths / completions lines).
V6_OUT = {}
for l in open(os.path.join(N8, 'j2_cycle_v6.out')):
    m = re.match(r'\(([\d, ]+)\) deaths (\d+) completions (\d+)', l.strip())
    if m: V6_OUT[tuple(int(z) for z in m.group(1).split(','))] = (int(m.group(2)), int(m.group(3)))

def frac_str(fr): return str(fr)

def w1_kill_families_pb(n, J, dl):
    # j2_cycle_v6.py's w1_kill_families, extended: per-box death records with the cap's strict
    # flag added; U0/UJ returned for the chain-side classification.
    U0 = mk(n); Z = []
    for y in range(1, 7):
        hi = n[y] + F(1, 2)
        j = 1
        while 8 * j - 1 < 15 * hi + 2:
            Z.append((y, 8 * j - 1, 8 * j + 1)); j += 1
    UJ = [r[:] for r in U0]
    for i in range(7):
        for j in range(7):
            if i != j and J[i][j] is not None:
                UJ = add(UJ, i, j, J[i][j][0], J[i][j][1])
                if UJ is None: return None, None, None, None
    deaths = Counter(); comp = [0]
    def attr(j, i, back):
        if U0[j][i] is not None and U0[j][i][0] == back[0]: return 'box'
        if J[j][i] is not None and J[j][i][0] == back[0]: return 'J'
        return 'derived'
    def step(i, j, P, Q, kind, U):
        c = F(P, Q)
        back = U[j][i]
        if back is not None:
            p = back[0] * c
            if p < 1 or p == 1:
                if i != j:
                    deaths[(kind, i + 1, j + 1, str(back[0]), bool(back[1]), attr(j, i, back), P, Q)] += 1
                return None
        return add(U, i, j, c, True)
    def rec(U, a, Aex, seen):
        if time.time() > dl: raise Budget
        W = step(a, 0, Aex, 15, 'end', U)
        if W is not None: comp[0] += 1; return
        for b, Bn, Ax in Z:
            if (b, Ax) in seen: continue
            V = step(a, b, Aex, Bn, 'seam1', U)
            if V is None: continue
            V = step(b, a, Ax, Aex, 'seam2', V)
            if V is None: continue
            rec(V, b, Ax, seen | {(b, Ax)})
    for y, Bn, Ax in Z:
        V = step(0, y, 9, Bn, 'start1', UJ)
        if V is None: continue
        V = step(y, 0, Ax, 9, 'start2', V)
        if V is None: continue
        rec(V, y, Ax, {(y, Ax)})
    return deaths, comp[0], U0, UJ

def chainside_cands(x1, y1, P, Q, J, U0):
    # Chain-side cap candidates on rho_{y1}/rho_{x1} (1-based readings), i.e. table [y1-1][x1-1]:
    # 'J' = the join of all W0 chains' closed tables (implied by every chain); 'box' = the box
    # closure U0 (holds on the whole box).  Returns the candidate list with the Lean JoinFam flags.
    c = F(P, Q)
    A, B = c.numerator, c.denominator
    out = []
    for side, tab in (('J', J), ('box', U0)):
        e = tab[y1 - 1][x1 - 1]
        if e is None: continue
        cv = e[0]; C, D = cv.numerator, cv.denominator
        conflict = (cv * c <= 1)
        jf = bool(conflict and B > 0 and D > 0 and pm1(A) and pm1(C))
        comb = bool(jf and pm1(B) and pm1(D))
        out.append({'side': side, 'cap': frac_str(cv), 'strict': bool(e[1]),
                    'C': C, 'D': D, 'C_mod8': C % 8, 'D_mod8': D % 8,
                    'conflict': bool(conflict), 'joinfam_valid': jf, 'comb_form': comb})
    return out, (A, B)

def classify_box(n, w0n, dlch, dlen):
    t0 = time.time()
    Cs = w0chains(n, t0 + dlch)
    J = join_tables([C for C, w in Cs])
    deaths, comp, U0, UJ = w1_kill_families_pb(n, J, t0 + dlen)
    if deaths is None:
        # box+J infeasible: the one-sided conditional kill is vacuous on this box
        return {'box': list(n), 'w0n': w0n,
                'role': 'two_sided_control' if n in FIVE else 'one_sided',
                'chains_enumerated': len(Cs), 'deaths_total': 0,
                'deaths_by_attr': {'box': 0, 'J': 0, 'derived': 0}, 'completions': 0,
                'matches_v6_out': False, 'jside_bounds': [], 'edges': [],
                'family': {'raw_edges': 0, 'demands_distinct': 0,
                           'family_edges_chainside_all': 0, 'family_edges_joinfam': 0,
                           'deaths_total': 0, 'deaths_covered_joinfam': 0, 'deaths_uncovered': 0,
                           'uncovered_derived_only': 0, 'uncovered_chainside_non_pm1': 0,
                           'non_pm1_reduced_demands': [], 'non_pm1_chainside_caps': [],
                           'derived_caps_distinct': [], 'verdict': 'box_plus_J_infeasible',
                           'family_edges_joinfam_list': []}}, Cs, J, U0
    # group: (kind, x1, y1) -> (P, Q) -> (cap, strict, attr) -> count
    edges = defaultdict(lambda: defaultdict(Counter))
    for (kind, x1, y1, cap, strict, at, P, Q), cnt in deaths.items():
        edges[(kind, x1, y1)][(P, Q)][(cap, strict, at)] += cnt
    jside_bounds = []
    for j in range(7):
        for i in range(7):
            if i != j and J[j][i] is not None:
                jside_bounds.append([j + 1, i + 1, frac_str(J[j][i][0]), bool(J[j][i][1])])
    fam_all = set(); fam_jf = set()
    deaths_total = sum(deaths.values()); deaths_cov = 0
    unc_derived = 0; unc_nonpm1 = 0
    nonpm1_demands = set(); nonpm1_caps = set(); derived_caps = set()
    edge_out = []
    for (kind, x1, y1), dem in sorted(edges.items()):
        dem_out = []
        for (P, Q), caps in sorted(dem.items(), key=lambda kv: (-sum(kv[1].values()), kv[0])):
            cands, (A, B) = chainside_cands(x1, y1, P, Q, J, U0)
            cov = any(cc['joinfam_valid'] for cc in cands)
            dcount = sum(caps.values())
            deaths_cov += dcount if cov else 0
            cap_out = []
            for (cap, strict, at), cnt in caps.items():
                cv = F(cap)
                C, D = cv.numerator, cv.denominator
                conflict = (cv * F(P, Q) <= 1)
                jf = bool(conflict and pm1(A) and pm1(C))
                cap_out.append({'cap': cap, 'strict': strict, 'attr': at, 'deaths': cnt,
                                'conflict': bool(conflict), 'joinfam_valid': jf,
                                'C_mod8': C % 8, 'D_mod8': D % 8})
                if at == 'derived': derived_caps.add(cap)
                if conflict and not pm1(C): nonpm1_caps.add(cap)
            if not cov:
                # why not covered: chain-side cap conflicts but breaks 8m+-1, or no chain-side
                # conflict at all (derived/composed cap needed, E813 item 7 form)
                if any(cc['conflict'] for cc in cands): unc_nonpm1 += dcount
                else: unc_derived += dcount
            if not pm1(A): nonpm1_demands.add('%d/%d' % (P, Q))
            for cc in cands:
                if cc['conflict']:
                    fam_all.add((x1 - 1, y1 - 1, A, B, cc['C'], cc['D']))
                    if cc['joinfam_valid']:
                        fam_jf.add((x1 - 1, y1 - 1, A, B, cc['C'], cc['D']))
            dem_out.append({'P': P, 'Q': Q, 'deaths': dcount,
                            'A': A, 'B': B, 'A_mod8': A % 8, 'B_mod8': B % 8,
                            'covered_joinfam': bool(cov),
                            'chainside': cands, 'caps': cap_out})
        edge_out.append({'kind': kind, 'x1': x1, 'y1': y1,
                         'deaths': sum(d['deaths'] for d in dem_out), 'demands': dem_out})
    # verdict
    v6ref = V6_OUT.get(tuple(n))
    reg = bool(v6ref and v6ref[0] == deaths_total and v6ref[1] == comp)
    if n in FIVE or comp > 0:
        verdict = 'residual_pairwise'
    elif deaths_cov == deaths_total and deaths_total > 0:
        verdict = 'joinfam_total_ready'
    else:
        verdict = 'needs_composition'
    fam = {'raw_edges': len(edges),
           'demands_distinct': sum(len(d) for d in edges.values()),
           'family_edges_chainside_all': len(fam_all),
           'family_edges_joinfam': len(fam_jf),
           'deaths_total': deaths_total, 'deaths_covered_joinfam': deaths_cov,
           'deaths_uncovered': deaths_total - deaths_cov,
           'uncovered_derived_only': unc_derived, 'uncovered_chainside_non_pm1': unc_nonpm1,
           'non_pm1_reduced_demands': sorted(nonpm1_demands),
           'non_pm1_chainside_caps': sorted(nonpm1_caps),
           'derived_caps_distinct': sorted(derived_caps),
           'verdict': verdict,
           'family_edges_joinfam_list': ['%d,%d,%d,%d,%d,%d' % e for e in sorted(fam_jf)]}
    rec = {'box': list(n), 'w0n': w0n,
           'role': 'two_sided_control' if n in FIVE else 'one_sided',
           'chains_enumerated': len(Cs),
           'deaths_total': deaths_total,
           'deaths_by_attr': {a: sum(1 for k, c in deaths.items() if k[5] == a) for a in ('box', 'J', 'derived')},
           'completions': comp,
           'matches_v6_out': reg,
           'jside_bounds': jside_bounds,
           'edges': edge_out,
           'family': fam}
    return rec, Cs, J, U0

def main():
    boxes = []
    for l in open('j2_g1sweep_class_v1.out'):
        m = re.match(r'\s*\((\d+, [\d, ]+)\) w0n=(\d+)', l)
        if m: boxes.append(((1,) + eval('(' + m.group(1) + ')'), int(m.group(2))))
    print('joinedge_perbox_v1: %d boxes (%d one-sided + %d two-sided controls)' %
          (len(boxes), sum(1 for n, _ in boxes if n not in FIVE), sum(1 for n, _ in boxes if n in FIVE)), flush=True)
    jp = os.path.join(AUD, 'joinedge_perbox_v1.jsonl')
    skip_enum = False
    if os.path.exists(jp):
        try:
            prior = [json.loads(l) for l in open(jp)]
            skip_enum = (len(prior) == len(boxes) and
                         all(r.get('matches_v6_out') is not None and 'edges' in r for r in prior))
            if skip_enum: print('jsonl already holds the complete enumeration; skipping to controls', flush=True)
        except Exception:
            skip_enum = False
    out = open(jp, 'w')
    ncov = 0
    if skip_enum:
        for r in prior: out.write(json.dumps(r, separators=(',', ':')) + '\n')
        ncov = sum(1 for r in prior if r.get('family', {}).get('verdict') == 'joinfam_total_ready')
        print('restored %d prior records (%d joinfam_total_ready)' % (len(prior), ncov), flush=True)
    for bi, (n, w0n) in enumerate(boxes if not skip_enum else []):
        t0 = time.time()
        try:
            rec, Cs, J, U0 = classify_box(n, w0n, 240, 600)
        except Budget:
            print(n, 'BUDGET hit, retrying with doubled deadlines', flush=True)
            rec, Cs, J, U0 = classify_box(n, w0n, 480, 1200)
        out.write(json.dumps(rec, separators=(',', ':')) + '\n')
        f = rec['family']
        print(n, 'role', rec['role'], 'deaths', rec['deaths_total'], 'comp', rec['completions'],
              'attr', rec['deaths_by_attr'], 'raw_edges', f['raw_edges'],
              'famJF', f['family_edges_joinfam'], 'cov', f['deaths_covered_joinfam'],
              '/', f['deaths_total'], 'unc(d,pm1)', f['uncovered_derived_only'], f['uncovered_chainside_non_pm1'],
              'v6reg', rec['matches_v6_out'], 'verdict', f['verdict'],
              'time', round(time.time() - t0, 1), flush=True)
        if f['verdict'] == 'joinfam_total_ready': ncov += 1
    out.close()
    if skip_enum:
        # restore the annotated jsonl (enumeration records were not recomputed)
        pass
    print('=== one-sided enumeration done:', ncov, 'boxes joinfam_total_ready; jsonl written', flush=True)

    # ---- the 5 two-sided controls: j2_cycle_v12 c-raw rerun, banked-match verification ----
    print('=== CONTROLS: j2_cycle_v12 five_box rerun on the 5 two-sided boxes', flush=True)
    src12 = open('j2_cycle_v12.py').read()
    exec(src12.split("\nif __name__ == '__main__':")[0], globals())  # PK, raw_edges_of_w1, five_box, ...
    ctrl_out = {}
    for n in FIVE:
        t0 = time.time()
        try:
            rawk, compc, unres = five_box(n, sample=220 if n == (1, 2, 3, 4, 5, 6, 7) else None)
        except Budget:
            print(n, 'BUDGET hit in five_box, retrying (fresh deadlines)', flush=True)
            rawk, compc, unres = five_box(n, sample=220 if n == (1, 2, 3, 4, 5, 6, 7) else None)
        # project rawk keys (kind, x1, y1, cclass, cap, demand) to the 5-field banked shape
        craw5 = {(k[0], k[1], k[2], k[4], k[5]): v for k, v in rawk.items() if k[3] == 'c-raw'}
        craw = craw5
        banked = BANKED_CRAW[n]
        rows_ok = all(k in craw for k in banked)
        cnt_ok = all(craw.get(k) == v for k, v in banked.items())
        # Lean-form validity of each banked edge (JoinFam form, 0-based x/y)
        lean = []
        for (kind, x1, y1, cap, dem) in banked:
            A, B = F(dem).numerator, F(dem).denominator
            C, D = F(cap).numerator, F(cap).denominator
            ok = (B > 0 and D > 0 and A * C <= B * D and pm1(A) and pm1(C))
            lean.append({'kind': kind, 'lean_edge': [x1 - 1, y1 - 1, A, B, C, D],
                         'conflict': A * C <= B * D, 'A_mod8': A % 8, 'C_mod8': C % 8,
                         'joinfam_valid': ok})
        ok = rows_ok and cnt_ok and all(z['joinfam_valid'] for z in lean)
        ctrl_out[n] = {'craw_rows_all': {';'.join(map(str, k)): v for k, v in craw.items()},
                       'banked_rows_found': rows_ok, 'banked_counts_match': cnt_ok,
                       'lean_form': lean, 'control_ok': ok}
        print('CONTROL', n, 'banked rows found', rows_ok, 'counts match', cnt_ok,
             'lean form ok', all(z['joinfam_valid'] for z in lean),
             '[T] %s' % ('PASS' if ok else 'FAIL'),
             'c-raw rows total', len(craw), 'time', round(time.time() - t0, 1), flush=True)
        for k, v in banked.items():
            print('   banked', k, 'count', v, 'rerun count', craw.get(k), flush=True)
    # annotate the 5 control records in the jsonl with the c-raw census
    recs = [json.loads(l) for l in open(os.path.join(AUD, 'joinedge_perbox_v1.jsonl'))]
    for r in recs:
        n = tuple(r['box'])
        if n in ctrl_out:
            r['twosided_v12'] = ctrl_out[n]
    with open(os.path.join(AUD, 'joinedge_perbox_v1.jsonl'), 'w') as out:
        for r in recs: out.write(json.dumps(r, separators=(',', ':')) + '\n')
    print('=== jsonl rewritten with control annotations;', len(recs), 'records', flush=True)
    print('TOTAL TIME', round(time.time() - t00, 1), flush=True)

if __name__ == '__main__':
    main()
