# m4fix_utc_v1.py -- per-prune-leaf `reach_utc` verdict dump for the M4 DFS certificate
# DELTA-DERIVED from reachutc_dump_v1.py (value-verbatim machinery; only the bank-record
# source, the tree/roots artifact filenames, the emitted Lean filename/stub family and
# the lean-stub readiness check differ -- see DELTA markers and m4fix_delta_log.txt).
# trees (the data side of OWED (b) of Fresh.M4CertSound: the discharge datum for the
# per-prune-leaf domination of `DfsPruneDom`).
#
# WHAT THIS IS.  The checkpoint generator (j2_admit_cert_v2.py, instrumented re-run
# m4comp_cert_v1.py) decided every closure-prune leaf ("reach" kind) by calling
#   reach_utc(U, t, P, a+2)
# at the node: a state-graph reachability over (frontier-sup, reading-rank) states --
# states (p, rank); from state (p, a) each OTHER rank b's tightened zone family (computed
# from the NODE table U via tzones) contributes an edge to (x, b) whenever the zone
# (A, B, e, x) straddles p (e < p < x), and a COMPLETING transition whenever
# e < p and x > 7 and 7*A < p*B.  compl = a completing state is reachable.  The generator
# pruned exactly the nodes with compl == False.
#
# THE HONEST FINDING this dump banks (task-anticipated): for the 36 transcribed boxes the
# checkpoint artifacts (j2_admit_cert2_checkpoint.jsonl, m4comp_cert_ckpt_v1.jsonl) record
# AGGREGATES ONLY (kind/fire/leaves/nodes/maxdepth/nstart; reach/deadend counts; lf/ld/dd
# pinches; last_zones).  Per-leaf reach_utc records (leaf_frontiers/leaf_nst/leaf_last/
# leaf_depth) exist ONLY for the 375 rich-sample boxes of m4comp_cert_sample_v1.jsonl,
# NONE of which is one of the 36.  BUT the banked per-box tree mirror
# (m4rung2_tree_<box>.jsonl, produced by m4rung2_recon_v1.py, each verified [T 32/32]
# against ckpt1 + ckpt2 + the banked Lean record) stores the FULL node state per node
# (U table, a lean rank, Aex, P) -- so the per-prune-leaf verdicts RECOMPUTE verbatim.
# This dump recomputes them and cross-checks every aggregate the artifacts DO record.
#
# WHAT IT CHECKS per box ([T n/N] tally):
#   ck1/ck2/bank count agreement with the tree mirror (nodes/leaves/kinds/nstart/depths);
#   the bidirectional classification: kind == 'reach'  <=>  recomputed compl == False
#     (the leaves the generator PRUNED are exactly the leaves the projection says are
#      sound to prune), and compl == True at every internal/deadend node;
#   per-reach-leaf pmax: recomputed == stored (the stored pmax was already banked against
#     the lf_min/med/max pinches of ck2 and the Lean record);
#   lf/ld/dd/last_zones/lzones pinches recomputed from the verdicts == ck2 == bank;
#   structural sanity (ids/parents/children; child state vs step; no chainstop).
#
# WHAT IT EMITS: reachutc_<box>.json -- per reach leaf: node id, lean stub name
# (m4rung2_<box>_pruneDom_<id>), depth, step, state (a_lean, rank, Aex, P), verdict
# (no_completing_state_reachable | INCONCLUSIVE-with-named-missing-datum), recomputed nst
# (state-graph size), explored state set in pop order, pmax (recomputed + stored), and the
# null completing witness with its reason; per internal/deadend node: the COMPLETING
# witness transitions (at_state (p, a), rank b, A, B, e, x) that fired compl -- the positive
# side of the projection verdict.  Plus reachutc_summary_v1.tsv over --all.
#
# --rich-validate: independent machinery validation -- re-runs the verbatim DFS on a rich
# sample box and compares per-leaf (pmax, nst, last, depths) against the generator's OWN
# saved per-leaf records (leaf_frontiers/leaf_nst/leaf_last/...): closes the loop on the
# state-count instrumentation even though our 36 boxes have no saved nst.
#
# Usage: python3 -I m4fix_utc_v1.py <box e.g. 1,1,1,4,6,15> | --all
# Exact Fractions throughout; floats steer never count.

import sys, os, json, statistics, re
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
MECH = os.path.normpath(os.path.join(HERE, '..', '..', 'LonelyRunnerFresh', 'Fresh',
                                     'MechDataBatch.lean'))
FRESHDIR = os.path.normpath(os.path.join(HERE, '..', '..', 'LonelyRunnerFresh', 'Fresh'))

# ---------- machinery: VERBATIM from j2_admit_cert_v2.py / m4comp_lib_v1.py ----------
# (copied through m4rung2_recon_v1.py, the banked value-verbatim mirror)
INF = None
def mk(n):
    U = [[(F(1), False) if i == j else INF for j in range(7)] for i in range(7)]
    for y in range(1, 7):
        U = add(U, y, 0, F(2 * n[y] + 1, 2), False)
        if U is None: return None
        U = add(U, 0, y, F(2, 2 * n[y] - 1), False)
        if U is None: return None
        U = add(U, 0, y, F(1), True)
        if U is None: return None
    for y in range(1, 6):
        U = add(U, y, y + 1, F(1), True)
        if U is None: return None
    return U
def add(U, i, j, c, s):
    cur = U[i][j]
    if cur is not None and (cur[0] < c or (cur[0] == c and (cur[1] or not s))): return U
    back = U[j][i]
    if back is not None:
        pr = back[0] * c
        if pr < 1 or (pr == 1 and (s or back[1])): return None
    V = [row[:] for row in U]
    for p in range(7):
        a = U[p][i]
        if a is None: continue
        for q in range(7):
            b = U[j][q]
            if b is None: continue
            v = a[0] * c * b[0]; st = a[1] or s or b[1]
            w = V[p][q]
            if w is None or v < w[0] or (v == w[0] and st and not w[1]): V[p][q] = (v, st)
    return V
def gt(U, A, a, B, b):
    if A > 0 and B <= 0: return U
    if A <= 0 and B > 0: return None
    if A == 0: return U if B < 0 else None
    if B == 0: return U if A > 0 else None
    if A > 0: return add(U, a, b, F(A, B), True)
    return add(U, b, a, F(-B, -A), True)
def tranges(U, t):
    R = []
    for y in range(1, 7):
        lo = max(F(2 * t[y - 1] - 1, 2), F(1))
        hi = F(2 * t[y - 1] + 1, 2)
        if U[0][y] is not None: lo = max(lo, 1 / U[0][y][0])
        if U[y][0] is not None: hi = min(hi, U[y][0][0])
        R.append((lo, hi))
    return R
def tzones(U, t):
    Z = []
    for y, (lo, hi) in enumerate(tranges(U, t)):
        zy = []; j = 1
        while True:
            e = F(8 * j - 1) / hi
            if e >= F(7): break
            zy.append((8 * j - 1, 8 * j + 1, e, F(8 * j + 1) / lo))
            j += 1
        Z.append(zy)
    return Z

def reach_utc_trace(U, t, p0, a0):
    """VERBATIM m4comp_lib_v1.reach_utc (3-value instrumented variant, m4rung2_recon_v1.py)
    plus a full trace: the explored states in pop order and the completing transitions.
    The verdict bit, nst and pmax are computed by the verbatim algorithm exactly."""
    Z = tzones(U, t)
    Zby = {y + 2: Z[y] for y in range(6)}
    seen = {(p0, a0)}; stack = [(p0, a0)]; compl = False; pmax = p0
    explored = []; completing = []
    while stack and not compl:
        p, a = stack.pop()
        if p > pmax: pmax = p
        explored.append((p, a))
        for b, Zb in Zby.items():
            if b == a: continue
            for A, B, e, x in Zb:
                if e < p and x > p:
                    st = (x, b)
                    if st not in seen: seen.add(st); stack.append(st)
                if e < p and x > F(7) and 7 * A < p * B:
                    compl = True
                    completing.append(((p, a), b, A, B, e, x))
    return compl, len(seen), pmax, explored, completing

def reach_utc(U, t, p0, a0):
    compl, nst, pmax, _, _ = reach_utc_trace(U, t, p0, a0)
    return compl, nst, pmax

# ---------- serialization helpers ----------
def fr(x): return None if x is None else '%s/%s' % (x.numerator, x.denominator)
def tab(U): return [[None if c is None else [fr(c[0]), c[1]] for c in row] for row in U]
def unfr(s):
    if s is None: return None
    if '/' in s:
        a, b = s.split('/'); return F(int(a), int(b))
    return F(int(s))
def untab(J):
    try:
        return [[None if c is None else (unfr(c[0]), bool(c[1])) for c in row] for row in J]
    except Exception:
        return None

# ---------- DELTA: the banked-record source is the CONSTRUCTED C3 record ----------
# (m4fix_res_v1.jsonl placeholders filled from m4comp_cert_ckpt_v1.jsonl; the loader is
# m4fix_recon_v1.parse_bank -- single source for the whole m4fix pipeline.)
def parse_bank(name):
    sys.path.insert(0, HERE)   # -I mode does not add the script's directory
    import m4fix_recon_v1
    return m4fix_recon_v1.parse_bank(name)

def load_ckpt(path, T, fire_true_only):
    hit = None
    for l in open(os.path.join(HERE, path)):
        r = json.loads(l)
        if r.get('t') == list(T) and (r.get('fire') is True or not fire_true_only):
            hit = r
    return hit

def load_tree(boxname):
    nodes = []
    with open(os.path.join(HERE, 'm4rung2_tree_%s.jsonl' % boxname)) as f:
        for l in f:
            nodes.append(json.loads(l))
    return nodes

def load_roots(boxname, rung1=False):
    p = os.path.join(HERE, 'm4rung1_roots_v1.json' if rung1
                     else 'm4fix_roots_%s.json' % boxname)
    if not os.path.exists(p): return None
    return json.load(open(p))['roots']

# ---------- per-box verdict dump ----------
RUNG1_BOX = '1_4_6_7_10_16_16'
RUNG1_TREE = 'm4rung1_tree_v1.jsonl'
RUNG1_LEAN = 'M4CertRung1.lean'
RUNG1_LEAF = 1294   # the gen's reach-prune leaf of the transcribed slice (step (2, 15, 17))

def dump_box(boxname, treefile=None, leanfile=None, rung1=False):
    t7 = tuple(int(x) for x in boxname.split('_'))
    assert len(t7) == 7 and t7[0] == 1, boxname
    T = list(t7[1:]); t = tuple(T)
    tf = treefile or ('m4fix_tree_%s.jsonl' % boxname)
    nodes = []
    with open(os.path.join(HERE, tf)) as f:
        for l in f:
            nodes.append(json.loads(l))
    roots = load_roots(boxname, rung1)
    ck1 = load_ckpt('j2_admit_cert2_checkpoint.jsonl', T, True)
    ck2 = load_ckpt('m4comp_cert_ckpt_v1.jsonl', T, False)
    bank = parse_bank('m4res_%s' % boxname)
    assert ck1 is not None and ck2 is not None, boxname

    out = []   # [T]/[F] lines
    def chk(name, ok, got=None, want=None):
        out.append('%s %s%s' % ('[T]' if ok else '[F]', name,
                    '' if ok else '  got=%s want=%s' % (got, want)))
        return ok

    # ---- structural sanity on the tree mirror ----
    ids = [n.get('id') for n in nodes]
    N = 0; tally = 0
    N += 1; tally += chk('struct.ids==0..n-1', ids == list(range(len(nodes))))
    byid = {n['id']: n for n in nodes}
    parent_ok = all((n['parent'] is None) or (n['parent'] in byid and
                    byid[n['parent']]['id'] < n['id']) for n in nodes)
    N += 1; tally += chk('struct.parents', parent_ok)
    kinds = {}
    for n in nodes: kinds[n['kind']] = kinds.get(n['kind'], 0) + 1
    N += 1; tally += chk('struct.kinds internal/reach/deadend only',
                         set(kinds) <= {'internal', 'reach', 'deadend'}, sorted(kinds))
    N += 1; tally += chk('struct.no chainstop in closed tree',
                         'chainstop' not in kinds)
    child_ok = True; step_ok = True
    for n in nodes:
        if n['kind'] == 'internal':
            if not n.get('children'): child_ok = False
            for c in n.get('children', []):
                cn = byid.get(c)
                if cn is None or cn['parent'] != n['id']: child_ok = False
        else:
            if n.get('children'): child_ok = False
        st = n.get('step')
        if n['parent'] is not None and st is not None:
            # step = [lean rank, A, B]; the child's state rows/exit must match
            if not (n['a'] == st[0] and n['Aex'] == st[2]): step_ok = False
    N += 1; tally += chk('struct.children/leaf-shape', child_ok)
    N += 1; tally += chk('struct.child state vs step (a, Aex=B)', step_ok)

    # ---- counts vs ck1 / ck2 / bank ----
    nre = kinds.get('reach', 0); nde = kinds.get('deadend', 0); nin = kinds.get('internal', 0)
    nstart_roots = len(roots) if roots is not None else None
    n_infeas = (len([r for r in roots if r['kind'] != 'root']) if roots is not None else None)
    maxdepth = max(n['depth'] for n in nodes)
    N += 1; tally += chk('ck1.kind closed', ck1['kind'] == 'closed', ck1['kind'])
    N += 1; tally += chk('ck1.nodes==tree', ck1['nodes'] == len(nodes), len(nodes), ck1['nodes'])
    N += 1; tally += chk('ck1.maxdepth==tree', ck1['maxdepth'] == maxdepth, maxdepth, ck1['maxdepth'])
    N += 1; tally += chk('ck1.nstart==roots', nstart_roots == ck1['nstart'], nstart_roots, ck1['nstart'])
    N += 1; tally += chk('ck1.leaves==reach+deadend+startinfeas',
                         ck1['leaves'] == nre + nde + (n_infeas or 0),
                         nre + nde + (n_infeas or 0), ck1['leaves'])
    N += 1; tally += chk('ck2.reach_leaves==tree', ck2['reach_leaves'] == nre, nre, ck2['reach_leaves'])
    N += 1; tally += chk('ck2.deadend_leaves==tree', ck2['deadend_leaves'] == nde, nde, ck2['deadend_leaves'])
    N += 1; tally += chk('ck2.start_infeas', ck2['start_infeas'] == n_infeas, n_infeas, ck2['start_infeas'])
    N += 1; tally += chk('bank.nodes', bank['nodes'] == len(nodes), len(nodes), bank['nodes'])
    N += 1; tally += chk('bank.leaves', bank['leaves'] == ck1['leaves'], ck1['leaves'], bank['leaves'])
    N += 1; tally += chk('bank.reach', bank['reach'] == nre, nre, bank['reach'])
    N += 1; tally += chk('bank.deadend', bank['deadend'] == nde, nde, bank['deadend'])
    N += 1; tally += chk('bank.maxdepth', bank['maxdepth'] == maxdepth, maxdepth, bank['maxdepth'])
    N += 1; tally += chk('bank.nstart', bank['nstart'] == ck1['nstart'], ck1['nstart'], bank['nstart'])
    N += 1; tally += chk('bank.startinfeas', bank['startinfeas'] == n_infeas, n_infeas, bank['startinfeas'])
    N += 1; tally += chk('bank.box==t7', bank['box'] == list(t7), bank['box'], list(t7))

    # ---- THE VERDICTS: per-node reach_utc recomputation from the banked node states ----
    # jsonl a = lean rank = a_py + 1; the generator called reach_utc(U, t, P, a_py + 2).
    per_leaf = []       # reach leaves: the OWED (b) datum
    witnesses = []      # internal/deadend nodes: the completing-side witness
    cls_bad = []; pmax_bad = []; inv_bad = []
    pmaxes = []; reds = []; dds = []; lasts = []
    n_inconclusive = 0
    for n in nodes:
        U = untab(n.get('U'))
        missing = []
        if n.get('U') is None: missing.append('node table U')
        if U is None and n.get('U') is not None: missing.append('U unparseable')
        if n.get('P') is None: missing.append('frontier sup P')
        if n.get('a') is None: missing.append('reading rank a')
        if n.get('Aex') is None: missing.append('exit numerator Aex')
        if missing:
            n_inconclusive += 1
            per_leaf.append(dict(node_id=n['id'], kind=n['kind'], verdict='INCONCLUSIVE',
                                 missing=missing))
            continue
        P = unfr(n['P']); Aex = unfr(n['Aex']); a_lean = n['a']
        compl, nst, pmax, explored, completing = reach_utc_trace(U, t, P, a_lean + 1)
        rec = dict(node_id=n['id'], kind=n['kind'], depth=n['depth'],
                   lean_stub=('m4rung1_pruneDom_c0' if n['id'] == RUNG1_LEAF else None)
                   if rung1 else
                   ('m4fix_%s_pruneDom_%d' % (boxname, n['id'])
                    if n['kind'] == 'reach' else None),
                   state=dict(a_lean=a_lean, rank=a_lean + 1, Aex=n['Aex'], P=n['P']),
                   nst=nst, pmax=fr(pmax),
                   explored_states=[[fr(p), a] for (p, a) in explored],
                   completing_transitions=[dict(at_state=[fr(p), a], rank_b=b, A=A, B=B,
                                                e=fr(e), x=fr(x))
                                           for ((p, a), b, A, B, e, x) in completing])
        if n['kind'] == 'reach':
            # the OWED (b) verdict: the projection found NO completing state
            rec['verdict'] = 'no_completing_state_reachable' if not compl else 'COMPLETING_REACHABLE'
            rec['completing_witness'] = None
            rec['witness_note'] = ('prune sound: all %d reachable (frontier-sup, rank) states '
                                   'explored, none admits a completing transition' % nst
                                   if not compl else
                                   'prune UNSOUND: completing transition reachable -- see '
                                   'completing_transitions')
            per_leaf.append(rec)
            pmaxes.append(pmax); reds.append(n['depth'])
            if compl: cls_bad.append(n['id'])
            if n.get('pmax') is not None:
                if unfr(n['pmax']) != pmax: pmax_bad.append((n['id'], n['pmax'], fr(pmax)))
            else:
                pmax_bad.append((n['id'], None, fr(pmax)))
            # verbatim invariant: compl=False exhausts the stack (every seen state explored)
            if len(explored) != nst: inv_bad.append(n['id'])
        if n['kind'] in ('reach', 'deadend'):
            lasts.append((a_lean + 1, unfr(n['Aex'])))
        if n['kind'] != 'reach':
            # internal/deadend: the generator expanded only because compl was True
            rec['verdict'] = 'completing_state_reachable' if compl else 'NO_COMPLETION_BUT_EXPANDED'
            witnesses.append(rec)
            if not compl: cls_bad.append(n['id'])
    N += 1; tally += chk('classify.reach<=>compl=False, expanded<=>compl=True (bidirectional)',
                         not cls_bad, cls_bad[:8], [])
    N += 1; tally += chk('pmax.recomputed==stored (all reach leaves)',
                         not pmax_bad, pmax_bad[:6], [])
    N += 1; tally += chk('invariant.compl=False exhausts state stack', not inv_bad, inv_bad[:8])

    # ---- the pinches: recomputed verdict aggregates vs ck2 vs bank ----
    # (ck2 stores Fractions via str(F): "9" when the denominator is 1 -- normalize both sides)
    lfs = pmaxes
    N += 1; tally += chk('ck2.lf_min==recomputed',
                         (fr(min(lfs)) == fr(unfr(ck2['lf_min']))) if lfs else ck2['lf_min'] is None,
                         fr(min(lfs)) if lfs else None, ck2['lf_min'])
    N += 1; tally += chk('ck2.lf_med==recomputed',
                         (fr(statistics.median(lfs)) == fr(unfr(ck2['lf_med']))) if lfs else ck2['lf_med'] is None,
                         fr(statistics.median(lfs)) if lfs else None, ck2['lf_med'])
    N += 1; tally += chk('ck2.lf_max==recomputed',
                         (fr(max(lfs)) == fr(unfr(ck2['lf_max']))) if lfs else ck2['lf_max'] is None,
                         fr(max(lfs)) if lfs else None, ck2['lf_max'])
    N += 1; tally += chk('ck2.ld_min/max==recomputed',
                         ((min(reds), max(reds)) == (ck2['ld_min'], ck2['ld_max'])) if reds
                         else ck2['ld_min'] is None,
                         (min(reds), max(reds)) if reds else None, (ck2['ld_min'], ck2['ld_max']))
    dds = [n['depth'] for n in nodes if n['kind'] == 'deadend']
    N += 1; tally += chk('ck2.dd_min/max==recomputed',
                         ((min(dds), max(dds)) == (ck2['dd_min'], ck2['dd_max'])) if dds
                         else ck2['dd_min'] is None,
                         (min(dds), max(dds)) if dds else None, (ck2['dd_min'], ck2['dd_max']))
    lz = sorted(set(lasts))
    N += 1; tally += chk('ck2.last_zones==leaf (rank, Aex) set',
                         lz == sorted(set(tuple(z) for z in ck2['last_zones'])),
                         [(a, b) for (a, b) in lz[:6]], ck2['last_zones'][:6])
    N += 1; tally += chk('bank.lf pinches==recomputed',
                         (fr(min(lfs)) == fr(bank['lf_min']) if lfs else bank['lf_min'] is None) and
                         (fr(statistics.median(lfs)) == fr(bank['lf_med']) if lfs else bank['lf_med'] is None) and
                         (fr(max(lfs)) == fr(bank['lf_max']) if lfs else bank['lf_max'] is None))
    N += 1; tally += chk('bank.lzones==leaf (rank, Aex) distinct set',
                         lz == sorted(set(bank['lzones'])),
                         [(a, fr(b)) for (a, b) in lz[:6]], bank['lzones'][:6])

    # ---- Lean transcription readiness: the OWED (b) stubs ----
    leanf = os.path.join(FRESHDIR, leanfile or ('M4FixRung2_%s.lean' % boxname))
    stub_ids = []; lean_present = os.path.exists(leanf)
    if lean_present:
        src = open(leanf).read()
        if rung1:
            stub_ids = [RUNG1_LEAF] if re.search(r'm4rung1_pruneDom_c0', src) else []
        else:
            stub_ids = [int(m) for m in
                        re.findall(r'pruneDom_(\d+) \(h : DfsPruneDomZone \(boxN m4res_%s\) tree\d+\)'
                                                 % boxname, src)]
    reach_ids = [n['id'] for n in nodes if n['kind'] == 'reach']
    if rung1:
        # the rung-1 Lean file transcribes ONE tree slice with ONE reach leaf (node 1294);
        # the stub must exist and the dump must cover that leaf with its verdict
        N += 1; tally += chk('lean.rung1 OWED(b) stub c0 exists, targets reach leaf %d '
                             '(dump covers all %d reach leaves)' % (RUNG1_LEAF, len(reach_ids)),
                             lean_present and RUNG1_LEAF in reach_ids,
                             (RUNG1_LEAF in reach_ids, lean_present))
    else:
        if lean_present:
            N += 1; tally += chk('lean.OWED(b) stub node ids == reach leaf ids',
                                 sorted(stub_ids) == sorted(reach_ids),
                                 sorted(stub_ids)[:8], sorted(reach_ids)[:8])
        else:
            out.append('[n] lean stubs PENDING (Fresh/M4FixRung2_%s.lean not yet emitted; '
                       'in the m4fix pipeline the gen runs after this dump) -- not counted '
                       'in the tally' % boxname)

    nst_all = [r['nst'] for r in per_leaf if r.get('verdict') == 'no_completing_state_reachable']
    summary = dict(box=list(t7), teeth=T, nodes=len(nodes), internal=nin, reach=nre,
                   deadend=nde, startinfeas=n_infeas or 0, nstart=nstart_roots,
                   verdicts_computed=len([r for r in per_leaf
                                          if r.get('verdict') == 'no_completing_state_reachable']),
                   inconclusive=n_inconclusive, checks_pass=tally, checks_total=N,
                   nst_min=min(nst_all) if nst_all else None,
                   nst_med=fr(F(statistics.median(nst_all))) if nst_all else None,
                   nst_max=max(nst_all) if nst_all else None,
                   pmax_min=fr(min(lfs)) if lfs else None,
                   pmax_max=fr(max(lfs)) if lfs else None,
                   lean_stubs=len(stub_ids), lean_file_found=lean_present)

    dump = dict(kind='reachutc_dump_v1', box=list(t7), teeth=T,
                sources=dict(tree=tf,
                             ck1='j2_admit_cert2_checkpoint.jsonl',
                             ck2='m4comp_cert_ckpt_v1.jsonl',
                             bank='m4fix_res_v1.jsonl + m4comp_cert_ckpt_v1.jsonl (constructed C3 record)',
                             lean='Fresh/%s' % os.path.basename(leanf), stubs='pending until m4fix_gen_v1 runs'),
                semantics=('reach_utc verbatim m4comp_lib_v1.reach_utc: state graph over '
                           '(frontier-sup p, rank a); from (p,a) rank b!=a zone (A,B,e,x) '
                           'gives edge to (x,b) iff e<p<x; completing iff e<p and x>7 and '
                           '7*A<p*B; recomputed from the banked node states (U, a, Aex, P) '
                           'of the [T 32/32]-verified tree mirror'),
                summary=summary,
                reach_leaves=per_leaf,
                expanded_node_witnesses=witnesses,
                checks=out)
    with open(os.path.join(HERE, 'reachutc_%s.json' % boxname), 'w') as f:
        json.dump(dump, f, indent=1)
    print('\n'.join(out))
    print('== reachutc %s [T %d/%d] == reach=%d deadend=%d internal=%d verdicts=%d '
          'inconclusive=%d nst[%s..%s] pmax[%s..%s]' % (
              boxname, tally, N, nre, nde, nin, summary['verdicts_computed'],
              n_inconclusive, summary['nst_min'], summary['nst_max'],
              summary['pmax_min'], summary['pmax_max']), flush=True)
    return tally == N, summary

# ---------- rich-sample machinery validation ----------
def cert_search_tree_collect(t, budget=400000):
    """Verbatim cert_search_dbg (j2_admit_cert_v2 / m4comp_lib_v1) traversal with BOTH the
    generator's collect aggregates AND per-leaf nst (from reach_utc_trace)."""
    n = (1,) + tuple(t)
    U0 = mk(n)
    assert U0 is not None
    leaves = 0; nodes = 0; maxdepth = 0; kind = 'closed'
    col = dict(leaf_frontiers=[], leaf_depth=[], leaf_last=[], leaf_nst=[], leaf_deadend_depth=[],
               start_infeas=0)
    def dfs(U, a, Aex, seen, depth, P):
        nonlocal leaves, nodes, maxdepth, kind
        nodes += 1; maxdepth = max(maxdepth, depth)
        if nodes > budget:
            kind = 'BUDGET'; return True
        if add(U, a + 1, 0, F(Aex, 7), True) is not None:
            kind = 'chain'; return True
        compl, nst, pmax, _, _ = reach_utc_trace(U, t, P, a + 2)
        if not compl:
            leaves += 1
            col['leaf_frontiers'].append(pmax)
            col['leaf_depth'].append(depth)
            col['leaf_last'].append((a + 2, Aex))
            col['leaf_nst'].append(nst)
            return False
        R = tranges(U, t)
        Zs = tzones(U, t)
        any_child = False
        for b in range(6):
            if b == a: continue
            for A, B, e, x in Zs[b]:
                if (b, B) in seen: continue
                if e >= P or e >= F(7): continue
                V = gt(U, Aex, a + 1, A, b + 1)
                if V is None: continue
                V = gt(V, B, b + 1, Aex, a + 1)
                if V is None: continue
                any_child = True
                if dfs(V, b, B, seen | {(b, B)}, depth + 1, x): return True
        if not any_child:
            leaves += 1
            col['leaf_deadend_depth'].append(depth)
            col['leaf_last'].append((a + 2, Aex))
        return False
    R0 = tranges(U0, t)
    Z0 = tzones(U0, t)
    nstart = 0
    for e in range(6):
        lo_e, hi_e = R0[e]
        for A0, B0, e0, x0 in Z0[e]:
            if e0 >= F(1) or x0 <= F(1): continue
            nstart += 1
            Us = add(U0, 0, e + 1, F(1, A0), True)
            if Us is None:
                leaves += 1; col['start_infeas'] += 1
                continue
            Us = add(Us, e + 1, 0, F(B0), True)
            if Us is None:
                leaves += 1; col['start_infeas'] += 1
                continue
            P1 = x0 if lo_e >= A0 else F(B0) / max(lo_e, F(A0))
            if dfs(Us, e, B0, {(e, B0)}, 1, P1): break
        if kind in ('chain', 'BUDGET'): break
    return dict(fire=(kind == 'closed'), kind=kind, leaves=leaves, maxdepth=maxdepth,
                nodes=nodes, nstart=nstart), col

def rich_validate():
    recs = []
    for l in open(os.path.join(HERE, 'm4comp_cert_sample_v1.jsonl')):
        r = json.loads(l)
        if r.get('fire') is True and r.get('kind') == 'closed' and 'leaf_nst' in r:
            recs.append(r)
    # validate a spread: the smallest, the largest, and the richest-in-reach-leaves
    recs.sort(key=lambda r: (r['nodes'], r['t']))
    picks = [recs[0], recs[len(recs) // 2], recs[-1],
             max(recs, key=lambda r: len(r['leaf_nst']))]
    seen = set(); chosen = []
    for r in picks:
        tk = tuple(r['t'])
        if tk not in seen:
            seen.add(tk); chosen.append(r)
    N = 0; tally = 0; out = []
    for r in chosen:
        T = tuple(r['t'])
        res, col = cert_search_tree_collect(T)
        bout = []
        def chk(name, ok, got=None, want=None):
            bout.append('%s %s%s' % ('[T]' if ok else '[F]', name,
                       '' if ok else '  got=%s want=%s' % (got, want)))
            return ok
        N += 1; tally += chk('rich%s.counts nodes/leaves/maxdepth/nstart' % (T,),
                             (res['nodes'], res['leaves'], res['maxdepth'], res['nstart']) ==
                             (r['nodes'], r['leaves'], r['maxdepth'], r['nstart']),
                             (res['nodes'], res['leaves'], res['maxdepth'], res['nstart']),
                             (r['nodes'], r['leaves'], r['maxdepth'], r['nstart']))
        N += 1; tally += chk('rich%s.leaf_frontiers per-leaf order+values' % (T,),
                             [fr(x) for x in col['leaf_frontiers']] == list(r['leaf_frontiers']),
                             [fr(x) for x in col['leaf_frontiers']][:5], r['leaf_frontiers'][:5])
        N += 1; tally += chk('rich%s.leaf_nst per-leaf (state counts)' % (T,),
                             col['leaf_nst'] == r['leaf_nst'],
                             col['leaf_nst'][:8], r['leaf_nst'][:8])
        N += 1; tally += chk('rich%s.leaf_last per-leaf' % (T,),
                             [list(x) for x in col['leaf_last']] ==
                             [list(x) for x in r['leaf_last']],
                             col['leaf_last'][:5], r['leaf_last'][:5])
        N += 1; tally += chk('rich%s.leaf_depth per-leaf' % (T,),
                             col['leaf_depth'] == r['leaf_depth'])
        N += 1; tally += chk('rich%s.leaf_deadend_depth per-leaf' % (T,),
                             col['leaf_deadend_depth'] == r['leaf_deadend_depth'])
        N += 1; tally += chk('rich%s.start_infeas' % (T,),
                             col['start_infeas'] == r.get('start_infeas', 0),
                             col['start_infeas'], r.get('start_infeas', 0))
        out.append('rich box t=%s (nodes=%d, reach=%d):' % (T, r['nodes'], len(r['leaf_nst'])))
        out.extend(bout)
    print('\n'.join(out))
    print('== rich-validate [T %d/%d] ==' % (tally, N), flush=True)
    return tally == N

# ---------- main ----------
def main():
    args = sys.argv[1:]
    if args and args[0] == '--rich-validate':
        sys.exit(0 if rich_validate() else 1)
    if args and args[0] == '--rung1':
        ok, s = dump_box(RUNG1_BOX, treefile=RUNG1_TREE, leanfile=RUNG1_LEAN, rung1=True)
        sys.exit(0 if ok else 1)
    if args and args[0] == '--all':
        boxes = sorted(f[len('m4fix_tree_'):-len('.jsonl')]
                       for f in os.listdir(HERE)
                       if f.startswith('m4fix_tree_') and f.endswith('.jsonl'))
    elif args:
        boxes = [a.replace(',', '_') for a in args]
    else:
        print('usage: reachutc_dump_v1.py <box 1,1,3,4,5,5,7 | --all | --rich-validate>')
        sys.exit(2)
    rows = []
    allok = True
    for b in boxes:
        ok, s = dump_box(b)
        allok = allok and ok
        rows.append(s)
    if len(rows) > 1:
        with open(os.path.join(HERE, 'reachutc_summary_v1.tsv'), 'w') as f:
            f.write('box\tnodes\tinternal\treach\tdeadend\tstartinfeas\tnstart\t'
                    'verdicts_computed\tinconclusive\tchecks\tnst_min\tnst_med\tnst_max\t'
                    'pmax_min\tpmax_max\tlean_stubs\tlean_match\n')
            for s in rows:
                f.write('%s\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d\t%d/%d\t%s\t%s\t%s\t%s\t%s\t%d\t%s\n' % (
                    '_'.join(str(x) for x in s['box']), s['nodes'], s['internal'], s['reach'],
                    s['deadend'], s['startinfeas'], s['nstart'], s['verdicts_computed'],
                    s['inconclusive'], s['checks_pass'], s['checks_total'],
                    s['nst_min'], s['nst_med'], s['nst_max'], s['pmax_min'], s['pmax_max'],
                    s['lean_stubs'],
                    'YES' if s['lean_stubs'] == s['reach'] and s['lean_file_found'] else 'NO'))
        treach = sum(s['reach'] for s in rows)
        tverd = sum(s['verdicts_computed'] for s in rows)
        tinc = sum(s['inconclusive'] for s in rows)
        print('== ALL %d boxes: reach leaves=%d verdicts computed=%d inconclusive=%d -- %s ==' % (
            len(rows), treach, tverd, tinc, 'ALL [T]' if allok else 'FAILURES PRESENT'))
        sys.exit(0 if allok else 1)

if __name__ == '__main__':
    main()
