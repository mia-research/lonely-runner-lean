# m4fix_recon_v1.py -- C3-box reconstruction of an M4 DFS certificate tree.
# DELTA-DERIVED from m4rung2_recon_v1.py (value-verbatim machinery; only the bank layer and
# the artifact filenames differ -- see the DELTA markers below and m4fix_delta_log.txt).
#
# C3 adaptation of m4rung2_recon_v1.py for an ARBITRARY C3-killed residual box:
# same verbatim machinery (mk/add/gt/tranges/tzones/instrumented reach_utc of
# j2_admit_cert_v2.py / m4comp_lib_v1.py), SAME root-loop abort semantics as the original
# j2_admit_cert_v2.cert_search (dfs returns True on chain/BUDGET abort, False otherwise --
# the rung-1 recon's `if dfs(...): break` returned a node id, which is falsy for node 0;
# this script returns the abort flag so the semantics are exactly the original's), and the
# SAME Lean-spec DfsEnum side-condition audit (children == filter-passing at every internal
# node, no passing candidates at dead ends, no holes at Lean rows 0 and a).
#
# Per box the [T] accounting is verified against THREE sources:
#   (1) j2_admit_cert2_checkpoint.jsonl (kind/fire/leaves/nodes/maxdepth/nstart),
#   (2) m4comp_cert_ckpt_v1.jsonl (leaf kinds, frontier/depth pinches),
#   (3) the CONSTRUCTED C3 record: `m4fix_res_v1.jsonl` (built by m4fix_res_v1.py from the
#       j2 checkpoint) with its PLACEHOLDER leaf-kind/frontier fields filled from the
#       instrumented re-run `m4comp_cert_ckpt_v1.jsonl` (the C3 boxes have NO banked
#       `Fresh.MechDataBatch.m4res_<box>` record -- E923's named gap; the Lean-side record
#       is emitted by m4fix_bank_v1.py into Fresh/M4FixResBank_v1.lean and kernel-checked
#       there via M4ResData).
#
# Usage: python3 -I m4fix_recon_v1.py 1,2,2,4,6,7,10
# Outputs (in this directory): m4fix_tree_<box>.jsonl (all nodes: lean-rank a, step, kind,
#   U table, children, pmax), m4fix_forest_<box>.json (forest summary for the generator:
#   roots, node order, lean-rank seen sets), m4fix_roots_<box>.json (start-zone records);
#   the [T] report goes to stdout (the driver redirects it to m4fix_recon_<box>.out).
import sys, os, json, time, statistics, re
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
MECH = os.path.normpath(os.path.join(HERE, '..', '..', 'LonelyRunnerFresh', 'Fresh',
                                     'MechDataBatch.lean'))

# ---------- machinery: VERBATIM from j2_admit_cert_v2.py ----------
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
def reach_utc(U, t, p0, a0):
    # 3-value instrumented variant, verbatim m4comp_lib_v1.reach_utc
    Z = tzones(U, t)
    Zby = {y + 2: Z[y] for y in range(6)}
    seen = {(p0, a0)}; stack = [(p0, a0)]; compl = False; pmax = p0
    while stack and not compl:
        p, a = stack.pop()
        if p > pmax: pmax = p
        for b, Zb in Zby.items():
            if b == a: continue
            for A, B, e, x in Zb:
                if e < p and x > p:
                    st = (x, b)
                    if st not in seen: seen.add(st); stack.append(st)
                if e < p and x > F(7) and 7 * A < p * B:
                    compl = True
    return compl, len(seen), pmax

# ---------- the Lean-spec candidate audit (verbatim m4rung1_recon_v1.py) ----------
def lean_dfs_hi(U, t, r):
    n = (1,) + tuple(t)
    if r == 0: return F(2 * n[0] + 1)
    hi = F(2 * n[r] + 1, 2)
    if U[r][0] is not None: hi = min(hi, U[r][0][0])
    return hi

def lean_uStep_survives(U, a_lean, b_lean, Aex, A, B):
    V = gt(U, Aex, a_lean, A, b_lean)
    if V is None: return False
    V = gt(V, B, b_lean, Aex, a_lean)
    return V is not None

def audit_node(U, t, a_py, Aex, P, seen_py):
    a_lean = a_py + 1
    seen_lean = set((r + 1, B) for (r, B) in seen_py)
    R = tranges(U, t)
    Zs = tzones(U, t)
    passing = []; hole0 = []; holea = []; jmax = {}
    for b in range(6):
        r = b + 1
        hi = lean_dfs_hi(U, t, r)
        jm = 0; j = 1
        while F(8 * j - 1) / hi < F(7): jm = j; j += 1
        jmax[r] = jm
        if b == a_py: continue
        for A, B, e, x in Zs[b]:
            if (b, B) in seen_py: continue
            if e >= P or e >= F(7): continue
            if lean_uStep_survives(U, a_lean, r, Aex, A, B):
                passing.append((r, A, B))
    hi0 = lean_dfs_hi(U, t, 0)
    jm0 = 0; j = 1
    while F(8 * j - 1) / hi0 < F(7): jm0 = j; j += 1
    jmax[0] = jm0
    for j in range(1, jm0 + 1):
        A = 8 * j - 1; B = 8 * j + 1
        if F(A) / hi0 >= P: continue
        if lean_uStep_survives(U, a_lean, 0, Aex, A, B):
            hole0.append((A, B))
    hia = lean_dfs_hi(U, t, a_lean)
    for j in range(1, jmax[a_lean] + 1):
        A = 8 * j - 1; B = 8 * j + 1
        if (a_py, B) in seen_py: continue
        if F(A) / hia >= P: continue
        if lean_uStep_survives(U, a_lean, a_lean, Aex, A, B):
            holea.append((A, B))
    return passing, hole0, holea, jmax

# ---------- the instrumented certificate search for ONE box (original abort semantics) ----------
def cert_search_tree(t, budget):
    n = (1,) + tuple(t)
    U0 = mk(n)
    assert U0 is not None
    nodes_rec = []
    def new_node(parent, step, depth, a, Aex, P, U):
        nid = len(nodes_rec)
        nodes_rec.append(dict(id=nid, parent=parent, step=step, depth=depth, kind=None,
                              a=a, Aex=Aex, P=P, U=U))
        return nid
    leaves = 0; nodes = 0; maxdepth = 0; kind = 'closed'
    stats = dict(hole0=0, holea=0, hole_nodes=[], mismatch=0, mismatch_nodes=[])
    def dfs(U, a, Aex, seen, depth, P, parent_id, step):
        # returns True on control abort (chain/BUDGET), False otherwise -- EXACTLY the
        # original j2_admit_cert_v2.cert_search semantics
        nonlocal leaves, nodes, maxdepth, kind
        nodes += 1; maxdepth = max(maxdepth, depth)
        nid = new_node(parent_id, step, depth, a, Aex, P, U)
        if nodes > budget:
            kind = 'BUDGET'; return True
        if add(U, a + 1, 0, F(Aex, 7), True) is not None:
            kind = 'chain'; nodes_rec[nid]['kind'] = 'chainstop'; return True
        compl, _nst, pmax = reach_utc(U, t, P, a + 2)
        if not compl:
            leaves += 1
            nodes_rec[nid]['kind'] = 'reach'
            nodes_rec[nid]['pmax'] = pmax
            return False
        R = tranges(U, t)
        Zs = tzones(U, t)
        any_child = False
        child_ids = []
        child_steps = []
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
                Pc = x
                child_steps.append((b + 1, A, B))
                cid = len(nodes_rec)          # the id the recursive call is about to create
                abort = dfs(V, b, B, seen | {(b, B)}, depth + 1, Pc, nid, (b + 1, A, B))
                child_ids.append(cid)
                if kind in ('chain', 'BUDGET'): return True
        if not any_child:
            leaves += 1
            nodes_rec[nid]['kind'] = 'deadend'
        else:
            nodes_rec[nid]['kind'] = 'internal'
            nodes_rec[nid]['children'] = child_ids
            nodes_rec[nid]['child_steps'] = child_steps
        passing, hole0, holea, jmax = audit_node(U, t, a, Aex, P, seen)
        nodes_rec[nid]['jmax'] = jmax
        if hole0 or holea:
            stats['hole0'] += len(hole0); stats['holea'] += len(holea)
            stats['hole_nodes'].append((nid, nodes_rec[nid]['kind'],
                                        [(A, fr(B)) for (A, B) in hole0],
                                        [(A, fr(B)) for (A, B) in holea]))
        if nodes_rec[nid]['kind'] == 'internal':
            if sorted(passing) != sorted(child_steps):
                stats['mismatch'] += 1
                stats['mismatch_nodes'].append(nid)
        elif nodes_rec[nid]['kind'] == 'deadend':
            if passing:
                stats['mismatch'] += 1
                stats['mismatch_nodes'].append(nid)
        return False
    # roots: start zones (verbatim, INCLUDING the original's break-on-abort semantics)
    U0tab = U0
    R0 = tranges(U0tab, t)
    Z0 = tzones(U0tab, t)
    nstart = 0
    roots = []
    for e in range(6):
        lo_e, hi_e = R0[e]
        for A0, B0, e0, x0 in Z0[e]:
            if e0 >= F(1) or x0 <= F(1): continue
            nstart += 1
            Us = add(U0tab, 0, e + 1, F(1, A0), True)
            if Us is None:
                leaves += 1
                roots.append(dict(e=e, A0=A0, B0=B0, kind='startinfeas1'))
                continue
            Us = add(Us, e + 1, 0, F(B0), True)
            if Us is None:
                leaves += 1
                roots.append(dict(e=e, A0=A0, B0=B0, kind='startinfeas2'))
                continue
            P1 = x0 if lo_e >= A0 else F(B0) / max(lo_e, F(A0))
            roots.append(dict(e=e, A0=A0, B0=B0, P1=P1, kind='root'))
            if dfs(Us, e, B0, {(e, B0)}, 1, P1, None, None): break
        if kind in ('chain', 'BUDGET'): break
    fire = (kind == 'closed')
    return dict(fire=fire, kind=kind, leaves=leaves, maxdepth=maxdepth, nodes=nodes,
                nstart=nstart), nodes_rec, roots, stats

# ---------- DELTA: the CONSTRUCTED C3 bank record (m4fix_res_v1.jsonl + ckpt2 fields) ----------
# The C3-killed boxes lack banked `Fresh.MechDataBatch.m4res_<box>` records (E923).  The
# constructed record m4fix_res_v1.jsonl carries box/t/nodes/leaves/maxdepth/fire/kind/nstart
# from j2_admit_cert2_checkpoint.jsonl; its reach/deadend/lf/last_zones fields are
# PLACEHOLDERS (j2 does not record them -- m4fix_res_v1.py defaulted 0/''/[]).  This loader
# returns the same 16-field dict shape as the rung-2 Lean-record parser, with the
# placeholder fields filled from the instrumented re-run m4comp_cert_ckpt_v1.jsonl (whose
# [T]-agreement with the j2 checkpoint on leaves/nodes/maxdepth/nstart over all 10,211 C3
# boxes was verified in pre-flight; the Lean-side record itself is emitted by
# m4fix_bank_v1.py and kernel-checked by M4ResData at compile time).
def parse_bank(name):
    boxname = name[len('m4res_'):]
    t7 = [int(x) for x in boxname.split('_')]
    T = t7[1:]
    fix = None
    for l in open(os.path.join(HERE, 'm4fix_res_v1.jsonl')):
        r = json.loads(l)
        if r.get('box') == t7: fix = r
    assert fix is not None, 'constructed record %s not found in m4fix_res_v1.jsonl' % name
    ck2 = None
    for l in open(os.path.join(HERE, 'm4comp_cert_ckpt_v1.jsonl')):
        r = json.loads(l)
        if r.get('t') == T: ck2 = r
    assert ck2 is not None, 'no m4comp checkpoint record for %s' % (T,)
    def unq(s):
        if s is None: return None
        assert isinstance(s, str), ('unexpected lf field type', s, type(s))
        if '/' in s:
            a, b = s.split('/'); return F(int(a), int(b))
        return F(int(s))
    return dict(box=fix['box'],
                leaves=fix['leaves'], nodes=fix['nodes'], maxdepth=fix['maxdepth'],
                nstart=fix['nstart'],
                reach=int(ck2['reach_leaves']), deadend=int(ck2['deadend_leaves']),
                startinfeas=int(ck2['start_infeas']),
                lzones=[(int(a), int(b)) for (a, b) in ck2['last_zones']],
                lf_min=unq(ck2['lf_min']), lf_med=unq(ck2['lf_med']), lf_max=unq(ck2['lf_max']),
                ld_min=ck2['ld_min'], ld_max=ck2['ld_max'],
                dd_min=ck2['dd_min'], dd_max=ck2['dd_max'],
                # provenance extras (checked in main; placeholders acknowledged, not [T]-ed
                # against the live tree -- they are construction defaults, not data):
                key=fix.get('key'), killed=fix.get('killed'),
                fire=fix['fire'], kind=fix['kind'],
                placeholders=dict(reach_leaves=fix['reach_leaves'],
                                  deadend_leaves=fix['deadend_leaves'],
                                  lf_min=fix['lf_min'], lf_med=fix['lf_med'],
                                  lf_max=fix['lf_max'], last_zones=fix['last_zones']))

def fr(x): return None if x is None else '%s/%s' % (x.numerator, x.denominator)
def tab(U): return [[None if c is None else [fr(c[0]), c[1]] for c in row] for row in U]

def reconstruct_seen(node, nodes_rec):
    seen = set()
    x = node
    while x is not None:
        if x['parent'] is None:
            seen.add((x['a'], x['Aex']))          # the start zone itself (0-based row)
        else:
            seen.add((x['step'][0] - 1, x['step'][2]))   # step stored as (lean rank, A, B)
        x = None if x['parent'] is None else nodes_rec[x['parent']]
    return seen

def main():
    t0 = time.time()
    t7 = tuple(int(x) for x in sys.argv[1].split(','))
    assert len(t7) == 7 and t7[0] == 1, 'pass the 7-tuple box (leading 1)'
    T = t7[1:]
    boxname = '_'.join(str(x) for x in t7)
    BUDGET = 10 ** 9
    res, nodes_rec, roots, stats = cert_search_tree(T, BUDGET)
    print('recon %s done in %.1fs: %s' % (boxname, time.time() - t0, res), flush=True)

    bank = parse_bank('m4res_%s' % boxname)
    ck1 = None
    for l in open(os.path.join(HERE, 'j2_admit_cert2_checkpoint.jsonl')):
        r = json.loads(l)
        if r.get('t') == list(T) and r.get('fire') is True: ck1 = r
    ck2 = None
    for l in open(os.path.join(HERE, 'm4comp_cert_ckpt_v1.jsonl')):
        r = json.loads(l)
        if r.get('t') == list(T): ck2 = r
    assert ck1 is not None and ck2 is not None, 'no checkpoint record for %s' % (T,)

    out = []
    def chk(name, ok, got=None, want=None):
        out.append('%s %s%s' % ('[T]' if ok else '[F]', name,
                    '' if ok else '  got=%s want=%s' % (got, want)))
        return ok
    tally = 0; N = 0
    N += 1; tally += chk('ckpt1.kind', res['kind'] == ck1['kind'], res['kind'], ck1['kind'])
    N += 1; tally += chk('ckpt1.fire', res['fire'] == ck1['fire'])
    N += 1; tally += chk('ckpt1.leaves', res['leaves'] == ck1['leaves'], res['leaves'], ck1['leaves'])
    N += 1; tally += chk('ckpt1.nodes', res['nodes'] == ck1['nodes'], res['nodes'], ck1['nodes'])
    N += 1; tally += chk('ckpt1.maxdepth', res['maxdepth'] == ck1['maxdepth'], res['maxdepth'], ck1['maxdepth'])
    N += 1; tally += chk('ckpt1.nstart', res['nstart'] == ck1['nstart'], res['nstart'], ck1['nstart'])
    N += 1; tally += chk('ckpt2.agree fields',
        all(res[k] == ck2[k] for k in ('leaves', 'nodes', 'maxdepth', 'nstart')))
    nre = sum(1 for x in nodes_rec if x['kind'] == 'reach')
    nde = sum(1 for x in nodes_rec if x['kind'] == 'deadend')
    N += 1; tally += chk('ckpt2.reach', nre == ck2['reach_leaves'], nre, ck2['reach_leaves'])
    N += 1; tally += chk('ckpt2.deadend', nde == ck2['deadend_leaves'], nde, ck2['deadend_leaves'])
    N += 1; tally += chk('ckpt2.startinfeas', res['nstart'] - len([r for r in roots if r['kind'] == 'root']) == ck2['start_infeas'])
    N += 1; tally += chk('bank.leaves = reach+deadend+startinfeas',
                         res['leaves'] == nre + nde + (res['nstart'] - len([r for r in roots if r['kind'] == 'root'])))
    N += 1; tally += chk('bank.leaves', res['leaves'] == bank['leaves'], res['leaves'], bank['leaves'])
    N += 1; tally += chk('bank.nodes', res['nodes'] == bank['nodes'], res['nodes'], bank['nodes'])
    N += 1; tally += chk('bank.maxdepth', res['maxdepth'] == bank['maxdepth'])
    N += 1; tally += chk('bank.nstart', res['nstart'] == bank['nstart'])
    N += 1; tally += chk('bank.reach', nre == bank['reach'], nre, bank['reach'])
    N += 1; tally += chk('bank.deadend', nde == bank['deadend'], nde, bank['deadend'])
    N += 1; tally += chk('bank.startinfeas',
                         res['nstart'] - len([r for r in roots if r['kind'] == 'root']) == bank['startinfeas'])
    lfs = [x['pmax'] for x in nodes_rec if x['kind'] == 'reach']
    lds = [x['depth'] for x in nodes_rec if x['kind'] == 'reach']
    dds = [x['depth'] for x in nodes_rec if x['kind'] == 'deadend']
    N += 1; tally += chk('bank.lf_min', fr(min(lfs)) == fr(bank['lf_min']) if lfs else bank['lf_min'] is None,
                         fr(min(lfs)) if lfs else None, fr(bank['lf_min']))
    N += 1; tally += chk('bank.lf_med', fr(statistics.median(lfs)) == fr(bank['lf_med']) if lfs else bank['lf_med'] is None,
                         fr(statistics.median(lfs)) if lfs else None, fr(bank['lf_med']))
    N += 1; tally += chk('bank.lf_max', fr(max(lfs)) == fr(bank['lf_max']) if lfs else bank['lf_max'] is None,
                         fr(max(lfs)) if lfs else None, fr(bank['lf_max']))
    N += 1; tally += chk('bank.ld', (min(lds), max(lds)) == (bank['ld_min'], bank['ld_max']) if lds else bank['ld_min'] is None,
                         (min(lds), max(lds)) if lds else None, (bank['ld_min'], bank['ld_max']))
    N += 1; tally += chk('bank.dd', (min(dds), max(dds)) == (bank['dd_min'], bank['dd_max']) if dds else bank['dd_min'] is None,
                         (min(dds), max(dds)) if dds else None, (bank['dd_min'], bank['dd_max']))
    ll = sorted(set((x['a'] + 2, x['Aex']) for x in nodes_rec if x['kind'] in ('reach', 'deadend')))
    N += 1; tally += chk('bank.lzones(distinct set)', ll == sorted(set(bank['lzones'])),
                         [(a, fr(b)) for (a, b) in ll[:6]], bank['lzones'][:6])
    N += 1; tally += chk('bank.lzones.count', len(ll) == len(set(bank['lzones'])), len(ll), len(set(bank['lzones'])))
    N += 1; tally += chk('bank.box', bank['box'] == list(t7), bank['box'], list(t7))
    N += 1; tally += chk('shape.leaves<=nodes', res['leaves'] <= res['nodes'])
    N += 1; tally += chk('shape.maxdepth<=nodes', res['maxdepth'] <= res['nodes'])
    N += 1; tally += chk('shape.nodes<=leaves*maxdepth', res['nodes'] <= res['leaves'] * res['maxdepth'])
    N += 1; tally += chk('audit.children==passing (all internal+deadend)', stats['mismatch'] == 0,
                         stats['mismatch'], 0)
    N += 1; tally += chk('audit.no hole at lean row 0', stats['hole0'] == 0, stats['hole0'], 0)
    N += 1; tally += chk('audit.no hole at lean row a', stats['holea'] == 0, stats['holea'], 0)
    N += 1; tally += chk('fix.key==aA (C3-killed provenance)', bank.get('key') == 'aA',
                         bank.get('key'), 'aA')
    N += 1; tally += chk('fix.killed', bank.get('killed') is True, bank.get('killed'), True)
    N += 1; tally += chk('fix.fire==ckpt1.fire', bank.get('fire') == ck1['fire'],
                         bank.get('fire'), ck1['fire'])
    N += 1; tally += chk('fix.kind==ckpt1.kind', bank.get('kind') == ck1['kind'],
                         bank.get('kind'), ck1['kind'])
    N += 1; tally += chk('fix.placeholders-as-constructed (j2 lacks reach/lf/lz fields)',
                         bank['placeholders']['reach_leaves'] == 0 and
                         bank['placeholders']['lf_min'] == '' and
                         bank['placeholders']['last_zones'] == [], bank['placeholders'])
    kindcount = {}
    for x in nodes_rec: kindcount[x['kind']] = kindcount.get(x['kind'], 0) + 1
    print('\n'.join(out), flush=True)
    print('== %s recon [T %d/%d] ==  kinds=%s holes: row0=%d rowA=%d at %d nodes; mismatches=%d' % (
        boxname, tally, N, kindcount, stats['hole0'], stats['holea'],
        len(stats['hole_nodes']), stats['mismatch']), flush=True)

    # ---------- dumps ----------
    with open(os.path.join(HERE, 'm4fix_tree_%s.jsonl' % boxname), 'w') as f:
        for x in nodes_rec:
            rec = dict(id=x['id'], parent=x['parent'],
                       step=(x['step'][0], fr(x['step'][1]), fr(x['step'][2])) if x['step'] else None,
                       depth=x['depth'], kind=x['kind'], a=x['a'] + 1, Aex=fr(x['Aex']),
                       P=fr(x['P']), U=tab(x['U']))
            if 'children' in x: rec['children'] = x['children']
            if x['kind'] == 'reach': rec['pmax'] = fr(x['pmax'])
            f.write(json.dumps(rec) + '\n')
    # forest summary for the generator: roots in creation order, lean-rank seen sets
    forest = dict(box=list(t7), nstart=res['nstart'],
                  roots=[x['id'] for x in nodes_rec if x['parent'] is None],
                  nodes=[dict(id=x['id'], parent=x['parent'], kind=x['kind'],
                              step=x['step'], depth=x['depth'],
                              a=x['a'] + 1, Aex=fr(x['Aex']), P=fr(x['P']),
                              children=x.get('children', []),
                              seen=sorted((r + 1, fr(B)) for (r, B) in
                                          reconstruct_seen(x, nodes_rec)))
                          for x in nodes_rec])
    with open(os.path.join(HERE, 'm4fix_forest_%s.json' % boxname), 'w') as f:
        json.dump(forest, f, indent=1)
    root_nodes = [x for x in nodes_rec if x['parent'] is None]
    ri = 0
    rr = []
    for r in roots:
        d = dict(e=r['e'], A0=fr(r['A0']), B0=fr(r['B0']), kind=r['kind'])
        if r['kind'] == 'root':
            nd = root_nodes[ri]; ri += 1
            d.update(P1=fr(r['P1']), a=nd['a'], Aex=fr(nd['Aex']), U=tab(nd['U']),
                     node_id=nd['id'])
        rr.append(d)
    with open(os.path.join(HERE, 'm4fix_roots_%s.json' % boxname), 'w') as f:
        json.dump(dict(box=list(t7), nstart=res['nstart'], roots=rr), f, indent=1)
    print('dumped tree (%d nodes) + forest + roots' % len(nodes_rec), flush=True)
    return 0 if tally == N else 1

if __name__ == '__main__':
    sys.exit(main())
