# joinedge2_perbox_v1.py -- dump v2: DOMINATION WITNESSES for the joinedge death rows
# (the joinedge_perbox_v1.jsonl known limit: derived-only deaths' killing caps are the word's
# own accumulated products, recorded as values without their walks; the DumpDom data-side
# predicate of Fresh/CapChainsOfCarve.lean wants each cap VALUE paired with its dominating
# U-table entry, plus the path decomposition z_1..z_k of composed walks, E813 item 7).
#
# Reruns the one-sided enumeration VERBATIM (joinedge_perbox_v1.py's machinery: exec of
# j2_cycle_v2.py's pre-main, v1's classify_box / w1_kill_families_pb) with a PARALLEL
# provenance-tracking table machinery: every table entry carries its exact decomposition
# into primitive bounds -- hop = (u, v, value, strict, tag), tags:
#   ('box', kind, ranks...)   the box opening bounds of mk(n): face_hi (2n+1)/2 (rho_y/rho_0),
#                             face_lo 2/(2n-1) (rho_0/rho_y), one (rho_0/rho_y < 1), ord
#                             (rho_y/rho_{y+1} < 1);
#   ('J', i, j)               the W0-chain join entry added into UJ (dominated by EVERY
#                             chain's closed-trace entry, the join being the entrywise max);
#   ('word', kind, rl...)     the W1 word's own bounds along the DFS walk: start1 9/(8l-1),
#                             start2 (8l+1)/9, seam1 (8a+1)/(8b-1), seam2 Ax/Aex, end Aex/15
#                             -- the (rank, numerator) pairs recorded;
#   ('chain', kind, rl...)    the W0 chain's own raw bounds (controls' c-raw caps): start
#                             1/(8l-1), start_exit Ax, seamE, seamM, end Aex/7.
# The value/strict semantics of addp/mkp/gtp are VERBATIM the plain ones (asserted per box:
# plain vs provenance death Counters identical; chain tables and U0 identical).
#
# Per death row (kind, x1, y1, P, Q) and killing cap C/D the dump records the DOMINATION
# WITNESS: the cap's provenance walk y -> z_1 -> ... -> x (0-based Fin 7 indices, the
# ChainReal shape: caps_real = [(z_1, c_1), ..., (z_k = x, c_k)], exact product == cap), each
# hop tagged with its class and its DOMINATING TABLE ENTRY:
#   dom_box = the box-closure U0 entry at the hop pair if its value <= hop value (box-side
#             route, capChainsRealized_of_boxDom consumes these);
#   dom_J   = the join entry at the hop pair if J <= hop value (then EVERY chain's trace
#             entry <= J <= hop, the chain-side route of capChainsRealized_of_chainDom).
# Witness completeness: STRICT (DumpDom as stated) = every hop dom_box or dom_J; else
# CHAIN-ATTAINED = some enumerated chain's trace dominates every hop (the per-chain
# disjunctive form the banked c-raw families actually need -- the banked caps sit strictly
# below the join, so they are dominated only by their attaining chains); else INCOMPLETE
# (undominated word hops listed).
#
# Controls (the 5 two-sided boxes): j2_cycle_v12 five_box rerun verbatim; each banked
# spineFamData c-raw row (BANKED_CRAW) is matched to its attaining chains and its witness is
# recorded from the provenance chain tables [T 5/5 required].
#
# NEW files only (joinedge2_perbox_v1.py/.jsonl/.out); nothing existing is modified.
# Exact Fractions throughout; floats nowhere.  Nothing committed.
import os, sys, time, json, re, bisect
from fractions import Fraction as F
from collections import Counter, defaultdict

N8 = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.chdir(N8)  # the machinery opens its files by relative name (same cwd as the original runs)
AUD = os.path.join(N8, 'onefast_audit')

t00 = time.time()
src = open('j2_cycle_v2.py').read()
exec(src.split("\nif __name__ == '__main__':")[0])
from fractions import Fraction as Fraction

# ---- v1's own functions (verbatim), for the regression run and the family blocks ----
V1FILE = os.path.join(AUD, 'joinedge_perbox_v1.py')
src1 = open(V1FILE).read()
_g = globals(); _g['__file__'] = V1FILE
exec(src1.split("\nif __name__ == '__main__':")[0], _g)  # join_tables, pm1, FIVE, V6_OUT,
                                                         # w1_kill_families_pb, chainside_cands,
                                                         # classify_box  (verbatim v1)

# ================= provenance-tracking machinery (value-verbatim add/mk/gt) =================
# table entry: (value, strict, hops) with hops = tuple of primitive hop tuples
# hop = (u, v, value, strict, tag)

def addp(U, i, j, c, s, hop):
    # verbatim j2_g1sweep_v1.add value semantics; hops updated exactly when the entry updates
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
            if w is None or v < w[0] or (v == w[0] and st and not w[1]):
                V[p][q] = (v, st, a[2] + (hop,) + b[2])
    return V

def mkp(n):
    U = [[(F(1), False, ()) if i == j else None for j in range(7)] for i in range(7)]
    for y in range(1, 7):
        U = addp(U, y, 0, F(2 * n[y] + 1, 2), False, (y, 0, F(2 * n[y] + 1, 2), False, ('box', 'face_hi', y + 1)))
        if U is None: return None
        U = addp(U, 0, y, F(2, 2 * n[y] - 1), False, (0, y, F(2, 2 * n[y] - 1), False, ('box', 'face_lo', y + 1)))
        if U is None: return None
        U = addp(U, 0, y, F(1), True, (0, y, F(1), True, ('box', 'one', y + 1)))
        if U is None: return None
    for y in range(1, 6):
        U = addp(U, y, y + 1, F(1), True, (y, y + 1, F(1), True, ('box', 'ord', y + 1, y + 2)))
        if U is None: return None
    return U

def gtp(U, A, a, B, b, tag):
    # verbatim gt
    if A > 0 and B <= 0: return U
    if A <= 0 and B > 0: return None
    if A == 0: return U if B < 0 else None
    if B == 0: return U if A > 0 else None
    if A > 0: return addp(U, a, b, F(A, B), True, tag)   # rho_a / rho_b < A/B
    return addp(U, b, a, F(-B, -A), True, tag)           # |A|/rho_a < |B|/rho_b

def w0chainsp(n, dl=None):
    # verbatim w0chains (j2_cycle_v2), with hop tags on every primitive add
    U0 = mkp(n); Z = zones(n); out = []
    def rec(U, a, Aex, seen, w):
        if dl and time.time() > dl: raise Budget
        W = addp(U, a, 0, F(Aex, 7), True, (a, 0, F(Aex, 7), True, ('chain', 'end', a + 1, Aex, 1, 7)))
        if W is not None: out.append((W, w))
        for b, Bn, Ax in Z:
            if (b, Ax) in seen: continue
            V = gtp(U, Aex, a, Bn, b, (a, b, F(Aex, Bn), True, ('chain', 'seamE', a + 1, Aex, b + 1, Bn)))
            if V is None: continue
            V = gtp(V, Ax, b, Aex, a, (b, a, F(Ax, Aex), True, ('chain', 'seamM', b + 1, Ax, a + 1, Aex)))
            if V is None: continue
            rec(V, b, Ax, seen | {(b, Ax)}, w + [(b, Bn, Ax)])
    for y, Bn, Ax in Z:
        V = addp(U0, 0, y, F(1, Bn), True, (0, y, F(1, Bn), True, ('chain', 'start', 1, 1, y + 1, Bn)))
        if V is None: continue
        V = addp(V, y, 0, F(Ax), True, (y, 0, F(Ax), True, ('chain', 'start_exit', y + 1, Ax, 1, 1)))
        if V is None: continue
        rec(V, y, Ax, {(y, Ax)}, [(y, Bn, Ax)])
    return out

def strip(T):
    return [[None if e is None else (e[0], e[1]) for e in row] for row in T]

# ---- the provenance one-sided DFS: verbatim w1_kill_families_pb + witness recording ----
def w1_kill_families2_pb(n, J, dl):
    U0 = mkp(n); Z = []
    for y in range(1, 7):
        hi = n[y] + F(1, 2)
        j = 1
        while 8 * j - 1 < 15 * hi + 2:
            Z.append((y, 8 * j - 1, 8 * j + 1)); j += 1
    UJ = [r[:] for r in U0]
    for i in range(7):
        for j in range(7):
            if i != j and J[i][j] is not None:
                UJ = addp(UJ, i, j, J[i][j][0], J[i][j][1], (i, j, J[i][j][0], J[i][j][1], ('J', i, j)))
                if UJ is None: return None, None, None, None
    U0s = strip(U0)  # plain-value U0 for attr (verbatim)
    deaths = Counter(); comp = [0]
    wit = defaultdict(set)  # (kind, x1, y1, P, Q, cap, strict) -> {hops tuple}
    def attr(j, i, back):
        if U0s[j][i] is not None and U0s[j][i][0] == back[0]: return 'box'
        if J[j][i] is not None and J[j][i][0] == back[0]: return 'J'
        return 'derived'
    def step(i, j, P, Q, kind, U, tag):
        c = F(P, Q)
        back = U[j][i]
        if back is not None:
            p = back[0] * c
            if p < 1 or p == 1:
                if i != j:
                    deaths[(kind, i + 1, j + 1, str(back[0]), bool(back[1]), attr(j, i, back), P, Q)] += 1
                    wit[(kind, i + 1, j + 1, P, Q, str(back[0]), bool(back[1]))].add(back[2])
                return None
        return addp(U, i, j, c, True, tag)
    def rec(U, a, Aex, seen):
        if time.time() > dl: raise Budget
        W = step(a, 0, Aex, 15, 'end', U, (a, 0, F(Aex, 15), True, ('word', 'end', a + 1, Aex, 1, 15)))
        if W is not None: comp[0] += 1; return
        for b, Bn, Ax in Z:
            if (b, Ax) in seen: continue
            V = step(a, b, Aex, Bn, 'seam1', U, (a, b, F(Aex, Bn), True, ('word', 'seam1', a + 1, Aex, b + 1, Bn)))
            if V is None: continue
            V = step(b, a, Ax, Aex, 'seam2', V, (b, a, F(Ax, Aex), True, ('word', 'seam2', b + 1, Ax, a + 1, Aex)))
            if V is None: continue
            rec(V, b, Ax, seen | {(b, Ax)})
    for y, Bn, Ax in Z:
        V = step(0, y, 9, Bn, 'start1', UJ, (0, y, F(9, Bn), True, ('word', 'start1', 1, 9, y + 1, Bn)))
        if V is None: continue
        V = step(y, 0, Ax, 9, 'start2', V, (y, 0, F(Ax, 9), True, ('word', 'start2', y + 1, Ax, 1, 9)))
        if V is None: continue
        rec(V, y, Ax, {(y, Ax)})
    return deaths, comp[0], wit, U0

# ================= witness processing =================
def lap_of(num):
    if num == 1: return 0
    if num % 8 == 1: return (num - 1) // 8
    if num % 8 == 7: return (num + 1) // 8
    return None

def hop_json(h, U0v, Jv):
    u, v, val, st, tag = h
    d = {'u': u, 'v': v, 'rank_u': u + 1, 'rank_v': v + 1, 'value': str(val), 'strict': bool(st)}
    cls = tag[0]; d['class'] = cls
    if cls == 'box':
        d['kind'] = tag[1]
        d['ranks'] = [tag[2]] if len(tag) == 3 else [tag[2], tag[3]]
        d['form'] = {'face_hi': '(2n+1)/2', 'face_lo': '2/(2n-1)', 'one': '1', 'ord': '1'}[tag[1]]
    elif cls == 'J':
        d['pair0'] = [tag[1], tag[2]]; d['form'] = 'join-entry'
    else:
        d['kind'] = tag[1]
        d['rl'] = [[tag[k], tag[k + 1]] for k in range(2, len(tag), 2)]  # (rank, numerator) pairs
        d['lap'] = [lap_of(t[1]) for t in d['rl']]
        d['form'] = 'seam(8a+/-1)/(8b-/+1)'
    e = U0v[u][v]
    d['dom_box'] = [u, v, str(e[0]), bool(e[1])] if (e is not None and e[0] <= val) else None
    e = Jv[u][v]
    d['dom_J'] = [u, v, str(e[0]), bool(e[1])] if (e is not None and e[0] <= val) else None
    d['dominated_strict'] = bool(d['dom_box'] or d['dom_J'])
    return d

class PairIndex:
    # per-pair sorted chain values (min side) for domination counts and attaining-chain sets
    def __init__(self, chain_tabs):
        self.vals = {}; self.cis = {}
        for u in range(7):
            for v in range(7):
                arr = []
                for ci, T in enumerate(chain_tabs):
                    e = T[u][v]
                    if e is not None: arr.append((e[0], ci))
                arr.sort(key=lambda t: t[0])
                self.vals[(u, v)] = [t[0] for t in arr]
                self.cis[(u, v)] = [t[1] for t in arr]
    def count_le(self, u, v, cap):
        return bisect.bisect_right(self.vals[(u, v)], cap)
    def chains_le(self, u, v, cap):
        k = bisect.bisect_right(self.vals[(u, v)], cap)
        return self.cis[(u, v)][:k]

def witness_json(capv, strict, hops, P, Q, x1, y1, U0v, Jv, pidx, want_att=False):
    prod = F(1)
    nodes = []
    for h in hops:
        prod *= h[2]
        nodes.append(h[0])
    if hops: nodes.append(hops[-1][1])
    exact = (prod == capv)
    endok = bool(nodes) and nodes[0] == y1 - 1 and nodes[-1] == x1 - 1
    flagok = (any(h[3] for h in hops) == strict) if hops else (strict == False)
    hj = [hop_json(h, U0v, Jv) for h in hops]
    strict_ok = all(h['dominated_strict'] for h in hj)
    undom = [[h['u'], h['v'], h['value']] for h in hj if not h['dominated_strict']]
    cls_cnt = Counter(h['class'] for h in hj)
    wj = {'cap': str(capv), 'strict': bool(strict), 'y': y1 - 1, 'x': x1 - 1,
          'nodes': nodes, 'caps_real': [[h['v'], h['value']] for h in hj],
          'n_hops': len(hops),
          'product_exact': bool(exact), 'endpoints_ok': bool(endok), 'flag_or_ok': bool(flagok),
          'datum_ok': bool(F(P, Q) * capv <= 1),
          'hops': hj, 'hop_classes': dict(cls_cnt),
          'complete_strict': bool(strict_ok and exact and endok and flagok),
          'attaining_chains': None, 'attaining_chain_sample': None, 'att_computed': False,
          'undominated_hops': undom}
    if want_att: compute_att(wj, hops, pidx)
    return wj

def compute_att(wj, hops, pidx):
    # the per-chain disjunctive datum: chains whose closed-trace entry dominates EVERY hop
    if wj['complete_strict'] or not hops:
        wj['att_computed'] = True; wj['attaining_chains'] = 0
        return
    cands = []
    for h in hops:
        cs = pidx.chains_le(h[0], h[1], h[2])
        if not cs:
            wj['att_computed'] = True; wj['attaining_chains'] = 0
            return
        cands.append(cs)
    cands.sort(key=len)
    S = set(cands[0])
    for cs in cands[1:]:
        S &= set(cs)
        if not S: break
    wj['att_computed'] = True
    wj['attaining_chains'] = len(S)
    wj['attaining_chain_sample'] = min(S) if S else None

# ================= controls: banked c-raw rows with provenance =================
def banked_witnesses(n, rawk, Cs, Csp, J, U0v, pidx):
    out = []
    for (kind, x1, y1, cap, dem), cnt in BANKED_CRAW[n].items():
        cv = F(cap); A, B = F(dem).numerator, F(dem).denominator
        C, D = cv.numerator, cv.denominator
        y, x = y1 - 1, x1 - 1
        atts = [ci for ci, (T, w) in enumerate(Cs) if T[y][x] is not None and T[y][x][0] == cv]
        rec = {'kind': kind, 'x1': x1, 'y1': y1, 'demand': dem, 'cap': cap, 'count': cnt,
               'in_rawk': (kind, x1, y1, 'c-raw', cap, dem) in rawk,
               'AC_le_BD': bool(A * C <= B * D), 'A_mod8': A % 8, 'C_mod8': C % 8,
               'attaining_chains': len(atts),
               'all_chains_dom': bool(all(T[y][x] is not None and T[y][x][0] <= cv for (T, w) in Cs)),
               'dom_box_at_pair': bool(U0v[y][x] is not None and U0v[y][x][0] <= cv),
               'join_at_pair': str(J[y][x][0]) if J[y][x] is not None else None,
               'witnesses': []}
        for ci in atts[:4]:
            e = Csp[ci][0][y][x]
            wj = witness_json(cv, bool(e[1]), e[2], A, B, x1, y1, U0v, J, pidx, want_att=True)
            wj['chain'] = ci
            wj['word'] = ['%d/%d/%d' % t for t in Cs[ci][1]]
            rec['witnesses'].append(wj)
        out.append(rec)
    return out

# ================= main =================
def main():
    only = None
    if len(sys.argv) > 1: only = set(eval(sys.argv[1]))  # optional list of box tuples to run
    boxes = []
    for l in open('j2_g1sweep_class_v1.out'):
        m = re.match(r'\s*\((\d+, [\d, ]+)\) w0n=(\d+)', l)
        if m: boxes.append(((1,) + eval('(' + m.group(1) + ')'), int(m.group(2))))
    if only is not None: boxes = [bw for bw in boxes if bw[0] in only]
    print('joinedge2_perbox_v1: %d boxes (%d one-sided + %d two-sided controls)' %
          (len(boxes), sum(1 for n, _ in boxes if n not in FIVE), sum(1 for n, _ in boxes if n in FIVE)), flush=True)
    v1recs = {}
    for l in open(os.path.join(AUD, 'joinedge_perbox_v1.jsonl')):
        r = json.loads(l); v1recs[tuple(r['box'])] = r
    # controls machinery once (j2_cycle_v12 pre-main: PK, five_box, raw_edges_of_w1, ...)
    src12 = open('j2_cycle_v12.py').read()
    exec(src12.split("\nif __name__ == '__main__':")[0], globals())
    jp = open(os.path.join(AUD, 'joinedge2_perbox_v1.jsonl'), 'w')
    G = Counter(); Gv = Counter()
    for bi, (n, w0n) in enumerate(boxes):
        t0 = time.time()
        # ---- plain v1 run (regression + family block) ----
        try:
            rec1, Cs, J, U0v = classify_box(n, w0n, 240, 600)
        except Budget:
            rec1, Cs, J, U0v = classify_box(n, w0n, 480, 1200)
        deaths_plain, comp_plain, _, _ = w1_kill_families_pb(n, J, time.time() + 900)
        # ---- provenance chains (assert value-equality) ----
        Csp = w0chainsp(n)
        chains_eq = (len(Csp) == len(Cs) and all(strip(Tp) == T for (Tp, wp), (T, w) in zip(Csp, Cs)))
        chain_tabs = [T for (T, w) in Cs]
        # jprov: first attaining chain per join entry + join-domination check
        jprov = {}; join_dom_ok = True
        for i in range(7):
            for j in range(7):
                if i != j and J[i][j] is not None:
                    jv = J[i][j][0]; att = None
                    for ci, T in enumerate(chain_tabs):
                        e = T[i][j]
                        if e is not None:
                            if e[0] > jv: join_dom_ok = False
                            if att is None and e[0] == jv: att = ci
                    jprov[(i, j)] = att
                    if att is None: join_dom_ok = False
        # ---- provenance DFS ----
        try:
            deaths2, comp2, wit, U0p = w1_kill_families2_pb(n, J, time.time() + 900)
        except Budget:
            deaths2, comp2, wit, U0p = w1_kill_families2_pb(n, J, time.time() + 2400)
        deaths_eq = (deaths2 == deaths_plain) and (comp2 == comp_plain)
        U0_eq = (strip(U0p) == U0v)
        # v1-record regression
        v1 = v1recs[n]; f1 = v1['family']; f2 = rec1['family']
        v1_eq = all(f1[k] == f2[k] for k in f1) and v1['deaths_total'] == rec1['deaths_total'] \
            and v1['completions'] == rec1['completions'] and v1['deaths_by_attr'] == rec1['deaths_by_attr'] \
            and v1['jside_bounds'] == rec1['jside_bounds'] and v1['edges'] == rec1['edges']
        # ---- witness processing ----
        pidx = PairIndex(chain_tabs)
        wmap = {}   # (cap, hops, P, Q, x1, y1) -> id
        wjson = {}  # id -> witness json
        # rows: (kind,x1,y1,P,Q) -> (cap,strict) -> [attrCounter, witness-hop sets]
        rows = defaultdict(dict)
        for (kind, x1, y1, P, Q, cap, strict), hset in wit.items():
            cm = rows[(kind, x1, y1, P, Q)]
            if (cap, strict) not in cm: cm[(cap, strict)] = [Counter(), set()]
            cm[(cap, strict)][1] |= hset
        for (kind, x1, y1, cap, strict, at, P, Q), cnt in deaths2.items():
            cm = rows[(kind, x1, y1, P, Q)]
            if (cap, strict) not in cm: cm[(cap, strict)] = [Counter(), set()]
            cm[(cap, strict)][0][at] += cnt
        rows_out = []
        exact = [0, 0]; dat = [0, 0]; end = [0, 0]; flg = [0, 0]
        caps_total = caps_strict = caps_att = caps_inc = 0
        der_caps = der_strict = 0; row_complete = 0
        dcls = Counter(); dcls_der = Counter()
        lenhist = Counter()
        for (kind, x1, y1, P, Q), capmap in sorted(rows.items()):
            caps_out = []; row_strict = False
            for (cap, strict), (atcnt, hset) in sorted(capmap.items(), key=lambda kv: str(kv[0])):
                cv = F(cap); dcount = sum(atcnt.values())
                at = 'box' if atcnt.get('box') else ('J' if atcnt.get('J') else 'derived')
                # light witnesses (no att), ranked strict-first then shortest
                wjs = []
                for h in hset:
                    key = (cv, h, P, Q, x1, y1)
                    wi = wmap.get(key)
                    if wi is None:
                        wi = len(wmap); wmap[key] = wi
                    wj = witness_json(cv, strict, h, P, Q, x1, y1, U0v, J, pidx, want_att=False)
                    wjs.append((wj, wi, h))
                wjs.sort(key=lambda t: (0 if t[0]['complete_strict'] else 1, t[0]['n_hops'], t[1]))
                # early-stop att: only until one attained found (never needed for strict primaries)
                if wjs and not wjs[0][0]['complete_strict']:
                    for (wj, wi, h) in wjs:
                        if wj['complete_strict']: break
                        if wj['att_computed']:
                            if (wj['attaining_chains'] or 0) > 0: break
                            continue
                        compute_att(wj, h, pidx)
                        if (wj['attaining_chains'] or 0) > 0: break
                wjs.sort(key=lambda t: (0 if t[0]['complete_strict'] else
                                        (1 if (t[0]['attaining_chains'] or 0) > 0 else 2),
                                        t[0]['n_hops'], t[1]))
                caps_total += 1
                prim = wjs[0][0]
                if prim['complete_strict']:
                    caps_strict += 1; row_strict = True
                    dcls['strict'] += dcount; dcls_der['strict'] += dcount if at == 'derived' else 0
                    if at == 'derived': der_strict += 1
                elif (prim['attaining_chains'] or 0) > 0:
                    caps_att += 1
                    dcls['attained'] += dcount; dcls_der['attained'] += dcount if at == 'derived' else 0
                else:
                    caps_inc += 1
                    dcls['incomplete'] += dcount; dcls_der['incomplete'] += dcount if at == 'derived' else 0
                if at == 'derived': der_caps += 1
                lenhist[prim['n_hops']] += 1
                exact[0] += prim['product_exact']; exact[1] += 1
                dat[0] += prim['datum_ok']; dat[1] += 1
                end[0] += prim['endpoints_ok']; end[1] += 1
                flg[0] += prim['flag_or_ok']; flg[1] += 1
                for (wj, wi, h) in wjs[:2]:
                    if wi not in wjson: wjson[wi] = wj
                caps_out.append({'cap': cap, 'strict': strict, 'attr': at, 'deaths': dcount,
                                 'attr_counts': dict(atcnt),
                                 'conflict': bool(cv * F(P, Q) <= 1),
                                 'AC': int(P * cv.numerator), 'BD': int(Q * cv.denominator),
                                 'witness': wjs[0][1], 'witness_distinct': len(wjs),
                                 'witness_alt': [t[1] for t in wjs[1:2]],
                                 'complete_strict': prim['complete_strict'],
                                 'attaining_chains': prim['attaining_chains']})
            row_complete += row_strict
            rows_out.append({'kind': kind, 'x1': x1, 'y1': y1, 'P': P, 'Q': Q,
                             'deaths': sum(sum(c[0].values()) for c in capmap.values()),
                             'A': F(P, Q).numerator, 'B': F(P, Q).denominator,
                             'A_mod8': F(P, Q).numerator % 8, 'B_mod8': F(P, Q).denominator % 8,
                             'row_strict_complete': row_strict, 'caps': caps_out})
        wout = {str(wi): wjson[wi] for wi in sorted(wjson)}
        # ---- controls: banked c-raw rows ----
        ctrl = None
        if n in FIVE:
            try:
                rawk, compc, unres = five_box(n, sample=220 if n == (1, 2, 3, 4, 5, 6, 7) else None)
            except Budget:
                rawk, compc, unres = five_box(n, sample=220 if n == (1, 2, 3, 4, 5, 6, 7) else None)
            ctrl = banked_witnesses(n, rawk, Cs, Csp, J, U0v, pidx)
        bcensus = {'death_rows': len(rows_out), 'row_caps': caps_total,
                   'deaths_total': sum(dcls.values()),
                   'caps_strict_complete': caps_strict, 'caps_chain_attained': caps_att,
                   'caps_incomplete': caps_inc, 'derived_caps': der_caps,
                   'derived_strict_complete': der_strict, 'rows_strict_complete': row_complete,
                   'deaths_by_class': dict(dcls), 'derived_deaths_by_class': dict(dcls_der),
                   'walk_len_hist': {str(k): v for k, v in sorted(lenhist.items())}}
        rec = {'box': list(n), 'w0n': w0n, 'role': rec1['role'], 'chains_enumerated': len(Cs),
               'regression': {'v6_matches': rec1['matches_v6_out'], 'v1_record_matches': v1_eq,
                              'prov_chains_eq': chains_eq, 'prov_deaths_eq_plain': deaths_eq,
                              'prov_U0_eq': U0_eq, 'join_domination_all_chains': join_dom_ok},
               'family': f2,
               'U0_entries': [[i, j, str(U0v[i][j][0]), bool(U0v[i][j][1])]
                              for i in range(7) for j in range(7) if U0v[i][j] is not None],
               'jprov': {'%d,%d' % k: v for k, v in jprov.items()},
               'witnesses': wout, 'death_rows': rows_out,
               'checks': {'witness_exact': exact, 'datum': dat, 'endpoints': end, 'flag_or': flg},
               'census': bcensus, 'banked_control': ctrl}
        jp.write(json.dumps(rec, separators=(',', ':')) + '\n')
        G['rows'] += bcensus['death_rows']; G['caps'] += caps_total
        G['strict'] += caps_strict; G['att'] += caps_att; G['inc'] += caps_inc
        G['der'] += der_caps; G['ders'] += der_strict; G['rowsc'] += row_complete
        for k in ('strict', 'attained', 'incomplete'):
            G['D_' + k] += dcls[k]; G['DD_' + k] += dcls_der[k]
        Gv['ex'] += exact[0]; Gv['exN'] += exact[1]
        Gv['dat'] += dat[0]; Gv['datN'] += dat[1]
        Gv['end'] += end[0]; Gv['endN'] += end[1]
        Gv['flg'] += flg[0]; Gv['flgN'] += flg[1]
        print(n, rec1['role'], 'rows', bcensus['death_rows'], 'caps', caps_total,
              'strict', caps_strict, 'attained', caps_att, 'incomplete', caps_inc,
              '| derived', der_caps, 'der_strict', der_strict, '| rows_complete', row_complete,
              '| deaths s/a/i', dcls['strict'], dcls['attained'], dcls['incomplete'],
              '| reg v6', rec1['matches_v6_out'], 'v1', v1_eq, 'prov', deaths_eq, chains_eq, U0_eq,
              'exact %d/%d' % (exact[0], exact[1]),
              'time', round(time.time() - t0, 1), flush=True)
    jp.close()
    print('=== dump v2 written; rows', G['rows'], 'caps', G['caps'],
          '| strict-complete', G['strict'], 'chain-attained', G['att'], 'incomplete', G['inc'],
          '| derived-only caps', G['der'], 'of which strict-complete', G['ders'],
          '| rows with a strict-complete cap', G['rowsc'], flush=True)
    print('DEATHS by class: strict', G['D_strict'], 'attained', G['D_attained'],
          'incomplete', G['D_incomplete'], 'total', G['D_strict'] + G['D_attained'] + G['D_incomplete'], flush=True)
    print('DERIVED-attr DEATHS by class: strict', G['DD_strict'], 'attained', G['DD_attained'],
          'incomplete', G['DD_incomplete'], flush=True)
    print('VALIDITY: exact %d/%d  datum %d/%d  endpoints %d/%d  flagOR %d/%d' %
          (Gv['ex'], Gv['exN'], Gv['dat'], Gv['datN'], Gv['end'], Gv['endN'], Gv['flg'], Gv['flgN']), flush=True)
    print('TOTAL TIME', round(time.time() - t00, 1), flush=True)

if __name__ == '__main__':
    main()
