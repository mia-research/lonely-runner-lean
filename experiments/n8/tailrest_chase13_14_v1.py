# E838-841 continuation (R1 core, step 5c): the CAP CHASE v2 -- strips m = 6..12.
# Same exact machine as midbound_chase_v1.py (v1.out holds m=2..5: caps 511/31, 86989/3565 at
# m=2,3; strips 4,5 KILLED exhaustively).  v2 adds one more SOUND prune and parallelism:
#   OVERSHOOT PRUNE: all chain exits are increasing and the end node's exit satisfies
#   x_end < (8je+1)/V[se].lo (=: x_e_max, from the CURRENT box).  A node whose exit-min
#   (8j+1)/V[r].lo is >= x_e_max can never precede the end, nor can any later node -- dead branch.
#   (The static lap caps of v1 stand: smalls laps <= 7, rho7 laps <= 9m+1, exits < 9.)
# Ends are independent sub-runs; they are distributed over worker processes.  Every completed
# chain is judged by the exact fixpoint arbiter (binary difference constraints + boxes:
# bounds propagation complete => the box is the exact projection); feasible verdicts get
# verified witnesses; kill iff no type over all ends meets the open strip (8m-1, 8m+1).
# Exact Fractions throughout; floats steer only.
import sys, time
from fractions import Fraction as F
from multiprocessing import Pool

DIR = '/Users/trentpalelei/Desktop/Math Ex/experiments/n8/'

def imul(x, y): return (x[0] * y[0], x[1] * y[1])
def iinv(x): return (F(1) / x[1], F(1) / x[0])
def iinter(a, b): return (max(a[0], b[0]), min(a[1], b[1]))
def iempty(x): return x[0] >= x[1]
def edge_band(ju, jx): return (F(8 * jx - 1, 8 * ju + 1), F(8 * jx + 1, 8 * ju + 1))

def boxes(m, ranks, BM, leafband=None):
    n = len(ranks)
    RB = {}
    for i in range(n):
        for j in range(i + 1, n):
            a, b = ranks[i], ranks[j]
            if a == b:
                lo, hi = BM[(i, j)]
                if not (lo < 1 < hi): return None, 'selfband'
                continue
            key = (a, b)
            if key in RB: RB[key] = iinter(RB[key], BM[(i, j)])
            else: RB[key] = BM[(i, j)]
    for (a, b), rb in list(RB.items()):
        rb = (max(rb[0], F(1)), rb[1]) if a < b else (rb[0], min(rb[1], F(1)))
        if iempty(rb): return None, 'order'
        RB[(a, b)] = rb
    V = [(F(1), F(8 * m + 1)) for _ in range(6)]
    V[5] = iinter(V[5], (F(8 * m - 1), F(8 * m + 1)))
    V[4] = iinter(V[4], (F(1), F(49, 7)))          # P6
    if leafband is not None:
        V[leafband[0]] = iinter(V[leafband[0]], leafband[1])
        if iempty(V[leafband[0]]): return None, 'leafband'
    if iempty(V[5]): return None, 'strip'
    for _ in range(30):
        changed = False
        for (a, b), rb in RB.items():
            nb = iinter(V[b], imul(V[a], rb))
            if nb != V[b]:
                V[b] = nb; changed = True
                if iempty(nb): return None, 'fixpoint'
            na = iinter(V[a], imul(V[b], iinv(rb)))
            if na != V[a]:
                V[a] = na; changed = True
                if iempty(na): return None, 'fixpoint'
        if not changed: break
    if iempty(V[5]): return None, 'strip'
    return V, None

def witness(m, ranks, BM, V):
    n = len(ranks)
    for t in (F(1, 2), F(1, 4), F(3, 4), F(1, 8), F(7, 8), F(1, 16), F(15, 16)):
        vals = [V[r][0] + (V[r][1] - V[r][0]) * t for r in range(6)]
        ok = True
        for i in range(n):
            for j in range(i + 1, n):
                if ranks[i] == ranks[j]: continue
                lo, hi = BM[(i, j)]
                rat = vals[ranks[j]] / vals[ranks[i]]
                if not (lo < rat < hi): ok = False; break
            if not ok: break
        if ok:
            if all(V[r][0] < vals[r] < V[r][1] for r in range(6)): return vals
    return None

def run_end(arg):
    m, end, budget, deadline = arg
    se, je = end
    leafband = (se, (F(8 * je - 1, 7), F(8 * je + 1, 7)))
    ZONES = [(r, j) for r in range(5) for j in range(1, 8)] + \
            [(5, j) for j in range(m, 9 * m + 2)]
    st = {'end': end, 'types': 0, 'feas': 0, 'nodes': 0, 'complete': True, 'cap': F(0),
          'best': None, 'U': [F(0)] * 6, 'w': None, 'why': {}, 'basewhy': None}

    def xemax_of(V):
        return F(8 * je + 1) / V[se][0]

    def rec(path, used, BM, ranks):
        st['nodes'] += 1
        if st['nodes'] > budget or time.time() > deadline:
            st['complete'] = False; return
        cur = path[-1]; n = len(path)
        for (r, j) in ZONES:
            if (r, j) in used: continue
            if r == cur[0] and j <= cur[1]: continue
            eb = edge_band(cur[1], j)
            comps = {}
            dead_self = False
            for i in range(n):
                prev = BM[(i, n - 1)] if (i, n - 1) in BM else (F(1), F(1))
                comp = imul(prev, eb)
                comps[(i, n)] = comp
                if ranks[i] == r and not (comp[0] < 1 < comp[1]):
                    dead_self = True; break
            if dead_self:
                st['why']['selfband'] = st['why'].get('selfband', 0) + 1
                continue
            nb_m = dict(BM); nb_m.update(comps); nb_m[(n, n)] = (F(1), F(1))
            nranks = ranks + [r]
            st['types'] += 1
            V, why = boxes(m, nranks, nb_m, leafband)
            if V is None:
                st['why'][why] = st['why'].get(why, 0) + 1
                continue
            # overshoot prune (sound): exit-min of this node vs the end's exit-max
            if (r, j) != end:
                xz_min = F(8 * j + 1) / V[r][0]
                if xz_min >= xemax_of(V):
                    st['why']['overshoot'] = st['why'].get('overshoot', 0) + 1
                    continue
            npath = path + [(r, j)]
            si = iinter(V[5], (F(8 * m - 1), F(8 * m + 1)))
            if (r, j) == end:
                st['feas'] += 1
                if V[5][1] > st['cap']:
                    st['cap'] = V[5][1]; st['best'] = npath; st['V'] = V
                w = witness(m, nranks, nb_m, V)
                if w and si[0] < w[5] < si[1]: st['w'] = w
                for rr in range(6):
                    if V[rr][1] > st['U'][rr]: st['U'][rr] = V[rr][1]
                continue
            if not iempty(si):
                rec(npath, used | {(r, j)}, nb_m, nranks)
            else:
                st['why']['strip_ext'] = st['why'].get('strip_ext', 0) + 1
    BM0 = {(0, 0): (F(1), F(1))}
    V0, why0 = boxes(m, [5], BM0, leafband)
    if V0 is None:
        st['basewhy'] = why0
        return st
    # base overshoot: the anchor's own exit-min vs the end's exit-max
    x0_min = F(8 * m + 1) / V0[5][0]
    if x0_min >= xemax_of(V0) and end != (5, m):
        st['basewhy'] = 'overshoot_base'
        return st
    rec([(5, m)], {(5, m)}, BM0, [5])
    return st

def main(mlist):
    out = open(DIR + 'tailrest_chase13_14_v1.out', 'a')
    def P(*a):
        s = ' '.join(str(x) for x in a); print(s, flush=True); out.write(s + '\n'); out.flush()
    P('# tailrest chase 13-14 (re-typed verbatim from midbound_chase_v2.py, unchanged semantics; output renamed)', mlist)
    for m in mlist:
        t0 = time.time()
        ends = [(r, j) for r in range(5) for j in range(1, 8)] + \
               [(5, j) for j in range(m, 9 * m + 2)]
        ends = [e for e in ends if e != (5, m)]
        dl = time.time() + 3300
        args = [(m, e, 2000000, dl) for e in ends]
        with Pool(6) as pool:
            results = pool.map(run_end, args, chunksize=1)
        tot_t = sum(r['types'] for r in results); tot_f = sum(r['feas'] for r in results)
        tot_n = sum(r['nodes'] for r in results)
        complete = all(r['complete'] for r in results)
        strip_feas = tot_f; strip_cap = F(0); best = None
        U = [F(0)] * 6; endtally = {}; wsz = None
        for r in results:
            if r['feas']:
                if r['cap'] > strip_cap:
                    strip_cap = r['cap']; best = (r['end'], r['best'])
                for rr in range(6):
                    if r['U'][rr] > U[rr]: U[rr] = r['U'][rr]
                endtally[r['end']] = r['feas']
                if r['w'] and (wsz is None or r['w'][5] > wsz[5]): wsz = r['w']
        P('m=%d: types=%d feas_types=%d nodes=%d complete=%s | strip-feasible ends: %d' %
          (m, tot_t, tot_f, tot_n, complete, strip_feas))
        P('   KILLED: %s (vs strip lower edge %d)' % (strip_feas == 0 and complete, 8 * m - 1))
        P('   cap(m) = %s = %.5f | cap/(49/7) = %.5f vs (8m-1)/7 = %.5f' %
          (strip_cap, float(strip_cap), float(strip_cap) * 7 / 49, float(8 * m - 1) / 7))
        P('   best:', best)
        if wsz: P('   witness rho2..rho7:', [str(x) for x in wsz], [round(float(x), 4) for x in wsz])
        P('   U_r:', [str(u) for u in U], [round(float(u), 4) for u in U])
        P('   feasible end zones:', dict(sorted(endtally.items())))
        P('   elapsed', round(time.time() - t0, 1), 's')
    out.close()
    print('DONE')

if __name__ == '__main__':
    main([int(x) for x in sys.argv[1:]] or [13, 14])
