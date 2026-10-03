# sigpair_cell_v1 -- per-cell decision of the 7 closer ranks for the cell's opener rank.
# status per closer rank c (0-based index; rank c+1), best over all leaves (signatures) of the cell:
#   FE   exact Fraction arrangement in the cell's path class, verified with outcome() (path equal, opener rank, closer rank)
#   FO   exact Fraction arrangement with the right (opener, closer) ranks but a different exact path
#   FD   LP (slack > TOL) feasible for the full path system, rounding certificate failed
#   TB   open region empty (t<=TOL) but with entry-ties allowed against higher ranks the slack is > TOL (tie locus, lower rank wins)
#   TIE  closure nonempty but needs equal readings (distinctness rows nonstrict give slack > TOL)
#   TOUCH closure nonempty, best t in [-TOL, TOL], not explained by the above
#   INF  every branch LP-infeasible (t < -TOL), or no leaf
#   BUDGET DFS node budget exhausted before a certificate
import sys, pickle, time
from fractions import Fraction as F
sys.path.insert(0, '.')
from sigpair_lib_v1 import *
_src = open('outcome_classes_v2.py').read().split('\nif __name__ ==')[0]
exec(_src)

ORDER = ['FE', 'FO', 'FD', 'TB', 'TIE', 'TOUCH', 'BUDGET', 'INF']
class Done(Exception): pass

def certify(cell, c, x, dens=(10**12, 10**10, 10**8)):
    for d in dens:
        rho = [F(1)] + [F(float(v)).limit_denominator(d) for v in x[1:]]
        if any(rho[i] >= rho[i + 1] for i in range(6)) or rho[6] > cell.W: continue
        o = outcome(rho)
        if o['opener'] and o['opener'][0] == cell.s[cell.m] + 1 and o['closer'][0] == c + 1:
            return rho, o
    return None

def certify_exact(cell, c, rho):
    if rho is None or any(rho[i] >= rho[i + 1] for i in range(6)) or rho[6] > cell.W: return None
    o = outcome(rho)
    if o['opener'] and o['opener'][0] == cell.s[cell.m] + 1 and o['closer'][0] == c + 1: return rho, o
    return None

def decide_cell(path, box, J, node_budget=20000, skip=()):
    cell = Cell(path, box, J); S = setup(cell); m = cell.m
    status = {c: 'INF' for c in range(7)}; tbest = {c: None for c in range(7)}; cert = {}; xtb = {}
    stats = {'nodes': 0, 'final_leaves': 0, 'over': 0}
    def upd(c, st):
        if ORDER.index(st) < ORDER.index(status[c]): status[c] = st
    fin, inter = decisions(cell)
    def on_final(laps, t, x):
        stats['final_leaves'] += 1
        for c in range(7):
            if status[c] == 'FE' or c in skip: continue
            mk = S.mark(); add_closer(S, laps, c); r = S.solve()
            if r is not None and (tbest[c] is None or r[0] > tbest[c]): tbest[c] = r[0]
            if r is not None and r[0] > TOL:
                found = {}
                def on_full(laps2, t2, x2):
                    if t2 > TOL:
                        found['x'] = x2; found['ex'] = polish(S); found['full'] = interior_exact(S); return True
                    cr_ = certify_exact(cell, c, polish(S))
                    if cr_ is not None and cr_[1]['path'] == tuple(path): found['x'] = x2; found['ex'] = cr_[0]; found['thin'] = True; return True
                    found['touch'] = True; return False
                lv, nd, over, stopped = dfs(cell, S, inter, laps, on_full, node_budget)
                stats['nodes'] += nd
                if stopped:
                    cr = None
                    fl = found.get('full')
                    if fl is not None and fl[0] is not None:
                        cr = certify_exact(cell, c, fl[0])
                        if cr is not None and cr[1]['path'] != tuple(path): cr = None
                    if cr is None: cr = certify_exact(cell, c, found.get('ex'))
                    if cr is None or cr[1]['path'] != tuple(path): cr2 = certify(cell, c, found['x']); cr = cr2 if (cr2 is not None and (cr is None or cr2[1]['path'] == tuple(path))) else cr
                    if cr is not None and cr[1]['path'] == tuple(path): upd(c, 'FE'); cert[c] = cr
                    elif cr is not None: upd(c, 'FO'); cert.setdefault(c, cr)
                    else: upd(c, 'FD')
                elif over: stats['over'] += 1; upd(c, 'BUDGET') if status[c] == 'INF' else None
                elif found.get('touch'): upd(c, 'TOUCH')
            elif r is not None and r[0] >= -TOL:
                cr_ = certify_exact(cell, c, polish(S))
                if cr_ is not None and cr_[1]['path'] == tuple(path): upd(c, 'FE'); cert[c] = cr_; S.rollback(mk); continue
                r3 = S.solve_ignore_order()
                upd(c, 'TIE' if (r3 is not None and r3[0] > TOL) else 'TOUCH')
            S.rollback(mk)
        if all(status[c] == 'FE' for c in range(7)): return True
        return False
    laps0 = {cell.s[m]: cell.j[m]}
    lv, nd, over, stopped = dfs(cell, S, fin, laps0, on_final, node_budget)
    stats['nodes'] += nd
    if over:
        for c in range(7):
            if status[c] in ('INF', 'TOUCH', 'TIE', 'TB'): status[c] = 'BUDGET'
    return dict(path=tuple(path), opener=cell.s[m] + 1, status=status, t=tbest, xtb=xtb, nlp=S.nlp, leaves=stats['final_leaves'], nodes=stats['nodes'],
                cert={c: (tuple(map(str, v[0])), v[1]['path']) for c, v in cert.items()})

if __name__ == '__main__':
    J = int(sys.argv[1]); a = int(sys.argv[2]); b = int(sys.argv[3])
    T = pickle.load(open(f'terminals5_J{J}.pkl', 'rb')); M = dict(pickle.load(open(f'cell_members_J{J}.pkl', 'rb')))
    t0 = time.time()
    for i in range(a, b):
        p, lo, hi, box, w = T[i]
        r = decide_cell(p, box, J)
        mem = outcome(M[i]) if i in M else None
        print(i, p[-1], ''.join(r['status'][c][0:2].ljust(3) for c in range(7)), 'member', None if mem is None else (mem['opener'][0], mem['closer'][0]), 'nlp', r['nlp'], 'leaves', r['leaves'], flush=True)
    print('time', time.time() - t0)
