# v3_reach_v1 -- the reach of a W_0 chain on the V3 region (E819's quantity): for every chain state of the exact search
# (v3_growth_profile_v2 logic: 1<=rho2<=..<=rho7<=B, rho6>17, rho7>=25, one window [1,7], strict mode),
# sup over the real readings satisfying the chain's rows of the chain's LAST EXIT (8j+1)/rho_y = (8j+1)*sup(u_y), u_0 = 1.
# reach(B) = max over all chain states.  No carve  <=>  reach(B) <= 7 (a carve needs the last exit to pass 7).
# Also: the best words, and the binding least-product path of rows (Bellman-Ford over the logged raw rows, exact Fractions).
# [PROVISIONAL: covering] claim named: reach <= 7 is no cover of [1,7] by the open zones, no carve of W_0.
import sys, time, json
from fractions import Fraction as F
sys.path.insert(0, '.')
import d0_points_only_k6_v2 as D
from d0_points_only_k6_v2 import base_system

_orig_add = D.Sys.add
def _add(self, p, q, c, strict):
    if not hasattr(self, 'log'): self.log = []
    self.log.append((p, q, F(c), strict))
    return _orig_add(self, p, q, c, strict)
_orig_copy = D.Sys.copy
def _copy(self):
    s = _orig_copy(self); s.log = list(getattr(self, 'log', [])); return s
D.Sys.add = _add; D.Sys.copy = _copy

def binding_path(s, y):
    """least-product path y -> ... -> 0 over the logged rows u_p <= c u_q; returns (product, [(p,q,c,strict)...])."""
    k = s.k; best = {y: (F(1), [])}
    for _ in range(k + 1):
        ch = False
        for (p, q, c, st) in s.log:
            if p in best:
                v = best[p][0] * c
                if q not in best or v < best[q][0]:
                    best[q] = (v, best[p][1] + [(p, q, str(c), st)]); ch = True
        if not ch: break
    return best.get(0)

def run(B, rho6lo, rho7lo, deadline, nread=7, h=F(1), windows=[(F(1), F(7))], top=6):
    B = F(B)
    s0 = base_system(nread, B)
    assert s0.add(nread-2, 0, 1/F(rho6lo), True)
    assert s0.add(nread-1, 0, 1/F(rho7lo), False)
    stack = [(s0, 0, None, None, [])]
    nodes = 0; covers = 0; best = []   # (sup exit, chain)
    while stack:
        if time.time() > deadline: return dict(B=str(B), status='CAP', nodes=nodes, covers=covers)
        s, wi, cur, prev, chain = stack.pop(); nodes += 1
        lo, hi = windows[wi]
        ce, cv = (lo, 0) if cur is None else (8*cur[1]+h, cur[0])
        M = s.M
        xmin = ce / M[0][cv][0]; xmax = ce * M[cv][0][0]
        jmax = int((hi*B + h)//8) + 1
        for y in range(1, nread):
            uymin = 1 / M[0][y][0]; uymax = M[y][0][0]
            jlo = max(1, int((xmin/uymax - h)//8)); jhi = min(jmax, int((xmax/uymin + h)//8) + 1)
            for j in range(jlo, jhi+1):
                if (wi, y, j) in chain: continue
                t = s.copy()
                if not t.add(y, cv, F(ce)/(8*j-h), True): continue
                if not t.add(cv, y, (8*j+h)/F(ce), True): continue
                if prev is not None:
                    pe, pv = prev
                    if not t.add(pv, y, (8*j-h)/F(pe), True): continue
                sup_exit = (8*j+h) * t.M[y][0][0]
                nc = chain + [(wi, y, j)]
                best.append((sup_exit, nc, t)); best.sort(key=lambda z: -z[0]); best = best[:top]
                tf = t.copy()
                if tf.add(0, y, (8*j+h)/hi, True): covers += 1; continue
                stack.append((t, wi, (y, j), (ce, cv), nc))
    out = []
    for sup_exit, nc, t in best:
        y = nc[-1][1]
        bp = binding_path(t, y)
        out.append(dict(sup_exit=str(sup_exit), word=[(y_, j_) for (_, y_, j_) in nc], depth=len(nc),
                        path_product=(str(bp[0]) if bp else None), path=(bp[1] if bp else None)))
    return dict(B=str(B), status='DONE', nodes=nodes, covers=covers, best=out)

if __name__ == "__main__":
    B = sys.argv[1]; secs = int(sys.argv[2]); t0 = time.time()
    r = run(B, 17, 25, time.time() + secs); r['secs'] = round(time.time() - t0, 1)
    print(json.dumps(r))
