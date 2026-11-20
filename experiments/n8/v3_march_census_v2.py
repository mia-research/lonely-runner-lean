# v3_march_census_v2 -- CORRECTION of v3_march_census_v1 (one-line fix, nothing else changed).
#
# Correction recorded 2026-11-20: in v1, run()'s extension loop `for y in range(1, 7):` REBINDS the
# function parameter y (the hinge reading index). The hinge test `has_hinge = (0, y, k) in chain`
# (v1 line 71) runs before the loop only on the first stack iteration, where chain is empty; on every
# later iteration y == 6 (the last loop value). So for hinge index y == 6 the check was accidentally
# correct (the validated k15 run (6,15,22) is unaffected), but for y in {4, 5} v1 tested
# (0, 6, k) in chain -- the WRONG hinge: hinge_words / cover_words / deaths were censuses of the
# zone-6-at-lap-k words, not of the member's hinge words. The search tree itself (stack, window rows,
# rejections) is identical in v1 and v2; only the labels change. The /tmp probes (4,13,19), (5,13,19)
# were v1 runs and are therefore mislabeled; ALL members are rerun under v2.
#
# Fix: capture the hinge index in hy before the loop; test (0, hy, k). No other change of any kind.
# Semantics unchanged: for a survivor type {anchor (rho_4,1) = reading index 3 lap 1, hinge
# (index y, lap k), cover (index y, lap j)}, the thin window (u_y in (7/(8j+1), min(33/((8k-1)*7),
# 7/(8j-1))), front rho_4 in (7, 5841/833), region rho_6 > 17 strict / rho_7 >= 25, B caps all
# readings (exact (8j+1)/7 for y=6; caller-supplied working cap, e.g. 49, for y in {4,5} -- the
# census then closes the member for rho_7 <= B), exact Fractions; every maximal hinge-word's
# per-candidate rejection is recorded with its killing cycle product (strict-row cycle with
# product <= 1 is the contradiction); cover_words counts words reaching a 7-covering exit.
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

def least_prod_path(s, src, dst):
    """least-product path src -> dst over logged rows u_p <= c u_q (relaxation on edges p->q)."""
    best = {src: (F(1), [])}
    for _ in range(9):
        ch = False
        for (p, q, c, st) in s.log:
            if p in best:
                v = best[p][0] * c
                if q not in best or v < best[q][0]:
                    best[q] = (v, best[p][1] + [(p, q, str(c))]); ch = True
        if not ch: break
    return best.get(dst)

def run(y, k, j, B, node_cap, deadline):
    hy = y            # v2 FIX: the extension loop below rebinds y; keep the hinge reading index.
    # Survivor window on the hinge reading (0-indexed y in {4,5,6}):
    #   u_y > 7/(8j+1)   (cover exit)            -- floor, non-strict row (sound relaxation)
    #   u_y <= 33/((8k-1)*7) (tree apex)         -- ceiling, strict
    #   u_y < 7/(8j-1)   (cover entry)           -- ceiling, strict (redundant when apex tighter)
    # B caps ALL readings (the search needs finite laps). For y=6 the type pins rho_7 < (8j+1)/7
    # so B := (8j+1)/7 is exact; for y in {4,5} rho_7 is only region-bounded (>= 25) and the caller
    # supplies a working cap (the census then closes the member for rho_7 <= B -- stated in output).
    s0 = base_system(7, B)
    assert s0.add(5, 0, F(1, 17), True)            # rho_6 > 17 (idx5)
    assert s0.add(6, 0, F(1, 25), False)           # rho_7 >= 25 (idx6)
    assert s0.add(3, 0, F(1, 7), True)             # rho_4 > 7 (front, strict)
    assert s0.add(0, 3, F(5841, 833), False)       # rho_4 <= 5841/833
    assert s0.add(hy, 0, F(33, (8*k-1)*7), True)   # tree apex: u_y < 33/((8k-1)*7)
    assert s0.add(0, hy, F(8*j + 1, 7), False)     # cover floor: u_y >= 7/(8j+1)
    assert s0.add(hy, 0, F(7, 8*j-1), True)        # cover entry: u_y < 7/(8j-1)
    stack = [(s0, None, None, [])]
    nodes = 0
    deaths = []          # maximal hinge-words: (chain, [(y, j, reason, product, cyclepath)])
    hinge_words = 0
    cover_words = 0
    while stack:
        if nodes >= node_cap or time.time() > deadline:
            return dict(status='CAP', nodes=nodes, hinge_words=hinge_words, cover_words=cover_words,
                        deaths=deaths[:200])
        s, cur, prev, chain = stack.pop(); nodes += 1
        has_hinge = (0, hy, k) in chain               # v2 FIX: was (0, y, k) with y rebound to 6.
        if has_hinge: hinge_words += 1
        ce, cv = (F(1), 0) if cur is None else (8 * cur[1] + 1, cur[0])
        M = s.M
        xmin = ce / M[0][cv][0]; xmax = ce * M[cv][0][0]
        jmax = int((7 * B + 1) // 8) + 1
        extended = False
        rejections = []
        for y in range(1, 7):
            uymin = 1 / M[0][y][0]; uymax = M[y][0][0]
            jlo = max(1, int((xmin / uymax - 1) // 8))
            jhi = min(jmax, int((xmax / uymin + 1) // 8) + 1)
            for j2 in range(jlo, jhi + 1):
                if (0, y, j2) in chain: continue
                t = s.copy()
                ok1 = t.add(y, cv, F(ce) / (8 * j2 - 1), True)
                if not ok1:
                    bp = least_prod_path(s, cv, y)
                    prod = (F(ce) / (8 * j2 - 1)) * bp[0] if bp else None
                    rejections.append((y, j2, 'entry', str(prod) if prod is not None else None,
                                       bp[1] if bp else None))
                    continue
                ok2 = t.add(cv, y, (8 * j2 + 1) / F(ce), True)
                if not ok2:
                    bp = least_prod_path(s, y, cv)
                    prod = ((8 * j2 + 1) / F(ce)) * bp[0] if bp else None
                    rejections.append((y, j2, 'progress', str(prod) if prod is not None else None,
                                       bp[1] if bp else None))
                    continue
                if prev is not None:
                    pe, pv = prev
                    if not t.add(pv, y, (8 * j2 - 1) / F(pe), True):
                        bp = least_prod_path(t, y, pv)
                        prod = ((8 * j2 - 1) / F(pe)) * bp[0] if bp else None
                        rejections.append((y, j2, 'irred', str(prod) if prod is not None else None,
                                           bp[1] if bp else None))
                        continue
                tf = t.copy()
                if tf.add(0, y, (8 * j2 + 1) / F(7), True):
                    if has_hinge: cover_words += 1
                    extended = True
                    continue        # a covering word: count it, do not extend (redundant)
                extended = True
                stack.append((t, (y, j2), (ce, cv), chain + [(0, y, j2)]))
        if has_hinge and not extended:
            deaths.append(([(y_, j_) for (_, y_, j_) in chain], rejections))
    return dict(status='DONE', nodes=nodes, hinge_words=hinge_words, cover_words=cover_words,
                deaths=deaths, window=str(F(7, 8*j+1)) + ' < u_y < ' + str(min(F(33, (8*k-1)*7), F(7, 8*j-1))), B=str(B))

if __name__ == '__main__':
    y = int(sys.argv[1]); k = int(sys.argv[2]); j = int(sys.argv[3])
    B = F(sys.argv[4]) if len(sys.argv) > 4 and sys.argv[4] != 'auto' else F(8*j + 1, 7)
    if B < 25: B = F(25)
    cap = int(sys.argv[5]) if len(sys.argv) > 5 else 3_000_000
    secs = int(sys.argv[6]) if len(sys.argv) > 6 else 1200
    t0 = time.time()
    r = run(y, k, j, B, cap, time.time() + secs)
    r['secs'] = round(time.time() - t0, 1)
    r['hinge_y'] = y; r['Bcap'] = str(B)
    # summarize the killing cycles
    from collections import Counter
    cc = Counter()
    for (_, rej) in r.get('deaths', []):
        for (y, j2, why, prod, path) in rej:
            if prod is not None: cc[(why, prod)] += 1
    r['killing_cycle_top'] = [[w, p, n] for (w, p), n in cc.most_common(12)]
    r['death_count'] = len(r.get('deaths', []))
    print(json.dumps(r))
