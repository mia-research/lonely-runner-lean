# v3_march_self_v1 -- SELF-ANCHORED survivor-class march census (the family E887 opened, 2026-11-21).
#
# Copy of the validated instrument v3_march_census_v2.py with the BASE ROWS changed for the
# self-anchored type family, plus ONE non-search fix (row logging; see below).  The search loop
# (stack, extension rows, irredundancy, lap pruning, cover test, rejection recording) is v2
# VERBATIM; only run()'s base-row block, the hinge constants, two extra counters and the CLI differ.
#
# Type family (strip m, self-anchored): the anchor zone is rho_7's OWN lap-m zone containing the
# window start x = 1 of W_0 = [1,7]:  entry (8m-1)u_6 <= 1 (closed-zone entry) and exit (8m+1)u_6 > 1
# <=>  u_6 in (1/(8m+1), 1/(8m-1)]  <=>  rho_7 in [8m-1, 8m+1)  -- the strip C_m = (8m-1, 8m+1).
# Base rows (v2's front rho_4 rows and v2's survivor window rows apex/floor/entry are DROPPED):
#   sorted (base_system) + rho_6 > 17 strict (idx5) + rho_7 >= 25 (idx6; subsumed by the strip for
#   m >= 4, kept for region parity) + strip rows u_6 <= 1/(8m-1) (NON-strict, entry side) and
#   u_6 > 1/(8m+1) (strict, exit side).  B = 8m+1 exact (auto): the strip pins rho_7 < 8m+1 and the
#   weak order caps every reading at rho_7 < 8m+1 <= B, so B cuts nothing.
# Hinge: has_hinge = (0, 6, m) in chain -- words containing the anchor zone (6, m).  cover_words
#   counts hinge-words reaching a 7-covering exit ((8j+1) u_y > 7, strict row, at any extension);
#   cover_words_any counts ALL words reaching one (the per-m question is existential over the strip).
#   The march-limited reach of zone (6, j) is (8j+1)/(8m-1) (sup over the strip, from the single row
#   u_6 <= 1/(8m-1)); a 7-covering exit needs j >= 7m (strict cover row; the non-strict threshold
#   ceil((7(8m-1)-1)/8) = 7m-1).  jmax_seen = largest lap pushed in any word (cover or stack).
#
# Logging fix (the one non-base-row change; see v3_march_census_findings_v1.md sec. 5): rows are
# appended to Sys.log only when add() SUCCEEDS.  v2 logged the row before the feasibility verdict,
# so every recorded 'irred' certificate was a loop artifact (the relaxation re-traversed the
# infeasible row).  The search never reads log (only add()/M), so nodes / hinge_words / cover_words
# / deaths are identical to v2 semantics; only the irred certificate products become exact
# least-product killing cycles (entry/progress certificates were already exact: computed on the
# pre-add state).
#
# CLI: python3 -I v3_march_self_v1.py <m> <B|auto> <node_cap> <secs>
#   B 'auto' = 8m+1 (exact strip cap); a numeric B < 8m+1 censuses the sub-strip rho_7 <= B
#   (e.g. B=40 for m=5 = the banked v3_reach_v1_B40 slice).
import sys, time, json
from fractions import Fraction as F
sys.path.insert(0, '.')
import d0_points_only_k6_v2 as D
from d0_points_only_k6_v2 import base_system

_orig_add = D.Sys.add
def _add(self, p, q, c, strict):
    ok = _orig_add(self, p, q, c, strict)
    if ok:                                # v3 fix: log only rows that did not kill the state
        if not hasattr(self, 'log'): self.log = []
        self.log.append((p, q, F(c), strict))
    return ok
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

def run(m, B, node_cap, deadline):
    hy = 6            # hinge reading index: u_6 = 1/rho_7 (self-anchored; v2's hy-capture kept)
    hk = m            # hinge lap: the anchor zone (6, m)
    # Base rows: strip + region, NO rho_4 front, NO v2 survivor window rows (see header).
    s0 = base_system(7, B)
    assert s0.add(5, 0, F(1, 17), True)            # rho_6 > 17 (idx5), strict   [v2 region row]
    assert s0.add(6, 0, F(1, 25), False)           # rho_7 >= 25 (idx6)          [v2 region row; subsumed]
    assert s0.add(6, 0, F(1, 8*m-1), False)        # strip entry side: u_6 <= 1/(8m-1)
    assert s0.add(0, 6, F(8*m+1), True)            # strip exit side:  u_6 > 1/(8m+1)
    stack = [(s0, None, None, [])]
    nodes = 0
    deaths = []          # maximal hinge-words: (chain, [(y, j, reason, product, cyclepath)])
    hinge_words = 0
    cover_words = 0      # hinge-words reaching a 7-covering exit
    cover_words_any = 0  # ALL words reaching a 7-covering exit (the per-m existential)
    jmax_seen = 0        # largest lap pushed in any word (v3 addition; does not steer the search)
    while stack:
        if nodes >= node_cap or time.time() > deadline:
            return dict(status='CAP', nodes=nodes, hinge_words=hinge_words, cover_words=cover_words,
                        cover_words_any=cover_words_any, jmax_seen=jmax_seen, deaths=deaths[:200])
        s, cur, prev, chain = stack.pop(); nodes += 1
        has_hinge = (0, hy, hk) in chain
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
                    cover_words_any += 1
                    if j2 > jmax_seen: jmax_seen = j2
                    if has_hinge: cover_words += 1
                    extended = True
                    continue        # a covering word: count it, do not extend (redundant)
                if j2 > jmax_seen: jmax_seen = j2
                extended = True
                stack.append((t, (y, j2), (ce, cv), chain + [(0, y, j2)]))
        if has_hinge and not extended:
            deaths.append(([(y_, j_) for (_, y_, j_) in chain], rejections))
    return dict(status='DONE', nodes=nodes, hinge_words=hinge_words, cover_words=cover_words,
                cover_words_any=cover_words_any, jmax_seen=jmax_seen, deaths=deaths,
                strip='1/' + str(8*m+1) + ' < u_6 <= 1/' + str(8*m-1), B=str(B),
                j_carve_nonstrict=7*m-1, j_carve_strict=7*m)

if __name__ == '__main__':
    m = int(sys.argv[1])
    B = F(sys.argv[2]) if len(sys.argv) > 2 and sys.argv[2] != 'auto' else F(8*m+1)
    if B < 25: B = F(25)
    cap = int(sys.argv[3]) if len(sys.argv) > 3 else 5_000_000
    secs = int(sys.argv[4]) if len(sys.argv) > 4 else 1800
    t0 = time.time()
    r = run(m, B, cap, time.time() + secs)
    r['secs'] = round(time.time() - t0, 1)
    r['m'] = m; r['Bcap'] = str(B); r['hinge'] = [6, m]
    # summarize the killing cycles
    from collections import Counter
    cc = Counter()
    for (_, rej) in r.get('deaths', []):
        for (y, j2, why, prod, path) in rej:
            if prod is not None: cc[(why, prod)] += 1
    r['killing_cycle_top'] = [[w, p, n] for (w, p), n in cc.most_common(12)]
    r['death_count'] = len(r.get('deaths', []))
    print(json.dumps(r))
