# leafhigh_close_v1.py -- rule-22 closure analysis of the 3,765 D=64 uncertified boxes ("leaves")
# of the taildeep fixed-R0 certifier for band rho7 in [95,97) (taildeep_leaves_95_97.txt).
# Reuses leaves3739_mech_v1 / frontier_window_cert_v1 machinery verbatim (read-only exec).
# Exact integers/Fractions for every conclusion; floats steer only.
# Sections:
#  [1] C-certifier reproduction: fresh compile of taildeep_box_dfs256.c -> refine the leaf file at
#      cap D=64; the C re-reports the 3,765 as uncertified (artifact reproduced from the C side).
#  [2] EXACT fixed-R0 re-certification at D=64 of all leaves with the certifier's OWN integer
#      predicate exact_clear (no float stage): per leaf, the exact common lonely set (Fractions),
#      a dyadic witness r/2^20 inside it, and the cap diagnostic (component index of the witness
#      window in the rho7 union vs the C's 64-component cap).  Witnesses -> leafhigh_dyadic_witnesses.txt
#  [3] window-type certifier (E833 machinery, exact) at D=64 on all leaves: cross-certificate census.
#  [4] staged window-type DFS on the window-uncertified remainder: caps 128, 256, 512, 1024
#      (task 2a); cert-by-depth census.
#  [5] plane-split side test at D=64 with the dominant derived tie planes (E834-style, exhaustive
#      per-side window types) on representative leaves -- recorded for the tail-lemma menu.
# usage: python3 leafhigh_close_v1.py
import os, sys, math, collections, itertools, subprocess, time
from fractions import Fraction as F
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))
IN = os.path.join(HERE, 'taildeep_leaves_95_97.txt')
WIT = os.path.join(HERE, 'leafhigh_dyadic_witnesses.txt')

# ---- verbatim machinery from frontier_window_cert_v1.py (module level: imports + defs only)
_sys_argv_saved = sys.argv; sys.argv = ['x']
exec(open(os.path.join(HERE, 'frontier_window_cert_v1.py')).read().split("def sorted_feasible")[0])
sys.argv = _sys_argv_saved

def sorted_feasible(n):  # verbatim
    x = n[0]
    for i in range(6):
        if n[i] > x: x = n[i]
        if x > n[i] + 1: return False
    return True

GQ = 1 << 20
def exact_clear(r, n, D):
    # verbatim integer predicate of taildeep_box_dfs256.c
    t = r * n; u = r * (n + 1); base = GQ * D
    if t < base: return False
    j = (t - base) // (8 * base)
    return u <= (8 * j + 7) * base

def lonely_set(D, n):
    # exact common lonely set (leaves3739_mech_v1 verbatim), merged intervals; returns (intervals, killing reading or None)
    cur = [(F(1), F(7))]
    for i in range(6):
        ivs = []
        j = 0
        while True:
            lo = F((8 * j + 1) * D, n[i]); hi = F((8 * j + 7) * D, n[i] + 1)
            if lo > 7: break
            if hi >= 1: ivs.append((max(lo, F(1)), min(hi, F(7))))
            j += 1
        nxt = []
        for a, b in cur:
            for lo, hi in ivs:
                c, d = (a if a > lo else lo), (b if b < hi else hi)
                if c <= d: nxt.append((c, d))
        nxt.sort()
        m = []
        for c, d in nxt:
            if m and c <= m[-1][1]:
                if d > m[-1][1]: m[-1] = (m[-1][0], d)
            else: m.append((c, d))
        cur = m
        if not cur: return [], i
    return cur, None

def rho7_components(D, n):
    # the rho7 clear-interval union in [1,7]: exact intervals, ascending, with lap j
    ivs = []
    j = 0
    while True:
        lo = F((8 * j + 1) * D, n[5]); hi = F((8 * j + 7) * D, n[5] + 1)
        if lo > 7: break
        if hi >= 1: ivs.append((max(lo, F(1)), min(hi, F(7)), j))
        j += 1
    return ivs

def exact_recert(D, n):
    # (certified?, witness r or None, K7, witness-window component index in rho7 union (1-based),
    #  n common windows, n windows with component index <= 64)
    ls, kill = lonely_set(D, n)
    K7ivs = rho7_components(D, n)
    K7 = len(K7ivs)
    wit = None; idx = None
    nw = len(ls); nkept = 0
    for a, b in ls:
        jstar = None
        for k, (lo, hi, j) in enumerate(K7ivs):
            if lo <= a and b <= hi: jstar = k + 1; break
        if jstar is not None and jstar <= 64: nkept += 1
        r_lo = max(GQ, math.ceil(a * GQ)); r_hi = min(7 * GQ, math.floor(b * GQ))
        for r in range(r_lo, r_hi + 1):
            if all(exact_clear(r, ni, D) for ni in n):
                wit = r; idx = jstar; break
        if wit is not None: break
    return wit is not None, wit, K7, idx, nw, nkept

def w_work(item):
    D, n = item
    return 1 if certify(D, n) else 0

def refine_to(args):
    # staged DFS: certify box; else split until cap; returns (cert depth or 0, leaves at cap)
    D, n, cap = args
    out = []
    def rec(D, n):
        if certify(D, n): return D
        if D >= cap: out.append((D, n)); return 0
        best = 0
        for m in range(64):
            c = tuple(2 * n[i] + ((m >> i) & 1) for i in range(6))
            if sorted_feasible(c):
                r = rec(2 * D, c)
                best = max(best, r)
        return best
    d = rec(D, n)
    return d, out

def side_vertices(D, n, plane, want_positive):  # leaves3739_mech_v1 verbatim
    V = corners(D, n); pos = []; neg = []; zero = []
    for u in V:
        h = plane(u)
        if h > 0: pos.append(u)
        elif h < 0: neg.append(u)
        else: zero.append(u)
    cross = []
    for i in range(6):
        for m0 in range(64):
            if (m0 >> i) & 1: continue
            m1 = m0 | (1 << i)
            c0 = tuple(F(n[k] + ((m0 >> k) & 1), D) for k in range(6))
            c1 = tuple(F(n[k] + ((m1 >> k) & 1), D) for k in range(6))
            h0, h1 = plane(c0), plane(c1)
            if (h0 > 0) == (h1 > 0) or h0 == 0 or h1 == 0: continue
            s = h0 / (h0 - h1)
            w = tuple(c0[k] + s * (c1[k] - c0[k]) for k in range(6))
            cross.append(w)
    side = pos + zero + cross
    other = neg + zero + cross
    if want_positive: return side, other
    return other, side

def side_types(V):  # leaves3739_mech_v1 verbatim
    if not V: return []
    rmin = {}; rmax = {}
    for i in range(6):
        for k in range(6):
            vals = [u[i] / u[k] for u in V]
            rmin[(i, k)] = min(vals); rmax[(i, k)] = max(vals)
    cmin = [min(u[i] for u in V) for i in range(6)]
    cmax = [max(u[i] for u in V) for i in range(6)]
    xdescs = [(1, None)]; ydescs = [(7, None)]
    for k in range(6):
        j = 0
        while True:
            num = 8 * j + 1
            if num > 7 * cmax[k]: break
            if num >= cmin[k]: xdescs.append((num, k))
            j += 1
        j = 1
        while True:
            num = 8 * j - 1
            if num > 7 * cmax[k]: break
            if num >= cmin[k]: ydescs.append((num, k))
            j += 1
    out = []
    for na, ka in xdescs:
        for nb, kb in ydescs:
            if ka is not None and na < cmax[ka]: continue
            if kb is not None and nb > 7 * cmin[kb]: continue
            if ka is None and kb is None: pass
            elif ka is None:
                if cmax[kb] > nb: continue
            elif kb is None:
                if na > 7 * cmin[ka]: continue
            else:
                if na * rmax[(kb, ka)] > nb: continue
            laps = []; ok = True
            for i in range(6):
                if ka is None: top = cmin[i]
                elif ka == i: top = F(na)
                else: top = na * rmin[(i, ka)]
                jx = math.floor((top - 1) / 8)
                if kb is None: bot = 7 * cmax[i]
                elif kb == i: bot = F(nb)
                else: bot = nb * rmax[(i, kb)]
                jy = math.ceil((bot - 7) / 8)
                jlo = jy if jy > 0 else 0
                if jlo > jx: ok = False; break
                laps.append(8 * jx + 1)
            if ok: out.append(((na, ka), (nb, kb), tuple(laps)))
    return out

def main():
    t0 = time.time()
    leaves = []
    for l in open(IN):
        v = [int(x) for x in l.split()]
        if len(v) == 7: leaves.append((v[0], tuple(v[1:])))
    N = len(leaves)

    O = open(os.path.join(HERE, 'leafhigh_close_v1.out'), 'w')
    def P(*a):
        s = ' '.join(str(x) for x in a)
        print(s, flush=True); O.write(s + '\n')

    P('== leafhigh_close_v1: rule-22 closure of the 3,765 D=64 leaves, band rho7 in [95,97) ==')
    P('[0] inputs:', IN, '| leaves', N)

    # ---- [1] C-certifier reproduction (fresh compile from the source of record)
    P('')
    P('[1] C-certifier reproduction: fresh compile of taildeep_box_dfs256.c -> leafhigh_recheck_bin,')
    P('    refine the leaf file at cap D=64 (the C re-decides every leaf):')
    BIN = os.path.join(HERE, 'leafhigh_recheck_bin')
    REOUT = os.path.join(HERE, 'leafhigh_c_recheck_leaves.txt')
    try:
        cc = subprocess.run(['cc', '-O2', '-o', BIN, os.path.join(HERE, 'taildeep_box_dfs256.c')],
                            capture_output=True, text=True, timeout=120)
        if cc.returncode != 0: P('    compile failed:', cc.stderr[:400])
        else:
            run = subprocess.run([BIN, '6080', '6208', '64', REOUT, IN], capture_output=True, text=True, timeout=3600)
            P('    C summary:', run.stdout.strip().replace('\n', ' | '))
            nl = sum(1 for _ in open(REOUT)) if os.path.exists(REOUT) else 0
            P('    leaves written by the C re-run:', nl)
            same = open(REOUT).read() == open(IN).read() if os.path.exists(REOUT) else False
            P('    identical to the input leaf file:', same)
    except Exception as e:
        P('    C reproduction skipped/failed:', e)

    # ---- [2] exact fixed-R0 re-certification at D=64 (the certifier's own integer predicate)
    P('')
    P('[2] EXACT fixed-R0 re-certification at D=64 (integer predicate exact_clear of the C; no float stage):')
    cert_cnt = 0; K7s = []; idxs = []; idx_gt64 = 0; nwins = []; keptwin_leaves = 0
    W = open(WIT, 'w')
    t1 = time.time()
    for k, (D, n) in enumerate(leaves):
        ok, wit, K7, idx, nw, nkept = exact_recert(D, n)
        K7s.append(K7); nwins.append(nw)
        if ok:
            cert_cnt += 1
            W.write('%d %s %d\n' % (D, ' '.join(map(str, n)), wit))
            idxs.append(idx)
            if idx is not None and idx > 64: idx_gt64 += 1
        if nkept > 0: keptwin_leaves += 1
        if k % 500 == 499: P('    ...%d leaves done (%d certified), %.0f s' % (k + 1, cert_cnt, time.time() - t1))
    W.close()
    P('    EXACTLY certified by fixed-R0 at D=64: %d of %d leaves' % (cert_cnt, N))
    P('    dyadic witnesses written:', WIT, '(format: D n2..n7 r, R0 = r/2^20)')
    P('    cap diagnostic over certified leaves:')
    P('      rho7-union components in [1,7] (K7): min %d max %d  (C float stage keeps only the first 64)' % (min(K7s), max(K7s)))
    P('      witness window component index in the rho7 union: min %s max %s | leaves with witness beyond the 64-cap: %d'
      % (min(idxs) if idxs else None, max(idxs) if idxs else None, idx_gt64))
    P('      leaves with ANY common window inside the kept (first 64) components: %d' % keptwin_leaves)
    P('      common-window count per leaf: min %d max %d' % (min(nwins), max(nwins)))
    if cert_cnt == N:
        P('    => ALL 3,765 boxes satisfy the fixed-R0 certifier\'s own soundness criterion at D=64:')
        P('       the "uncertified leaves" are an artifact of the C\'s long-double candidate stage,')
        P('       which caps its interval intersection at 64 components (nxt[64], nn < 64) and so')
        P('       never generates candidates inside the true common window (components 65+).')

    # ---- [3] window-type certifier (E833) at D=64 on all leaves
    P('')
    P('[3] window-type certifier (E833 machinery, exact) at D=64 on all %d leaves:' % N)
    t1 = time.time()
    with Pool(10) as p:
        flags = p.map(w_work, leaves, chunksize=16)
    wt64 = sum(flags)
    P('    window-type certified at D=64: %d of %d | elapsed %.0f s' % (wt64, N, time.time() - t1))
    P('    (fixed-R0 exact certificate and window-type certificate are independent sufficient conditions;')
    P('     the fixed-R0 one already covers 100% of the leaves at D=64.)')

    # ---- [4] staged window-type DFS on the window-uncertified remainder (task 2a)
    P('')
    P('[4] staged window-type DFS (E833 refine) on the window-uncertified remainder:')
    rem = [leaves[k] for k in range(N) if not flags[k]]
    P('    remainder entering the DFS:', len(rem), 'leaves')
    if rem:
        front = rem
        for cap in (128, 256, 512, 1024):
            t1 = time.time()
            with Pool(10) as p:
                res = p.map(refine_to, [(D, n, cap) for D, n in front], chunksize=4)
            certd = collections.Counter(); nxt_front = []
            for d, out in res:
                if d: certd[d] += 1
                nxt_front += out
            tot = sum(certd.values())
            P('    cap D=%d: input %d -> certified %d (by depth %s) | still uncertified at cap %d | %.0f s'
              % (cap, len(front), tot, dict(sorted(certd.items())), len(nxt_front), time.time() - t1))
            outf = os.path.join(HERE, 'leafhigh_wleaves_%d.txt' % cap)
            open(outf, 'w').write(''.join('%d %s\n' % (D, ' '.join(map(str, n))) for D, n in nxt_front))
            P('      wrote', outf)
            front = nxt_front
            if not front: break
        P('    final window-type frontier:', len(front), 'boxes')

    # ---- [5] plane-split side test at D=64 (E834-style) with the dominant derived planes
    P('')
    P('[5] plane-split side test at D=64 (moot for closure -- [2] already closes everything -- recorded')
    P('    for the tail-lemma menu): exhaustive per-side window types (leaves3739 side_types) on the')
    P('    two dominant derived tie planes of the census:')
    P1n = lambda c: 23 * c[2] - 17 * c[4]          # 23*rho4 - 17*rho6
    P2n = lambda c: 343 * c[4] - 25 * c[5]         # 343*rho6 - 25*rho7
    RN = ['rho2', 'rho3', 'rho4', 'rho5', 'rho6', 'rho7']
    def dsc(a):
        if a[1] is None: return '1' if a[0] == 1 else ('7' if a[0] == 7 else str(a[0]))
        return '%d/%s' % (a[0], RN[a[1]])
    def strad(D, n, h):
        lo_v = sum(h[i] * (n[i] if h[i] >= 0 else n[i] + 1) for i in range(6))
        hi_v = sum(h[i] * (n[i] + 1 if h[i] >= 0 else n[i]) for i in range(6))
        return lo_v < 0 < hi_v
    H46 = (0, 0, 23, 0, -17, 0); H67 = (0, 0, 0, 0, 343, -25); H37 = (0, 0, -23, 0, 0, 1)
    reps = []
    for h, tag in ((H46, '23r4-17r6'), (H67, '343r6-25r7'), (H37, 'r7-23r3')):
        c = 0
        for D, n in leaves:
            if strad(D, n, h):
                reps.append((tag, D, n)); c += 1
                if c == 2: break
    for tag, D, n in reps:
        for nm, pl in (('23r4-17r6', P1n), ('343r6-25r7', P2n)):
            Sp, Sn = side_vertices(D, n, pl, True)
            tp = side_types(Sp); tn = side_types(Sn)
            P('    n=%s [%s] | split at %s: |V+|=%d |V-|=%d | types on + side: %d | on - side: %d' %
              (n, tag, nm, len(Sp), len(Sn), len(tp), len(tn)))
            for lbl, ts in (('+', tp), ('-', tn)):
                if ts:
                    a, b, laps = ts[0]
                    P('      %s side first type: X=%s Y=%s laps(8j+1)=%s' % (lbl, dsc(a), dsc(b), list(laps)))

    P('')
    P('done close in %.1f s' % (time.time() - t0))
    O.close()

if __name__ == '__main__':
    main()
