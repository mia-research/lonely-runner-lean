# schema_sweep_v1.py -- the G1 two-stage box certificate sweep parametrized over the order k.
#
# Lineage: experiments/n8/j2_g1sweep_v1.py (order 8; E810/E812/G1 machinery, mk/add/gt verbatim from
# j2_nchain_v1.py).  This file generalizes 8 -> k everywhere:
#   threshold 1/k; readings rho_1 = 1 < rho_2 < ... < rho_{k-1}; windows W_m = [km+1, km+k-1];
#   J-region rho_{k-1} <= 2k+1; nearest-integer tuples (n_2..n_{k-1}) non-decreasing in [1, 2k+1]
#   (count C(3k-2, k-2); at k=8: C(22,6) = 74613); zone edges (kj +- 1)/rho; anchors k' = 1 mod k.
#   Stage 1: W_0 = [1, k-1] admission (monotone zone chain).  Stage 2: the c(1) = W_1 = [k+1, 2k-1]
#   joint (standard comb at integer shift t=1), with E812 join pruning.
# A joint hit means real readings in the box carve both W_0 and W_1, so the cascade lands at or past
# 2k+1.  Every hit is rule-22 verified (exact witness, both carve forms, exact cascade replay).
#
# VALIDATION PROTOCOL (owner, 2026-11-07: lower orders first): k = 8 must reproduce the G1 result
# bit-for-bit (74540 none / 73 chain / 0 joint) before k <= 7 results are trusted.  At k <= 7
# existence is proved (native Lean proofs, other tree); any joint hit there is a bug or a discovery.
#
# usage: python3 schema_sweep_v1.py k [workers] [b1] [b2] [--priority-only]
import sys, os, time, json, itertools, random
from fractions import Fraction as F
from math import floor
from multiprocessing import Pool

HERE = os.path.dirname(os.path.abspath(__file__))

# ---------- order parameters (globals set in main) ----------
K = 8                    # order
NR = K - 1               # readings rho_1..rho_{K-1}; table size NR x NR
W0 = (1, K - 1)          # window W_0
W1 = (K + 1, 2 * K - 1)  # window W_1
NMAX = 2 * K + 1         # J-region top reading bound; tuple values in [1, 2K+1]
CKPT = None              # set in main

# ---------- core table machinery: verbatim from j2_nchain_v1.py (E810), sizes generalized ----------
INF = None
def mk(n):
    U = [[(F(1), False) if i == j else INF for j in range(NR)] for i in range(NR)]
    for y in range(1, NR):
        U = add(U, y, 0, F(2 * n[y] + 1, 2), False)
        if U is None: return None
        U = add(U, 0, y, F(2, 2 * n[y] - 1), False)
        if U is None: return None
        U = add(U, 0, y, F(1), True)
        if U is None: return None
    for y in range(1, NR - 1):
        U = add(U, y, y + 1, F(1), True)
        if U is None: return None
    return U
def add(U, i, j, c, s):
    # rho_i / rho_j < c (strict s) or <= c
    cur = U[i][j]
    if cur is not None and (cur[0] < c or (cur[0] == c and (cur[1] or not s))): return U
    back = U[j][i]
    if back is not None:
        pr = back[0] * c
        if pr < 1 or (pr == 1 and (s or back[1])): return None
    V = [row[:] for row in U]
    for p in range(NR):
        a = U[p][i]
        if a is None: continue
        for q in range(NR):
            b = U[j][q]
            if b is None: continue
            v = a[0] * c * b[0]; st = a[1] or s or b[1]
            w = V[p][q]
            if w is None or v < w[0] or (v == w[0] and st and not w[1]): V[p][q] = (v, st)
    return V
def gt(U, A, a, B, b):
    # A/rho_a > B/rho_b
    if A > 0 and B <= 0: return U
    if A <= 0 and B > 0: return None
    if A == 0: return U if B < 0 else None
    if B == 0: return U if A > 0 else None
    if A > 0: return add(U, a, b, F(A, B), True)       # rho_a / rho_b < A/B
    return add(U, b, a, F(-B, -A), True)               # |A|/rho_a < |B|/rho_b
class Budget(Exception): pass

# ---------- stage 1: W_0 admission (v1.w0 verbatim, window generalized) ----------
def w0zones(n):
    Zs = []
    for y in range(1, NR):
        for j in range(1, int(((K - 1) * (n[y] + 1)) // K) + 2):
            Zs.append((y, K * j - 1, K * j + 1))
    return Zs
def w0w(U, n, deadline):
    # W_0 chain search on table U: monotone zones (kj-1, kj+1)/rho covering [1, K-1]
    Zs = w0zones(n)
    def rec(U, a, Aex, seen, word):
        if time.time() > deadline: raise Budget
        W = add(U, a, 0, F(Aex, K - 1), True)
        if W is not None: return W, word
        for b, Bn, Ax in Zs:
            if (b, Ax) in seen: continue
            V = gt(U, Aex, a, Bn, b)
            if V is None: continue
            V = gt(V, Ax, b, Aex, a)
            if V is None: continue
            R = rec(V, b, Ax, seen | {(b, Ax)}, word + [(b, Ax)])
            if R is not None: return R
        return None
    for y, Bn, Ax in Zs:
        V = add(U, 0, y, F(1, Bn), True)      # entry Bn/rho_y < 1
        if V is None: continue
        V = add(V, y, 0, F(Ax), True)         # exit Ax/rho_y > 1
        if V is None: continue
        R = rec(V, y, Ax, {(y, Ax)}, [(y, Ax)])
        if R is not None: return R
    return None

# ---------- stage 2: W_1 / c(1) chains (window [K+1, 2K-1], standard comb) ----------
def w1zones(n):
    # generous, sound both ways (v1.w1zones shape): jlo = max(1, ((K+1)(n_y-1))//K),
    # jhi = ((2K-1)(n_y+1) + 2K)//K
    Zs = []
    for y in range(1, NR):
        jlo = max(1, int(((K + 1) * (n[y] - 1)) // K))
        jhi = int(((2 * K - 1) * (n[y] + 1) + 2 * K) // K)
        for j in range(jlo, jhi + 1): Zs.append((y, K * j - 1, K * j + 1))
    return Zs
def w1(U0, n, deadline, visit):
    # enumerate monotone standard-comb zone chains covering [K+1, 2K-1] on table U0
    Zs = w1zones(n)
    def rec(U, a, Aex, seen, word):
        if time.time() > deadline: raise Budget
        W = add(U, a, 0, F(Aex, 2 * K - 1), True)    # exit Aex/rho_a > 2K-1: chain complete
        if W is not None:
            if visit(W, word + [(a, Aex)]): return True
        for b, Bn, Ax in Zs:
            if (b, Ax) in seen: continue
            V = gt(U, Aex, a, Bn, b)
            if V is None: continue
            V = gt(V, Ax, b, Aex, a)
            if V is None: continue
            if rec(V, b, Ax, seen | {(b, Ax)}, word + [(b, Ax)]): return True
        return False
    for y, Bn, Ax in Zs:
        V = add(U0, 0, y, F(K + 1, Bn), True)     # entry Bn/rho_y < K+1
        if V is None: continue
        V = add(V, y, 0, F(Ax, K + 1), True)      # exit Ax/rho_y > K+1 (covers the left end)
        if V is None: continue
        if rec(V, y, Ax, {(y, Ax)}, []): return 'joint'
    return 'exhausted'

# ---------- exact replay + witness verification ----------
def chain_on(U, kind, word):
    # replay a chain word [(rank0, Ax), ...] on table U; kind 'w0' -> W0, 'w1' -> W1
    LO, HI = (W0 if kind == 'w0' else W1)
    a, Aex = word[0]; Bn = Aex - 2
    U = add(U, 0, a, F(LO, Bn), True)
    U = None if U is None else add(U, a, 0, F(Aex, LO), True)
    for (b, Ax) in word[1:]:
        Bn = Ax - 2
        U = None if U is None else gt(U, Aex, a, Bn, b)
        U = None if U is None else gt(U, Ax, b, Aex, a)
        a, Aex = b, Ax
    U = None if U is None else add(U, a, 0, F(Aex, HI), True)
    return U
def chain_table(n, kind, word):
    return chain_on(mk(n), kind, word)
def point(U):
    # exact witness readings from a feasible table (midpoint fractions first, then a rational grid)
    r = [F(1)] + [None] * (NR - 1)
    for y in range(1, NR):
        lo = 1 / U[0][y][0]; hi = U[y][0][0]
        for q in (F(1, 2), F(1, 4), F(3, 4), F(1, 8), F(7, 8), F(1, 16), F(15, 16), F(1, 64), F(63, 64), F(1, 1024), F(1023, 1024)):
            m = lo + q * (hi - lo)
            U2 = add(U, y, 0, m, False)
            U2 = add(U2, 0, y, 1 / m, False) if U2 is not None else None
            if U2 is not None:
                U = U2; r[y] = m; break
        else:
            return None
    return r
def sg(r): return [f if f < F(1, 2) else f - 1 for f in [x - floor(x) for x in r]]
def covered(r, g, t):
    # verbatim shape from j2_rot_scan_v1.py: is [1, K-1] carved by c(t) zones at readings r, phases g?
    z = []
    for y in range(1, NR):
        x = r[y]; d = K * t * g[y]; j0 = floor((x + d - 1) / K); j = j0
        while True:
            a = (K * j - 1 - d) / x
            if a >= K - 1: break
            b = (K * j + 1 - d) / x
            if b > 1: z.append((a, b, y, j))
            j += 1
    z.sort(); cur = F(1); chain = []
    for a, b, y, j in z:
        if a >= cur: return False, chain, cur
        if b > cur: cur = b; chain.append((y, j))
        if cur > K - 1: return True, chain, cur
    return (cur > K - 1), chain, cur
def covered_w(r):
    # independent form: standard comb on [K+1, 2K-1] directly (must agree with covered(...,t=1))
    z = []
    for y in range(1, NR):
        x = r[y]
        for j in range(1, 64):
            a = F(K * j - 1) / x
            if a >= 2 * K - 1: break
            b = F(K * j + 1) / x
            if b > K + 1: z.append((a, b, y, j))
    z.sort(); cur = F(K + 1); ch = []
    for a, b, y, j in z:
        if a >= cur: return False, ch, cur
        if b > cur: cur = b; ch.append((y, j))
        if cur > 2 * K - 1: return True, ch, cur
    return (cur > 2 * K - 1), ch, cur
def pos(R, rho): return (R * rho) % K
def blocks(R, rho):
    p = pos(R, rho); return min(p, K - p) < 1
def cascade(rhos, cap=4000):
    # exact cascade, verbatim semantics of cascade_path_map_v1.py::path
    R = F(1); steps = []
    while True:
        bl = [i for i, r in enumerate(rhos) if blocks(R, r)]
        if not bl: return steps, R
        if len(steps) >= cap: return steps, None
        ex = [((K * round(R * rhos[i] / K) + 1) / rhos[i], i, round(R * rhos[i] / K)) for i in bl]
        R2, setter, lap = max(ex)
        steps.append(dict(R=R, setter=setter, lap=lap, R2=R2)); R = R2
def verify_witness(n, w1word, w0word):
    # rule-22 verification of a joint hit; words 0-based [(rank, Ax), ...]; None on failure
    T = chain_table(n, 'w1', w1word)
    T = None if T is None else chain_on(T, 'w0', w0word)
    if T is None: return None
    r = point(T)
    if r is None: return None
    g = sg(r); gf = [x - floor(x) for x in r]
    nt = tuple(int(x - y) for x, y in zip(r, g))
    c0 = covered(r, g, F(0))[0]
    c1 = covered(r, g, F(1))[0]
    c1f = covered(r, gf, F(1))[0]
    cw = covered_w(r)[0]
    steps, landing = cascade(r)
    return dict(r=[str(x) for x in r], nt=nt, c0=c0, c1=c1, c1f=c1f, cw=cw,
                moves=len(steps), landing=str(landing) if landing is not None else 'CAP',
                land_ge_cap=(landing is not None and landing >= 2 * K + 1),
                w1word=[(a + 1, A) for a, A in w1word], w0word=[(a + 1, A) for a, A in w0word])

# ---------- E812 join of W_0 chains (verbatim join, sizes generalized) ----------
def w0chains(n, deadline):
    U0 = mk(n); Z = w0zones(n)
    out = []
    def rec(U, a, Aex, seen):
        if time.time() > deadline: raise Budget
        W = add(U, a, 0, F(Aex, K - 1), True)
        if W is not None: out.append(W)
        for b, Bn, Ax in Z:
            if (b, Ax) in seen: continue
            V = gt(U, Aex, a, Bn, b)
            if V is None: continue
            V = gt(V, Ax, b, Aex, a)
            if V is None: continue
            rec(V, b, Ax, seen | {(b, Ax)})
    for y, Bn, Ax in Z:
        V = add(U0, 0, y, F(1, Bn), True)
        if V is None: continue
        V = add(V, y, 0, F(Ax), True)
        if V is None: continue
        rec(V, y, Ax, {(y, Ax)})
    return out
def join(Ts):
    J = [r[:] for r in Ts[0]]
    for W in Ts[1:]:
        for i in range(NR):
            for j in range(NR):
                a, b = J[i][j], W[i][j]
                if a is None or b is None: J[i][j] = None
                elif b[0] > a[0] or (b[0] == a[0] and a[1] and not b[1]): J[i][j] = b
    return J
def merge(U, J):
    V = [r[:] for r in U]
    for i in range(NR):
        for j in range(NR):
            if i == j or J[i][j] is None: continue
            V = add(V, i, j, J[i][j][0], J[i][j][1])
            if V is None: return None
    return V

# ---------- the per-tuple job ----------
def job(args):
    t, b1, b2, att = args[:-1]
    global K, NR, W0, W1, NMAX
    K = args[-1]; NR = K - 1; W0 = (1, K - 1); W1 = (K + 1, 2 * K - 1); NMAX = 2 * K + 1
    n = (1,) + tuple(t)
    t0 = time.time(); rec = dict(t=list(t), att=att, ts=time.time())
    U = mk(n)
    if U is None:
        rec.update(s1='nobox', s2='skipped', d=round(time.time() - t0, 3)); return rec
    try:
        R = w0w(U, n, time.time() + b1)
        rec['s1'] = 'chain' if R is not None else 'none'
    except Budget:
        rec.update(s1='BUDGET', s2='skipped', d=round(time.time() - t0, 3)); return rec
    if rec['s1'] == 'none':
        rec.update(s2='skipped', d=round(time.time() - t0, 3)); return rec
    hit = []
    w1n = [0]
    try:
        Cs = w0chains(n, time.time() + b2 / 4)
        J = join(Cs)
        UJ = merge(U, J)
        dl = time.time() + b2
        def visit(W, word):
            w1n[0] += 1
            Rw = w0w(W, n, dl)
            if Rw is not None:
                hit.append((list(word), list(Rw[1])))
                return True
            return False
        if UJ is None:
            st = 'exhausted'
        else:
            st = w1(UJ, n, dl, visit)
        rec.update(w0n=len(Cs), s2='joint' if hit else ('none' if st == 'exhausted' else 'BUDGET'),
                   w1n=w1n[0], d=round(time.time() - t0, 3))
    except Budget:
        rec.update(s2='BUDGET', w0n=-1, w1n=w1n[0], d=round(time.time() - t0, 3))
    if hit:
        ver = verify_witness(n, hit[0][0], hit[0][1])
        rec['wit'] = ver if ver else 'EXTRACTION-FAILED'
    return rec

# ---------- checkpoint, driver ----------
def load_ckpt():
    done = {}
    try:
        for l in open(CKPT):
            l = l.strip()
            if not l: continue
            try: d = json.loads(l)
            except json.JSONDecodeError: continue
            done[tuple(d['t'])] = d
    except FileNotFoundError:
        pass
    return done
def final(rec):
    if rec is None: return False
    if rec.get('s1') in ('BUDGET',): return False
    if rec.get('s1') in ('none', 'nobox'): return True
    return rec.get('s2') in ('joint', 'none')
def main():
    global K, NR, W0, W1, NMAX, CKPT
    K = int(sys.argv[1])
    NR = K - 1; W0 = (1, K - 1); W1 = (K + 1, 2 * K - 1); NMAX = 2 * K + 1
    CKPT = os.path.join(HERE, 'schema_sweep_k%d_checkpoint.jsonl' % K)
    workers = int(sys.argv[2]) if len(sys.argv) > 2 else 8
    b1 = float(sys.argv[3]) if len(sys.argv) > 3 else 2.0
    b2 = float(sys.argv[4]) if len(sys.argv) > 4 else 120.0
    allt = list(itertools.combinations_with_replacement(range(1, NMAX + 1), K - 2))
    done = load_ckpt()
    queue = []
    for t in allt:
        r = done.get(t)
        if final(r): continue
        att = (r.get('att', 0) + 1) if r else 1
        eb1, eb2 = (b1, b2) if att == 1 else (b1 * 8 ** (att - 1), b2 * 4 ** (att - 1))
        if att > 3: continue
        queue.append((t, eb1, eb2, att, K))
    print('schema sweep k=%d: %d tuples, %d already final, %d queued (workers %d, b1 %gs, b2 %gs)' % (
        K, len(allt), sum(1 for t in allt if final(done.get(t))), len(queue), workers, b1, b2), flush=True)
    n_f = open(CKPT, 'a', buffering=1)
    done_n = 0; t0 = time.time()
    with Pool(workers) as p:
        for rec in p.imap_unordered(job, queue, chunksize=1):
            n_f.write(json.dumps(rec) + '\n'); n_f.flush()
            done_n += 1
            if done_n % 200 == 0 or rec.get('s2') in ('joint',) or done_n <= 40:
                print('[%6d/%d %.0fs] %s s1=%s s2=%s w1n=%s d=%s%s' % (
                    done_n, len(queue), time.time() - t0, tuple(rec['t']), rec.get('s1'), rec.get('s2'),
                    rec.get('w1n', '-'), rec.get('d'), (' WITNESS ' + json.dumps(rec.get('wit'))[:400]) if rec.get('wit') else ''), flush=True)
    print('queue drained: %d records this run, %.0fs total' % (done_n, time.time() - t0), flush=True)
if __name__ == '__main__':
    main()
