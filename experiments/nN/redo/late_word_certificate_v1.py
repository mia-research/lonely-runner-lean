"""Order 8: every cascade climb from R = 1 into (7, 9), as exact word polytopes.  Exact rational simplex.

Coordinates.  Readings s_1 = 1 (d_min) <= s_2 <= ... <= s_7 = S (d_j / d_min, sorted; a difference set is its
ratios by scale invariance).  R = 8 d_min t, so the bound is R = 1 and a reading s is in the subject's slot at R
iff |s R - 8M| < 1 for some M >= 1.  A move by setter j at lap M lands on R' = (8M + 1)/s_j (MANUSCRIPT_v21 s6.13).

A word w = ((j_1, M_1), ..., (j_L, M_L)) is a climb.  Its polytope (strict rows carry the margin tau, as in the
order-5 certificate, v21 s8.2):
  step 1:  8M_1 - 1 < s_{j1} < 8M_1 + 1                                  (setter in the slot at R = 1)
  step i:  (8M_i - 1) s_{j(i-1)} < (8M_{i-1} + 1) s_{ji} < (8M_i + 1) s_{j(i-1)}   (in the slot at R_{i-1})
  band 0:  R_i <= 7 for i < L, i.e. 8M_i + 1 <= 7 s_{ji}
  exit:    7 s_{jL} < 8M_L + 1          (R_L > 7; R_L < 9 follows from Thm 6.25)
  order:   1 <= s_2 <= ... <= s_7 <= B
Relaxation, in the sound direction: the rows keep only that each setter is in the slot just before it sets; they
drop that it is the LATEST opening and that the others are clear.  So every real climb into (7, 9) lies in the
polytope of its own word, and a property shown for every feasible word's polytope holds for every real climb.
Setters: d_min (s_1) is never in the slot for R in [1, 7] (|R - 8M| >= 1 there), so setters are s_2..s_7; a setter
never sets twice in a row, and its laps strictly increase along the word.

Output per arm: words tested, feasible prefixes, terminal words (climbs into (7,9)), and for the terminal words the
exact range of S over their polytopes."""
import sys, time
from fractions import Fraction as F
from multiprocessing import Pool

NV = 6                      # y_j = s_{j+2} - 1 >= 0, j = 0..5 ; tau is variable index 6

def simplex_min(A, b, c):   # minimise c.x s.t. A x <= b, x >= 0; exact; big-M; Bland (order5_certificate_v3)
    m = len(A); nv = len(c)
    art = [i for i in range(m) if b[i] < 0]
    ncol = nv + m + len(art)
    T = [[F(0)] * (ncol + 1) for _ in range(m)]
    basis = [0] * m; ai = nv + m
    for i in range(m):
        s = -1 if b[i] < 0 else 1
        for j in range(nv): T[i][j] = s * A[i][j]
        T[i][nv + i] = F(s); T[i][ncol] = s * b[i]
        if s < 0: T[i][ai] = F(1); basis[i] = ai; ai += 1
        else: basis[i] = nv + i
    cost = [(F(0), F(x)) for x in c] + [(F(0), F(0))] * m + [(F(1), F(0))] * len(art)
    while True:
        cB = [cost[bi] for bi in basis]; enter = -1
        bset = set(basis)
        for j in range(ncol):
            if j in bset: continue
            rc0 = cost[j][0] - sum(cB[i][0] * T[i][j] for i in range(m) if T[i][j] != 0)
            if rc0 < 0: enter = j; break
            if rc0 == 0:
                rc1 = cost[j][1] - sum(cB[i][1] * T[i][j] for i in range(m) if T[i][j] != 0)
                if rc1 < 0: enter = j; break
        if enter < 0: break
        leave = -1; best = None
        for i in range(m):
            if T[i][enter] > 0:
                r = T[i][ncol] / T[i][enter]
                if best is None or r < best or (r == best and basis[i] < basis[leave]): best = r; leave = i
        if leave < 0: return 'unbounded'
        pv = T[leave][enter]; T[leave] = [x / pv for x in T[leave]]
        for i in range(m):
            if i != leave and T[i][enter] != 0:
                f = T[i][enter]; T[i] = [a - f * bb for a, bb in zip(T[i], T[leave])]
        basis[leave] = enter
    if any(basis[i] >= nv + m and T[i][ncol] != 0 for i in range(m)): return None
    x = [F(0)] * nv
    for i in range(m):
        if basis[i] < nv: x[basis[i]] = T[i][ncol]
    return sum(ci * xi for ci, xi in zip(c, x)), x

def rows_of(word, B, Slo):
    """rows (a[0..5] over s_2..s_7, at, b): a.s + at*tau <= b."""
    R = []
    def row(coef, at, b):
        a = [F(0)] * NV
        for idx, v in coef.items():           # idx = reading index 1..7 (1 = d_min, constant 1)
            if idx == 1: b -= v
            else: a[idx - 2] += v
        R.append((a, at, b))
    j1, M1 = word[0]
    row({j1: F(-1)}, F(1), F(-(8 * M1 - 1)))              # s > 8M-1
    row({j1: F(1)}, F(1), F(8 * M1 + 1))                  # s < 8M+1
    for i in range(1, len(word)):
        jp, Mp = word[i - 1]; ji, Mi = word[i]
        # (8Mi-1) s_p < (8Mp+1) s_i   ->  (8Mi-1) s_p - (8Mp+1) s_i + tau <= 0
        c = {}; c[jp] = c.get(jp, 0) + F(8 * Mi - 1); c[ji] = c.get(ji, 0) - F(8 * Mp + 1); row(c, F(1), F(0))
        # (8Mp+1) s_i < (8Mi+1) s_p
        c = {}; c[ji] = c.get(ji, 0) + F(8 * Mp + 1); c[jp] = c.get(jp, 0) - F(8 * Mi + 1); row(c, F(1), F(0))
    for i, (j, M) in enumerate(word):
        if i < len(word) - 1:
            row({j: F(-7)}, F(0), F(-(8 * M + 1)))        # 8M+1 <= 7 s_j   (R_i <= 7)
    jL, ML = word[-1]
    for k in range(2, 7):                                 # s_k <= s_{k+1}
        a = [F(0)] * NV; a[k - 2] = F(1); a[k - 1] = F(-1); R.append((a, F(0), F(0)))
    a = [F(0)] * NV; a[5] = F(1); R.append((a, F(0), F(B)))          # s_7 <= B
    a = [F(0)] * NV; a[5] = F(-1); R.append((a, F(0), F(-Slo)))      # s_7 >= Slo
    return R

def lp(rows, obj, with_tau):
    nv = NV + (1 if with_tau else 0)
    A = []; b = []
    for a, at, bb in rows:
        A.append(list(a) + ([at] if with_tau else [])); b.append(bb - sum(a))   # s = 1 + y
    if with_tau:
        e = [F(0)] * nv; e[NV] = F(1); A.append(e); b.append(F(1))
    c = [F(0)] * nv
    if obj == 'tau': c[NV] = F(-1)
    else:
        idx, sense = obj; c[idx] = F(-1) if sense == 'max' else F(1)
    r = simplex_min(A, b, c)
    if r is None or r == 'unbounded': return None
    x = r[1]
    return x[NV] if obj == 'tau' else x[obj[0]] + 1

def terminal(word):
    j, M = word[-1]
    return None   # decided by rows: we branch both ways below

def search(args):
    first, B, Slo, maxlen = args
    Lmax = (7 * B + 1) // 8
    stats = {'tested': 0, 'feasible': 0}
    terms = []
    def rec(word):
        # two readings of the last step: it stays in band 0, or it exits into (7,9)
        stats['tested'] += 1
        rows_exit = rows_of(word, B, Slo)
        jL, ML = word[-1]
        a = [F(0)] * NV
        exit_rows = rows_exit + ([({jL: 1} and (lambda: None)) and None] if False else [])
        # exit: 7 s_jL < 8ML + 1
        ex = [F(0)] * NV; b_ex = F(8 * ML + 1)
        if jL == 1: b_ex -= 7
        else: ex[jL - 2] = F(7)
        tau_exit = lp(rows_exit + [(ex, F(1), b_ex)], 'tau', True)
        if tau_exit is not None and tau_exit > 0:
            lo = lp(rows_exit + [(ex, F(0), b_ex)], (5, 'min'), False)
            hi = lp(rows_exit + [(ex, F(0), b_ex)], (5, 'max'), False)
            terms.append((list(word), tau_exit, lo, hi))
        # stay in band 0: 8ML + 1 <= 7 s_jL
        st = [F(0)] * NV; b_st = -F(8 * ML + 1)
        if jL == 1: b_st += 7
        else: st[jL - 2] = F(-7)
        rows_stay = rows_exit + [(st, F(0), b_st)]
        tau_stay = lp(rows_stay, 'tau', True)
        if tau_stay is None or tau_stay <= 0: return
        stats['feasible'] += 1
        if len(word) >= maxlen: stats.setdefault('truncated', 0); stats['truncated'] += 1; return
        used = {}
        for j, M in word: used[j] = M
        for nj in range(2, 8):
            if nj == jL: continue
            for nM in range(used.get(nj, 0) + 1, Lmax + 1):
                rec(word + [(nj, nM)])
    rec([first])
    return first, stats, terms

if __name__ == '__main__':
    B = F(sys.argv[1]) if len(sys.argv) > 1 else F(9)
    Slo = F(sys.argv[2]) if len(sys.argv) > 2 else F(1)
    maxlen = int(sys.argv[3]) if len(sys.argv) > 3 else 40
    Lmax = (7 * B + 1) // 8
    starts = [(j, M) for j in range(2, 8) for M in range(1, int(Lmax) + 1)]
    t0 = time.time()
    print(f"late-word certificate: readings in [1, {B}], far reading S >= {Slo}, laps <= {Lmax}, words to {maxlen}", flush=True)
    with Pool() as p:
        res = p.map(search, [(s, B, Slo, maxlen) for s in starts])
    tested = sum(r[1]['tested'] for r in res); feas = sum(r[1]['feasible'] for r in res)
    trunc = sum(r[1].get('truncated', 0) for r in res)
    terms = [t for r in res for t in r[2]]
    print(f"  words tested {tested}; feasible band-0 prefixes {feas}; truncated at max length {trunc}; {time.time()-t0:.0f}s")
    print(f"  terminal words (climbs into (7,9)) with positive margin: {len(terms)}")
    if terms:
        lo = min(t[2] for t in terms); hi = max(t[3] for t in terms)
        print(f"  far reading S over all terminal polytopes: [{lo}, {hi}]  =  [{float(lo):.4f}, {float(hi):.4f}]")
        from collections import Counter
        print("  first step (setter reading index, lap) of terminal words:", dict(Counter(tuple(t[0][0]) for t in terms)))
        terms.sort(key=lambda t: len(t[0]))
        print(f"  shortest terminal word: {terms[0][0]} (length {len(terms[0][0])}), S in [{float(terms[0][2]):.4f}, {float(terms[0][3]):.4f}]")
        print(f"  longest terminal word length: {len(terms[-1][0])}")
