"""E659 (block step rule, any setter; E658 extended). E658 check of the folded-block step rule (derived in the log entry first). Signed readings e_i = y_i - v_k of the
other block form an AP in i with step s. At the exit of other-block reading j (sign sg_j, |e_j| t = M + 1/8),
delta = s t, f_i = frac(sg_j (i - j) delta): i is in the way iff f_i in (3/4, 1); its exit is later than t by
(1 - f_i)/|e_i| if e_i has the sign of e_j, and by (f_i - 3/4)/|e_i| otherwise. Own-block in-way readings enter with
their exits as computed. Predicted next setter = latest exit; checked against the unchanged cascade on every move from
an other-block setter. Two populations: the rational strip of E647 (all G, gap and interleaved) and the Q(sqrt2)
strip of E657. Argument: 'rat' or 'irr'."""
import sys, io, contextlib, pickle
from fractions import Fraction as F
from collections import Counter
from qsqrt2_v1 import Q2
import math
MODE = sys.argv[1]
E = F(1, 8)
if MODE == 'rat':
    def fl(x): return math.floor(x)
    def num(x): return F(x)
    key = lambda x: x
else:
    def fl(x): return x.floor()
    def num(x): return Q2(x)
    key = float
def frac(x): return x - fl(x)
def dist(x):
    f = frac(x); return f if f < 1 - f else 1 - f
def rnd(x): return fl(x + F(1, 2))
def cascade(r):
    t = F(1, 8) / r[0]; path = []
    while True:
        way = [(i, d) for i, d in enumerate(r) if dist(d * t) < E]
        if not way: return t, path
        best = None
        for i, d in way:
            M = rnd(d * t); nt = (M + E) / d
            if best is None or key(nt) > key(best[0]) or (nt == best[0] and False): best = (nt, i, M)
        t, i, M = best; path.append((i, M, t))
res = Counter(); bad = []
def check(p, b, G, k, reg):
    A = G + (p - 1)
    v = [num(i) for i in range(p)] + [A + b * j for j in range(8 - p)]
    if len({(x.a, x.b) if MODE == 'irr' else x for x in v}) < 8: return
    ownb = list(range(p)) if k < p else list(range(p, 8))
    oth = [i for i in range(8) if i not in ownb]           # in index order: signed readings e_i form an AP
    s = b if k < p else num(1)
    e = {i: v[i] - v[k] for i in oth}
    rd = sorted(((v[i] - v[k]) if v[i] > v[k] else (v[k] - v[i]), i) for i in range(8) if i != k)
    rd.sort(key=lambda z: key(z[0]))
    r = [d for d, _ in rd]; who = [i for _, i in rd]
    _, path = cascade(r)
    blocks = [list(range(p)), list(range(p, 8))]
    steps_ = [num(1), b]
    for (ia, Ma, ta), (ib, Mb, tb) in zip(path, path[1:]):
        wa = who[ia]
        bi = 0 if wa < p else 1
        B = blocks[bi]; sB = steps_[bi]
        eB = {i: v[i] - v[k] for i in B if i != k}
        sj = 1 if eB[wa] > 0 else -1
        ja = B.index(wa); delta = sB * ta; cand = []
        for i in B:
            if i == k or i == wa: continue
            f = frac(delta * (sj * (B.index(i) - ja)))
            if f > F(3, 4) and f < 1:
                ei = eB[i]; ae = ei if ei > 0 else -ei
                same = (ei > 0) == (sj > 0)
                cand.append((ta + ((1 - f) if same else (f - F(3, 4))) / ae, i))
        for w in blocks[1 - bi]:
            if w == k: continue
            d = r[who.index(w)]
            if dist(d * ta) < E: cand.append(((rnd(d * ta) + E) / d, w))
        kind = 'own-block setter' if wa in ownb else 'other-block setter'
        if not cand: res[(reg, kind, 'no predicted in-way reading')] += 1; continue
        mx = max(cand, key=lambda z: key(z[0]))
        tied = [c for c in cand if c[0] == mx[0]]
        wb = who[ib]
        if mx[0] == tb and any(c[1] == wb for c in tied):
            res[(reg, kind, 'agree' + (' (exit tie)' if len(tied) > 1 else ''))] += 1
        else:
            res[(reg, kind, 'differ')] += 1
            if len(bad) < 8: bad.append((p, str(b), str(G), k, wa, wb, [(str(c[0]), c[1]) for c in cand], str(tb)))
if MODE == 'rat':
    recs = pickle.load(open('two_block_strip_cascade_v1.pkl', 'rb'))
    seen = set()
    for (p, b, G, k, *_rest) in recs:
        check(p, b, G, k, 'gap' if G > 0 else 'interleaved')
else:
    with contextlib.redirect_stdout(io.StringIO()):
        from two_block_remainder_v1 import gcov
    r2 = Q2(0, 1)
    for p in range(2, 7):
        for n in range(2, 96, 4):
            bq = F(n, 12); b = r2 * F(1, 100) + bq
            gc, _ = gcov(p, bq); m = max(F(1), bq)
            gs = [F(-(p - 1)) + F(j, 4) for j in range(4 * (p - 1) + 1)]
            g = m / 4
            while g < gc: gs.append(g); g += m / 4
            for g in gs:
                for k in range(8): check(p, b, r2 * F(1, 997) + g, k, 'gap' if g > 0 else 'interleaved')
print(MODE)
for kk, vv in sorted(res.items()): print("  ", vv, kk)
for x in bad: print("  differ:", x)
