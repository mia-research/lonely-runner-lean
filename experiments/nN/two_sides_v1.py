"""Do the two sides cover everything?  (exhaustive on the [1,40] residual)

  LEN      the length induction: the six other disparities (S without d_max) have a lonely cell
           at 1/8 of length >= 1/(4 d_max) -- ANY of their cells, not the cascade's first -- so
           d_max is clear inside it.
  NEAR-AP  the sign rule's instants: some d in S read as the k-th term of an AP of step D = d/k
           (k = 1..7); its global instants a/(8D) = a k/(8 d), a in {1, 3, 5, 7}: one is lonely.
  RULE     the rung-selection rule at some q <= 8 (rung_selection_v1).
Reported: how many residual sets each covers, and every set that LEN misses and the other two miss
too, with ALL its lonely cells (the user's point: the cascade finds one isolation, others may
exist and a rule may be catching a different one).
Floating point for the cell sweep (boundaries have denominators <= 8*40*... far apart), with an
exact Fraction recheck of any length ratio within 1e-9 of 1.
"""
import itertools, os, time
from fractions import Fraction as F
from multiprocessing import Pool
from collections import Counter
HERE = os.path.dirname(os.path.abspath(__file__))
_rs = os.path.join(HERE, 'rung_selection_v1.py')
_s = open(_rs).read(); __file__ = _rs; exec(_s[:_s.index("for top in (30, 40):")])

def ndf(x): x = x % 1.0; return min(x, 1.0 - x)
def cells_f(S):
    pts = sorted({((8 * n + s) / (8 * d)) % 1.0 for d in S for n in range(d + 1) for s in (1, -1)} | {0.0}) + [1.0]
    out = []; run = None
    for a, b in zip(pts, pts[1:]):
        if b - a < 1e-15: continue
        if all(ndf(d * (a + b) / 2) >= 0.125 - 1e-12 for d in S):
            run = a if run is None else run
        else:
            if run is not None: out.append((run, a)); run = None
    if run is not None: out.append((run, 1.0))
    return out
def longest_exact(S):
    E = F(1, 8)
    def nd(x): x = x % 1; return min(x, 1 - x)
    pts = sorted({F(8 * n + s, 8 * d) % 1 for d in S for n in range(d + 1) for s in (1, -1)} | {F(0)}) + [F(1)]
    best = F(0); run = None
    for a, b in zip(pts, pts[1:]):
        if all(nd(d * (a + b) / 2) >= E for d in S):
            run = a if run is None else run; best = max(best, b - run)
        else: run = None
    return best
def LEN(S):
    D = max(S); six = [d for d in S if d != D]
    r = max((b - a for a, b in cells_f(six)), default=0.0) * 4 * D
    if abs(r - 1) < 1e-9: return longest_exact(six) * 4 * D >= 1
    return r >= 1
def NEAR(S):
    for d in S:
        for k in range(1, 8):
            for a in (1, 3, 5, 7):
                t = F(a * k, 8 * d)
                if all(8 * min((e * t) % 1, 1 - (e * t) % 1) >= 1 for e in S): return (d, k, a)
    return None
def RULE(S): return any(rule(S, q, free_exact) for q in range(2, 9))
def job(S):
    l = LEN(S); n = NEAR(S) is not None; r = RULE(S)
    return S, l, n, r

if __name__ == '__main__':
    t0 = time.time()
    R = [S for S in itertools.combinations(range(1, 41), 7) if eight_residual(S)]
    c = Counter(); left = []
    with Pool(4) as pool:
        for S, l, n, r in pool.imap_unordered(job, R, chunksize=200):
            c[(l, n, r)] += 1
            if not (l or n or r): left.append(S)
    tot = len(R)
    print(f"[1,40] residual {tot}  ({time.time()-t0:.0f}s)")
    print("   (LEN, NEAR-AP, RULE) counts:", sorted(c.items(), key=lambda x: -x[1]))
    print(f"   LEN covers {sum(v for k, v in c.items() if k[0])}; NEAR-AP {sum(v for k, v in c.items() if k[1])}; RULE {sum(v for k, v in c.items() if k[2])}")
    print(f"   LEN fails: {sum(v for k, v in c.items() if not k[0])}; of those covered by NEAR-AP or RULE: {sum(v for k, v in c.items() if not k[0] and (k[1] or k[2]))}")
    print(f"   covered by none: {len(left)}")
    for S in sorted(left)[:12]:
        cs = cells_f(S)
        print(f"      {S}: {len(cs)} lonely cells in [0,1): " + ", ".join(f"[{a:.5f},{b:.5f}]" for a, b in cs[:8]) + (" ..." if len(cs) > 8 else ""))
