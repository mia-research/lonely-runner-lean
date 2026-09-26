"""Owner: perturb the speeds through the cascade to find the mechanism of a repeated setting.  For arrangements whose
Case C cascade (from 1/(8 g_1)) has a runner setting twice, move one runner's speed at a time (exact, integer speeds
scaled by 64 so steps are fine) until the repeat disappears; bisect to the exact boundary and report the link that
flips there: at the exit instant t = (8k+1)/(8s) of setter s, runner d changes between 'in the way' and 'clear', i.e.
|d(8k+1) - 8 m s| crosses s.  Exact; positive speeds throughout."""
from fractions import Fraction as F
from math import floor
from collections import Counter
from arrangement_lib import nd
from relay_law_v1 import chain, repeats

def steps(ds, t):
    """the chain with, per step, the in-way set and setter"""
    out = []
    while True:
        way = frozenset(d for d in ds if nd(d * t) < F(1, 8))
        if not way: return out
        cand = {d: (F(floor(d * t - F(1, 8)) + 1) + F(1, 8)) / d for d in way}
        s = max(cand, key=lambda x: cand[x]); out.append((t, way, s)); t = cand[s]

def reps(V):
    ds = sorted(v - V[0] for v in V[1:]); ch, _ = chain(ds, F(1, 8 * ds[0]))
    return len(repeats(ch)) > 0

def study(V, j, sign, maxfrac=F(1, 5)):
    """move V[j] by sign*x*gap-scale until the repeat vanishes (x up to maxfrac of V[j]-V[j-1]); exact bisection"""
    base = V[j]; span = maxfrac * (V[j] - V[j - 1] if j > 0 else V[j])
    def Vx(x):
        W = list(V); W[j] = base + sign * x * span; return W
    lo, hi = F(0), None
    for k in range(1, 41):
        x = F(k, 40)
        W = Vx(x)
        if len(set(W)) < 8 or min(W) <= 0 or sorted(W) != [W[i] for i in sorted(range(8), key=lambda i: W[i])]: break
        if not reps(W): hi = x; break
        lo = x
    if hi is None: return None
    for _ in range(40):
        mid = (lo + hi) / 2
        if reps(Vx(mid)): lo = mid
        else: hi = mid
    A, B = Vx(lo), Vx(hi)
    dsA = sorted(v - A[0] for v in A[1:]); dsB = sorted(v - B[0] for v in B[1:])
    sa, sb = steps(dsA, F(1, 8 * dsA[0])), steps(dsB, F(1, 8 * dsB[0]))
    rank = lambda ds, d: ds.index(d)
    for i, ((ta, wa, xa), (tb, wb, xb)) in enumerate(zip(sa, sb)):
        ra = {rank(dsA, d) for d in wa}; rb = {rank(dsB, d) for d in wb}
        if ra != rb or rank(dsA, xa) != rank(dsB, xb):
            return dict(j=j, sign=sign, x=float(lo), step=i, way_with=sorted(ra), way_without=sorted(rb),
                        setter_with=rank(dsA, xa), setter_without=rank(dsB, xb),
                        prev_setter=rank(dsA, sa[i - 1][2]) if i else None,
                        chain_with=[rank(dsA, s) for _, _, s in sa], chain_without=[rank(dsB, s) for _, _, s in sb])
    return dict(j=j, sign=sign, x=float(lo), note='chains agree on the common prefix; lengths differ',
                chain_with=[rank(dsA, s) for _, _, s in sa], chain_without=[rank(dsB, s) for _, _, s in sb])

if __name__ == '__main__':
    import case_c_map_v1 as cm
    cm.rnd.seed(26); cases = []
    for shape in ('even', 'clumped+outliers', 'even+clump'):
        for g1div in (30, 100, 1000):
            n = 0
            while n < 150:
                g = cm.rest(shape); W6 = sum(g); g1 = max(1, W6 // (g1div - 1))
                if g1 + W6 <= 22 * g1: continue
                V = cm.arrangement([g1] + g)
                if len(set(V)) < 8: continue
                n += 1
                if reps(V): cases.append((shape, g1div, [64 * v for v in V]))
    print(f"arrangements with a repeated setting: {len(cases)}")
    flips = Counter()
    for shape, g1div, V in cases:
        print(f"\n== {shape} W/{g1div}  gaps {[ (V[i+1]-V[i])//64 for i in range(7)]}")
        for j in range(1, 8):
            for sign in (1, -1):
                r = study(V, j, sign)
                if r is None: continue
                if 'note' in r:
                    print(f"  move runner {j} {'+' if sign>0 else '-'}: repeat gone at x={r['x']:.4f}; {r['note']}; with {r['chain_with']} without {r['chain_without']}")
                    continue
                gained = sorted(set(r['way_without']) - set(r['way_with'])); lost = sorted(set(r['way_with']) - set(r['way_without']))
                print(f"  move runner {j} {'+' if sign>0 else '-'}: repeat gone at x={r['x']:.4f}, step {r['step']} after setter {r['prev_setter']}: "
                      f"in the way lost {lost} gained {gained}; chain with {r['chain_with']} -> without {r['chain_without']}")
                flips[(tuple(lost), tuple(gained))] += 1
    print("\nflip types (in-the-way lost, gained) at the boundary:", flips.most_common(12))
