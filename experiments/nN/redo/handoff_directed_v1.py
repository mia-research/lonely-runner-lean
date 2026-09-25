"""Step 2, directed.  handoff_search_v1 (random offsets in [1,80]) found 0 handoffs in 4000: random offsets
rarely bunch at the core's opening.  Here the bunching is built in.  Arrangement: subject s = 1000, core
runners s + a, s + b (b/a just short of 7, so the core's first cell is narrow), a fast train s + N + j*d
(j = 0..f-1).  At the core's opening t_C = 1/(8a) the offsets j*d*t_C are spread round the circle with no gap
> 1/4, so the train is blocked when the core opens.  Every runner of the arrangement is run through the
exact cascade; the subject is the one whose readings carry the core/train split.

Prediction (N -> infinity limit, exact): t_pred = the first instant >= t_C at which the core is clear AND
the train's offsets leave a gap >= 1/4 (so the fast phase N*t can sit at distance >= 1/8 from all of them).
Both conditions change only at breakpoints c*t in Z +- 1/8 and (e_i - e_j)*t in Z + {0, 1/4, 3/4}; between
breakpoints each is constant, tested at the exact midpoint."""
from fractions import Fraction as F
from math import floor, ceil
from arrangement_lib import readings, nd
from isolated_persistence_v1 import cascade_cap
from block_rule_derived_v1 import max_gap

def breakpoints(rates, offsets, lo, hi):
    pts = {lo, hi}
    for c, sh in [(c, s) for c in rates for s in (F(1, 8), F(7, 8))] + \
                 [(abs(x - y), s) for x in offsets for y in offsets if x != y for s in (F(0), F(1, 4), F(3, 4))]:
        for m in range(floor(c * lo) - 1, ceil(c * hi) + 1):
            t = (m + sh) / c
            if lo < t < hi: pts.add(t)
    return sorted(pts)

def t_pred(core, E, lo, hi):
    bp = breakpoints(core, E, lo, hi)
    for u, v in zip(bp, bp[1:]):
        m = (u + v) / 2
        if all(nd(c * m) >= F(1, 8) for c in core) and max_gap([e * m for e in E]) >= F(1, 4):
            return u
    return None

def core_cells(core, lo, hi):
    bp = breakpoints(core, [], lo, hi); out = []
    for u, v in zip(bp, bp[1:]):
        if all(nd(c * (u + v) / 2) >= F(1, 8) for c in core):
            if out and out[-1][1] == u: out[-1] = (out[-1][0], v)
            else: out.append((u, v))
    return out

def run(a, b, d, f, N, s=1000):
    core, E = [a, b], [j * d for j in range(f)]
    V = [s, s + a, s + b] + [s + N + e for e in E]
    assert len(set(V)) == len(V) <= 8
    tC = F(1, 8 * a)
    cells = core_cells(core, tC, tC + 1)
    tp = t_pred(core, E, tC, tC + 1)
    ev = [cascade_cap(readings(V, k))[0] for k in range(len(V))]
    t = ev[0]
    idx = next((i for i, (u, v) in enumerate(cells) if u <= t <= v), None)
    return dict(tC=tC, cell1=cells[0], gap_tC=max_gap([e * tC for e in E]), t=t, idx=idx, tp=tp,
                off=(t - tp) * N if tp is not None else None, ev=ev)

if __name__ == '__main__':
    print("base: a=10, b=69, d=16, f=5, N=10^5")
    r = run(10, 69, 16, 5, 10**5)
    print(f"  t_C={r['tC']}, first core cell [{float(r['cell1'][0]):.6f}, {float(r['cell1'][1]):.6f}], "
          f"train max gap at t_C {r['gap_tC']}; subject event {float(r['t']):.6f} in core cell #{r['idx']}; "
          f"t_pred {r['tp']} = {float(r['tp']):.6f}; (t - t_pred)*N = {float(r['off']):.3f}")
    print("  every runner's event:", [f"{float(x):.6f}" for x in r['ev']])
    print("\nperturb b (core ratio), d (train step), f (train length), N:")
    rows = []
    for b in (61, 63, 65, 67, 68, 69):
        for d in (12, 14, 16, 18, 20):
            for f in (4, 5):
                for N in (10**4, 10**5, 10**6):
                    r = run(10, b, d, f, N)
                    rows.append((b, d, f, N, r))
    handoff = [x for x in rows if x[4]['idx'] != 0]
    print(f"  {len(rows)} arrangements; handoff (event outside the core's first cell) in {len(handoff)}")
    offs = [float(x[4]['off']) for x in rows]
    print(f"  (t - t_pred)*N over all: min {min(offs):.3f}, max {max(offs):.3f}")
    from collections import Counter
    print("  core-cell index of the event:", dict(Counter(x[4]['idx'] for x in rows)))
    for b, d, f, N, r in rows:
        if N == 10**5 and f == 5:
            print(f"   b={b} d={d}: first cell [{float(r['cell1'][0]):.5f},{float(r['cell1'][1]):.5f}] gap@tC {float(r['gap_tC']):.3f}"
                  f"  event {float(r['t']):.6f} cell#{r['idx']}  t_pred {r['tp']}  (t-tp)N {float(r['off']):.2f}")
