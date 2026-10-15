#!/usr/bin/env python3
"""Lonely intervals along grid-to-S deformations (as six_deform_v1.py: start v1*(1..5), move v5, v4, v3, v2 one at a
time, N rational steps each). Window [0, 2/v1]. At each sample, the lonely set at threshold 1/6 = intersection of the
five clear-band families [(k+1/6)/v, (k+5/6)/v], exact. Each interval is labelled (left runner, left lap; right
runner, right lap): the band entry it starts at and the band exit it ends at. Between consecutive samples intervals
are matched by overlap: no successor = DEATH, no predecessor = BIRTH, overlapping with a changed label = RELABEL.
Records per path: min number of intervals, steps with a death and a birth together (EXCHANGE), deaths of the last
interval in the window, and for births/deaths the runner pair (the moving runner and the other edge's runner)."""
import sys
from fractions import Fraction as F
from collections import Counter
N, K = int(sys.argv[1]), int(sys.argv[2])
sixth = F(1, 6)
def intervals(V, W):
    ivs = [(F(0), W, None, None)]
    for i, v in enumerate(V):
        new = []
        for a, b, la, lb in ivs:
            k0 = int(a * v - sixth) - 1
            k = max(k0, 0)
            while True:
                lo, hi = (k + sixth) / v, (k + 5 * sixth) / v
                if lo > b: break
                L, R = max(a, lo), min(b, hi)
                if L < R:
                    nla = (i + 1, k) if lo >= a else la
                    nlb = (i + 1, k) if hi <= b else lb
                    new.append((L, R, nla, nlb))
                k += 1
        ivs = new
    return ivs
def match(old, new):
    succ = {i: [j for j, (a2, b2, _, _) in enumerate(new) if a2 < b and b2 > a] for i, (a, b, _, _) in enumerate(old)}
    pred = {j: [i for i, (a, b, _, _) in enumerate(old) if a < b2 and b > a2] for j, (a2, b2, _, _) in enumerate(new)}
    return succ, pred
sets = [eval(l.split("\t")[0]) for l in list(open("six_cascade_observe_v1.tsv"))[1:]][::K]
chains = [tuple(map(int, l.split()[1:6])) for l in open("six_tau_over_v2.out")]
for label, group in (("ordinary sample", sets), ("resonant chains", chains)):
    minc = Counter(); deaths = births = exch = last_death = relabels = 0; dpair = Counter(); bpair = Counter()
    for S in group:
        Wn = F(2, S[0])
        V = [F(S[0] * k) for k in range(1, 6)]
        cur = intervals(V, Wn); mn = len(cur)
        for idx in (4, 3, 2, 1):
            a0, b0 = V[idx], F(S[idx])
            for j in range(1, N + 1):
                Wv = list(V); Wv[idx] = a0 + (b0 - a0) * F(j, N)
                if len(set(Wv)) < 5: continue
                nxt = intervals(Wv, Wn)
                succ, pred = match(cur, nxt)
                d = [i for i in succ if not succ[i]]; bb = [jj for jj in pred if not pred[jj]]
                deaths += len(d); births += len(bb)
                if d and bb: exch += 1
                if d and len(nxt) == 0: last_death += 1
                for i in d:
                    la, lb = cur[i][2], cur[i][3]
                    other = [x for x in (la, lb) if x and x[0] != idx + 1]
                    dpair[tuple(sorted(x[0] for x in other))] += 1
                for jj in bb:
                    la, lb = nxt[jj][2], nxt[jj][3]
                    other = [x for x in (la, lb) if x and x[0] != idx + 1]
                    bpair[tuple(sorted(x[0] for x in other))] += 1
                relabels += sum(1 for i in succ if len(succ[i]) == 1 and len(pred[succ[i][0]]) == 1
                                and (cur[i][2], cur[i][3]) != (nxt[succ[i][0]][2], nxt[succ[i][0]][3]))
                cur = nxt; mn = min(mn, len(cur))
            V[idx] = b0
        minc[mn] += 1
    print(f"{label}: paths {len(group)}; births {births}; deaths {deaths}; steps with both (exchange) {exch}; "
          f"deaths leaving the window empty {last_death}; relabels {relabels}")
    print(f"   fewest intervals in the window along a path: {dict(sorted(minc.items()))}")
    print(f"   death: other runner(s) at the dying interval's edges: {dpair.most_common(6)}")
    print(f"   birth: other runner(s) at the new interval's edges: {bpair.most_common(6)}")
