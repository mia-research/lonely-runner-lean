#!/usr/bin/env python3
"""E34: the lineage of the 5/6 grid event along STRAIGHT-LINE paths d(l) = (1-l) G + l S, l in [0,1], G = v1*(1..5)
(all speeds move together; d_1 = v1 fixed since G_1 = S_1). Each pair inequality of a lap box is linear in l, so a
box is alive on an exact closed l-interval. Follow L from (0,1,2,3,4) just off the grid; at each death of L the
takeover is the box alive just past the death whose instant is nearest to L's. Per death records: l, L, closing
pairs, B, B - L, jump (in 1/d_min), status (open / born), opening pairs if born, number of boxes alive just past,
and THIN = no box other than L alive on both sides of the death.
Usage: six_lineage_line_v1.py K out.tsv  (every K-th residual set in [1,40] plus the 11 chains)"""
import sys
from fractions import Fraction as F
src = open("six_boxes_v1.py").read().split("K = int(sys.argv[1])")[0]
ns = {}; exec(src, ns)
lonely_boxes, instant = ns["lonely_boxes"], ns["instant"]
def spd(G, D, l): return [g + l * d for g, d in zip(G, D)]
def alive_l(G, D, k):
    lo, hi = F(0), F(1)
    for i in range(5):
        for j in range(5):
            if i == j: continue
            c0 = (6*k[i]+1)*G[j] - (6*k[j]+5)*G[i]; c1 = (6*k[i]+1)*D[j] - (6*k[j]+5)*D[i]   # c0 + c1 l <= 0
            if c1 == 0:
                if c0 > 0: return None
            elif c1 > 0: hi = min(hi, -c0 / c1)
            else: lo = max(lo, -c0 / c1)
    return (lo, hi) if lo <= hi else None
def tight(W, k): return [(i+1, j+1, k[i], k[j]) for i in range(5) for j in range(5) if i != j and (6*k[i]+1)*W[j] == (6*k[j]+5)*W[i]]
def run(S, log, tag, G=None, L0=(0, 1, 2, 3, 4)):
    G = G or [F(S[0] * i) for i in range(1, 6)]; D = [F(s) - g for s, g in zip(S, G)]
    boxes = {}
    def discover(l, tc):
        W = spd(G, D, l)
        for k in lonely_boxes(W, max(F(3) / min(W), tc + F(2) / min(W))):
            if k not in boxes:
                iv = alive_l(G, D, k)
                if iv: boxes[k] = iv
        return W
    L = L0; iv = alive_l(G, D, L); boxes[L] = iv
    l = F(0)
    for t in range(41): discover(F(t, 40), instant(spd(G, D, F(t, 40)), L))
    while True:
        lL, hL = boxes[L]
        if hL >= 1: return
        x = hL; W = spd(G, D, x); tL = instant(W, L); eps = F(1, 10**9)
        discover(x + eps, tL); discover(x, tL); discover(x - eps, tL)
        cand = {k: b for k, b in boxes.items() if k != L and b[0] <= x < b[1]}
        if not cand: raise RuntimeError(f"no takeover {tag} l={x}")
        B = min(cand, key=lambda k: (abs(instant(W, k) - tL), instant(W, k))); tB = instant(W, B)
        born = cand[B][0] == x
        thin = not any(b[0] < x < b[1] for k, b in boxes.items() if k != L)
        log.write("\t".join(map(str, [tag, x, L, tight(W, L), B, tuple(bb - ll for ll, bb in zip(L, B)), tB - tL,
                  float((tB - tL) * min(W)), "born" if born else "open", tight(W, B) if born else "", len(cand),
                  "THIN" if thin else ""])) + "\n")
        L = B
log = open(sys.argv[2], "w")
log.write("tag\tl\tL\tL_closing\tB\tdelta\tjump\tjump_dmin\tB_status\tB_opening\tn_alive_after\tthin\n")
if sys.argv[1] == "control":
    import random
    rng = random.Random(5); bad = 0; tot = 0
    sets = [eval(l_.split("\t")[0]) for l_ in list(open("six_cascade_observe_v1.tsv"))[1:]][::400]
    for S in sets:
        G = [F(S[0] * i) for i in range(1, 6)]; D = [F(s) - g for s, g in zip(S, G)]
        for _ in range(20):
            l = F(rng.randint(0, 1000), 1000); W = spd(G, D, l)
            for k in lonely_boxes(W, F(3) / min(W)):
                tot += 1; iv = alive_l(G, D, k)
                bad += not (iv and iv[0] <= l <= iv[1])
    print("interval check: boxes found lonely at sampled l", tot, "; not inside their computed interval:", bad)
    c = 7
    run((c, 2*c, 3*c, 4*c, 6*c), log, "control-face", G=[F(c), F(2*c), F(3*c), F(4*c), F(4*c)], L0=(0, 0, 0, 0, 0))
    log.close(); print(open(sys.argv[2]).read()); sys.exit()
K = int(sys.argv[1])
sets = [eval(l_.split("\t")[0]) for l_ in list(open("six_cascade_observe_v1.tsv"))[1:]][::K]
chains = [tuple(map(int, l_.split()[1:6])) for l_ in open("six_tau_over_v2.out")]
for group, ss in (("ordinary", sets), ("chain", chains)):
    for S in ss: run(S, log, f"{group}{S}")
log.close()
