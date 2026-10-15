#!/usr/bin/env python3
"""E30: the lineage of one isolation along a deformation. Start: the grid event that survives (for spread > 5, the
5/6 event, box laps (0,1,2,3,4)). Moves as E21/E23 (v5, v4, v3, v2 linearly to S; v1 fixed), or a custom path.
While one speed d_m moves, every lap box is alive on an exact closed interval of d_m (six_boxes_v1.py). Follow the
current box L; at its death point x (end of its interval in the direction of motion), the takeover is the box alive
just past x whose instant is NEAREST to L's instant at x (not the earliest). Record per death:
  L, its closing pairs; takeover B, B - L; jump tB - tL (in 1/d_min and in mover laps); whether B was open before x
  or born at x; if born at x, B's opening pairs (tight at x); number of boxes alive just past x within the window.
Usage: six_lineage_v1.py K out.tsv          (every K-th residual set in [1,40] plus the 11 chains)
       six_lineage_v1.py custom out.tsv "V0" m target   (start speeds V0 as a python list, move index m to target)"""
import sys, ast
from fractions import Fraction as F
src = open("six_boxes_v1.py").read().split("K = int(sys.argv[1])")[0]
ns = {}; exec(src, ns)
lonely_boxes, alive_interval, instant = ns["lonely_boxes"], ns["alive_interval"], ns["instant"]
def tight(W, k): return [(i+1, j+1, k[i], k[j]) for i in range(5) for j in range(5) if i != j and (6*k[i]+1)*W[j] == (6*k[j]+5)*W[i]]
def boxes_on_move(V, m, b, tL):
    a = V[m]; lo_x, hi_x = min(a, b), max(a, b); boxes = {}
    def discover(x, tcen):
        W = list(V); W[m] = x; Wd = max(F(3) / min(W), tcen + F(2) / min(W))
        for k in lonely_boxes(W, Wd):
            if k not in boxes:
                iv = alive_interval(V, m, k)
                if iv: boxes[k] = iv
    for t in range(41): discover(lo_x + (hi_x - lo_x) * F(t, 40), tL)
    return boxes, lo_x, hi_x, discover
def run_move(V, m, b, L, log, tag):
    up = b > V[m]
    while True:
        W0 = list(V); tL0 = instant(W0, L)
        boxes, lo_x, hi_x, discover = boxes_on_move(V, m, b, tL0)
        if L not in boxes:
            iv = alive_interval(V, m, L)
            if iv is None: raise RuntimeError(f"lineage box {L} not alive at move start {tag}")
            boxes[L] = iv
        l, h = boxes[L]; x = h if up else l
        if (up and x >= b) or (not up and x <= b): return L        # survives the rest of the move
        W = list(V); W[m] = x; tL = instant(W, L)
        eps = F(1, 10**9) * (1 if up else -1)
        discover(x + eps, tL); discover(x, tL)
        cand = {k: iv for k, iv in boxes.items() if k != L and (iv[0] <= x < iv[1] if up else iv[0] < x <= iv[1])}
        if not cand: raise RuntimeError(f"no takeover at {tag} x={x}")
        B = min(cand, key=lambda k: (abs(instant(W, k) - tL), instant(W, k)))
        tB = instant(W, B); ivB = cand[B]
        born = (ivB[0] == x) if up else (ivB[1] == x)
        dmin = min(W)
        log.write("\t".join(map(str, [tag, m + 1, x, L, tight(W, L), B, tuple(bb - ll for ll, bb in zip(L, B)),
              tB - tL, float((tB - tL) * dmin), float((tB - tL) * x), "born" if born else "open",
              tight(W, B) if born else "", len(cand)])) + "\n")
        # continue the move from x with the new lineage box
        V = list(V); V[m] = x + eps; L = B
        if (up and V[m] >= b) or (not up and V[m] <= b): return L
log = open(sys.argv[2], "w")
log.write("tag\tmover\tx\tL\tL_closing\tB\tdelta\tjump\tjump_dmin\tjump_moverlaps\tB_status\tB_opening\tn_alive_after\n")
if sys.argv[1] == "custom":
    V = [F(v) for v in sys.argv[3].strip("[]").split(",")]; m = int(sys.argv[4]); b = F(sys.argv[5])
    L0 = ast.literal_eval(sys.argv[6]) if len(sys.argv) > 6 else None
    W = list(V); boxes = lonely_boxes(W, F(3) / min(W))
    if L0 is None: print("boxes at start:", sorted(boxes, key=lambda k: instant(W, k))[:8]); sys.exit()
    run_move(V, m, b, L0, log, f"custom{tuple(sys.argv[3:5])}")
else:
    K = int(sys.argv[1])
    sets = [eval(l.split("\t")[0]) for l in list(open("six_cascade_observe_v1.tsv"))[1:]][::K]
    chains = [tuple(map(int, l.split()[1:6])) for l in open("six_tau_over_v2.out")]
    for group, ss in (("ordinary", sets), ("chain", chains)):
        for S in ss:
            V = [F(S[0] * k) for k in range(1, 6)]; L = (0, 1, 2, 3, 4)
            for m in (4, 3, 2, 1):
                b = F(S[m])
                if V[m] != b:
                    if m == 4: V[4] += F(1, 10**9)          # step off the grid, onto the side where 5/6 opens
                    L = run_move(V, m, b, L, log, f"{group}{S}")
                V[m] = b
log.close()
