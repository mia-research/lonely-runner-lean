#!/usr/bin/env python3
"""Six-runner box tree, as o7_box6_exact_v3 (same serialisation, same split rule), but the leaf SEARCH is float and
every leaf found is VERIFIED in exact Fractions before it is written; if the float candidate fails the exact check,
the exact search of v3 is run for that box.  The written tree is therefore exactly checked leaf by leaf (and again by
the Lean kernel).  Usage: o7_box6_exact_v4.py Xn Xd Yn Yd T out.txt"""
import sys, time, math
from fractions import Fraction as Fr
sys.setrecursionlimit(200000)
S7, S67 = Fr(1, 7), Fr(6, 7)
def runner_tau_f(a, b, T):
    out = []; n = 0
    while True:
        lo = (n + 1 / 7) / a; hi = (n + 6 / 7) / b
        if lo > T: break
        if hi >= lo: out.append((lo, min(hi, T), n))
        n += 1
    return out
def runner_tau(a, b, T):
    out = []; n = 0
    while True:
        lo = (n + S7) / a; hi = (n + S67) / b
        if lo > T: break
        if hi >= lo: out.append((lo, min(hi, T), n))
        n += 1
    return out
def search(box, T, rt):
    cur = [(lo, hi, (n,)) for lo, hi, n in rt(box[5], box[5], T)]
    for i in (4, 3, 2, 1, 0):
        B = rt(box[i][0], box[i][1], T); nxt = []; p = q = 0
        while p < len(cur) and q < len(B):
            lo, hi = max(cur[p][0], B[q][0]), min(cur[p][1], B[q][1])
            if hi >= lo: nxt.append((lo, hi, (B[q][2],) + cur[p][2]))
            if cur[p][1] < B[q][1]: p += 1
            else: q += 1
        cur = nxt
        if not cur: return None
    return cur
def exact_leaf_ok(box, tau, ns):
    for i in range(5):
        a, b = box[i]
        if not (a > 0 and ns[i] + S7 <= a * tau and b * tau <= ns[i] + S67): return False
    return ns[5] + S7 <= tau <= ns[5] + S67
def leaf(box, T):
    fb = [(float(a), float(b)) for a, b in box] + [1.0]
    cand = search(fb, float(T), runner_tau_f)
    if cand:
        for lo, hi, ns in cand[:4]:
            for tf in ((lo + hi) / 2, lo, hi):
                tau = Fr(tf).limit_denominator(10**6)
                if exact_leaf_ok(box, tau, ns): return tau, ns
    ex = search(list(box) + [Fr(1)], T, runner_tau)
    if ex: return ex[0][0], ex[0][2]
    return None
def split_pt(a, b):
    m = (a + b) / 2
    lo, hi = math.floor(a * 42) + 1, math.ceil(b * 42) - 1
    ks = [Fr(k, 42) for k in range(max(1, lo), min(41, hi) + 1) if a < Fr(k, 42) < b]
    best = ks[0] if ks else m
    for z in ks:
        if abs(z - m) < abs(best - m): best = z
    return best
cnt = {"L": 0, "E": 0}
def build(box, T, out):
    stack = [("box", box)]
    while stack:
        kind, item = stack.pop()
        if kind == "str": out.append(item); continue
        box = item
        if any(box[i][0] >= box[i + 1][1] for i in range(4)) or box[4][0] >= 1:
            cnt["E"] += 1; out.append("E"); continue
        r = leaf(box, T)
        if r is not None:
            cnt["L"] += 1; tau, ns = r
            out.append(f"(L {tau.numerator} {tau.denominator} {' '.join(map(str, ns))})"); continue
        w = [b - a for a, b in box]; d = max(range(5), key=lambda k: w[k])
        if w[d] < Fr(1, 50000): raise RuntimeError(f"stuck {box}")
        m = split_pt(*box[d])
        l = list(box); l[d] = (box[d][0], m); r_ = list(box); r_[d] = (m, box[d][1])
        out.append(f"(S {d} {m.numerator} {m.denominator} ")
        stack += [("str", ")"), ("box", r_), ("str", " "), ("box", l)]
if __name__ == "__main__":
    X = Fr(int(sys.argv[1]), int(sys.argv[2])); Y = Fr(int(sys.argv[3]), int(sys.argv[4])); T = Fr(int(sys.argv[5]))
    t0 = time.time(); out = []
    build([(X, Fr(1))] * 4 + [(max(X, Y), Fr(1))], T, out)
    tree = "".join(out)
    open(sys.argv[6], "w").write(tree + "\n")
    print(f"six-runner tree x1..x4 in [{X}, 1], x5 in [{max(X, Y)}, 1]: leaves {cnt['L']}, empty {cnt['E']}, "
          f"{len(tree)} chars, {time.time() - t0:.0f} s")
