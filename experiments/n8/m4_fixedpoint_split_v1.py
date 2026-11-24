#!/usr/bin/env python3
"""m4_fixedpoint_split_v1 -- can M4BoxNoCarvePinned be paid by sub-box FixedClearCerts?

Object: an M4 box n (leading 1 + the 6-tuple t of m4comp_cert_ckpt_v1.jsonl), faces
FaceLo/FaceHi of Fresh/FilterAssembly.lean (n=1 -> [1,3/2], else [n-1/2, n+1/2]), with the pin
(some coordinate with n_i = 1 has g_i = 1 exactly; one case per such coordinate).

Leaf test (exact Fractions): the set of R in [1,7] with R*[lo_i,hi_i] inside a closed gap
[8j+1, 8j+7] for every reading i.  Nonempty -> a FixedClearCert (Fresh/CarveExclusionCerts.lean,
soundness `fixedClear_clear`) for that sub-box, which gives NoCarve on it (clear point
t = R/8 in [1/8,7/8]).  Empty -> bisect the widest unpinned face.  The sub-boxes partition the
box [PROVISIONAL: covering -- supports "the leaves cover the box"].

Output per box: leaves, depth, or FAIL with the sub-box where the node budget ran out
(those are the exceptions to understand, rule 22).
"""
import json, sys
from fractions import Fraction as F
from multiprocessing import Pool

ONE = F(1)

def good_R(lo, hi):
    """R in [1,7] with R*[lo,hi] in some [8j+1,8j+7]; list of closed intervals."""
    out = []
    j = 0
    while True:
        a = F(8 * j + 1) / lo
        if a > 7:
            break
        b = F(8 * j + 7) / hi
        a2, b2 = max(a, ONE), min(b, F(7))
        if a2 <= b2:
            out.append((a2, b2))
        j += 1
    return out

def inter(A, B):
    out = []
    i = k = 0
    while i < len(A) and k < len(B):
        lo = max(A[i][0], B[k][0]); hi = min(A[i][1], B[k][1])
        if lo <= hi:
            out.append((lo, hi))
        if A[i][1] < B[k][1]:
            i += 1
        else:
            k += 1
    return out

def feasible(faces):
    S = [(ONE, F(7))]
    for lo, hi in faces:
        S = inter(S, good_R(lo, hi))
        if not S:
            return None
    return S

def face(nv):
    return (F(max(2 * nv - 1, 2), 2), F(2 * nv + 1, 2))

def split_box(faces, pinned, budget):
    """DFS; returns (leaves, maxdepth, fail_subbox or None, nodes)."""
    stack = [(faces, 0)]
    leaves = 0; maxd = 0; nodes = 0
    while stack:
        fc, d = stack.pop()
        nodes += 1
        if nodes > budget:
            return leaves, maxd, fc, nodes
        S = feasible(fc)
        if S is not None:
            leaves += 1; maxd = max(maxd, d)
            continue
        # widest unpinned face
        w = -1; idx = -1
        for i, (lo, hi) in enumerate(fc):
            if i in pinned:
                continue
            if hi - lo > w:
                w = hi - lo; idx = i
        if w <= 0:
            return leaves, maxd, fc, nodes  # a point with no fixed clear R: degenerate
        lo, hi = fc[idx]; mid = (lo + hi) / 2
        a = list(fc); a[idx] = (lo, mid)
        b = list(fc); b[idx] = (mid, hi)
        stack.append((a, d + 1)); stack.append((b, d + 1))
    return leaves, maxd, None, nodes

def run(t, budget=4000):
    n = [1] + list(t)
    res = []
    for p in sorted(set(i for i in range(7) if n[i] == 1)):
        faces = [face(v) for v in n]
        faces[p] = (ONE, ONE)
        L, D, fail, nodes = split_box(faces, {p}, budget)
        res.append({"pin": p, "leaves": L, "depth": D, "nodes": nodes,
                    "fail": None if fail is None else [[str(a), str(b)] for a, b in fail]})
    return {"n": n, "cases": res}

if __name__ == "__main__":
    src = sys.argv[1]; lim = int(sys.argv[2]) if len(sys.argv) > 2 else None
    ts = [tuple(json.loads(l)["t"]) for l in open(src)]
    if lim:
        ts = ts[:lim]
    with Pool(10) as pool:
        out = pool.map(run, ts, chunksize=20)
    for r in out:
        print(json.dumps(r))
