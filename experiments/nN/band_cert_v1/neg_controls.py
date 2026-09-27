"""Negative controls for verify.py: each corrupted certificate must be REJECTED."""
import pickle, copy, subprocess
c = pickle.load(open("cert15.pkl", "rb"))
def run(cc, name):
    pickle.dump(cc, open("tmp_neg.pkl", "wb"))
    out = subprocess.run(["python3", "verify.py", "tmp_neg.pkl"], capture_output=True, text=True)
    last = (out.stdout + out.stderr).strip().splitlines()[-1]
    print(f"{name:55s} -> {last}")
# 1. R range shrunk to [1,7] u [9,9]
cc = copy.deepcopy(c); cc["Rhi"] = 9.0; run(cc, "Rhi = 9 (claim false for [1,9])")
# 2. R range shrunk to [1,7] u [9,14]
cc = copy.deepcopy(c); cc["Rhi"] = 14.0; run(cc, "Rhi = 14")
# 3. drop one level-5 cell (partition gap)
cc = copy.deepcopy(c); a, b, t = cc["top"][10]; t[0][2].pop(1); run(cc, "drop a level-5 cell")
# 4. top cells do not reach 9
cc = copy.deepcopy(c); cc["top"] = cc["top"][:-1]; run(cc, "drop last top cell")
# 5. collapse a level-2 node that the search had split (>= 2 cells) into the single cell [1,b]
cc = copy.deepcopy(c)
def find_split_l2(node, L):
    if L == 2:
        return node if len(node) >= 2 else None
    for a, b, sub in node:
        r = find_split_l2(sub, L - 1)
        if r is not None: return r
    return None
for top in cc["top"]:
    n = find_split_l2(top[2], 6)
    if n is not None:
        print("   collapsing level-2 node with", len(n), "cells over", (n[0][0], n[-1][1]))
        n[:] = [(n[0][0], n[-1][1], None)]; break
run(cc, "collapse a split level-2 node to one cell")
