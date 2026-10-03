# ceil library: exact helpers on top of b12_cell_lib_v1 (imported, not edited).
import sys; sys.path.insert(0, '.')
from b12_cell_lib_v1 import *
X7 = [F(1), F(9772258744003239, 3382348542792500), F(33037361603047, 8543434945135), F(18504041127465, 3841551499939),
      F(35095954505037, 5541903129092), F(29598145793981, 4300260877376), F(141630707042209, 8738350240737)]
def crosses(x):
    st, R = path(norm(x))
    return any(s['setter'] == 0 for s in st) and R > 7, st, R
def maxrho(rows, idx):
    """exact max of rho_{idx} (2..7) over closed cell: min of -rho; returns (X, lam dict) or None, verified exactly."""
    c = [F(0)] * 6; c[idx - 2] = F(-1)
    return min_rho_s_exact(rows, idx, cvec=c)
def tight(rows, X):
    return [i for i, a in enumerate(rows) if row_val(a, X) == 0]
def dedupe_rows(rows, idx):
    import math
    out = {}
    for i in idx:
        a = rows[i]; g = math.gcd(*[abs(t) for t in a]); out.setdefault(tuple(t // g for t in a), i)
    return list(out.values())
