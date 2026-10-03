# exact coordinate ranges (min and max of each rho_i) over the closed fine cell of the 24.38 crosser; exact LP with Farkas certificate
from ceil_lib_v1 import *
X24 = [F(t) for t in ['1', '2752864293769/970238379379', '3691147638604/961559468885', '4851775667488/988103849833', '5240560485773/830842598345', '2806730537001/400961505286', '474233610200591258564537783/19451412054102649094869700']]
x = norm(X24); rows, tags, _ = cell_rows(x)
for idx in range(2, 8):
    lo = min_rho_s_exact(rows, idx)
    hi = maxrho(rows, idx)
    print('rho%d range over closed cell: [%s, %s] = [%.12f, %.12f]; member %.12f' % (idx, lo[0][idx-1] if lo else None, hi[0][idx-1] if hi else None, float(lo[0][idx-1]) if lo else -1, float(hi[0][idx-1]) if hi else -1, float(x[idx-1])))
