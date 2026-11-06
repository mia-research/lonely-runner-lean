# E826: steering search (floats) for a counterexample to FrontierCarveCap: six sorted readings 1 <= r2 <= ... <= r6 < r7, 47/7 < r6 < 7, 15 < r7, carving every R in [1,7] (some reading r and integer j with 8j-1 < r R < 8j+1), with 31/r6 > 73/r7.  Seeded.
import numpy as np, sys
rng = np.random.default_rng(int(sys.argv[1]))
fine = np.linspace(1, 7, 24001)[None, :]
coarse = np.linspace(1, 7, 700)[None, :]
def covered(rs, R):
    # rs shape (n, 6); returns (n, len(R)) boolean: some reading has ρR within <1 of a multiple of 8
    x = rs[:, :, None] * R[None, :, :][:, :, :]  # (n,6,m)
    return (np.abs(x / 8 - np.round(x / 8)) < 1 / 8).any(axis=1)
n_total = 0; carved = 0; viol = []
for _ in range(int(sys.argv[2])):
    n = 20000
    r6 = rng.uniform(47 / 7, 7, n); r7 = rng.uniform(15, 17.6, n)
    mid = np.sort(rng.uniform(1, 1, (n, 4)) + rng.uniform(0, 1, (n, 4)) * (r6[:, None] - 1), axis=1)
    rs = np.concatenate([mid, r6[:, None], r7[:, None]], axis=1)
    c = covered(rs, coarse).all(axis=1)
    idx = np.where(c)[0]
    n_total += n
    if len(idx):
        cf = covered(rs[idx], fine).all(axis=1)
        for i in idx[cf]:
            carved += 1
            if 31 / r6[i] > 73 / r7[i] + 1e-12: viol.append(tuple(rs[i]))
print('samples', n_total, 'carves of [1,7] (grid, 24001 points)', carved, 'carves with 31/r6 > 73/r7:', len(viol))
for v in viol[:5]: print(v)
