# E824: chain length against 1 + (#gaps of the first window) + (sum of fillers per gap); the gaps that need 2 fillers.
import pickle
from fractions import Fraction as F
gp = pickle.load(open('chain_gaps_v1.pkl', 'rb'))
cp = {r[0]: r for r in pickle.load(open('chain_pieces_v1.pkl', 'rb'))}
eq = lt = gt = 0; diffs = []
for core, A, y0, ms in gp:
    n = len(cp[core][3]); pred = 1 + sum(1 + m for k, b, a, m in ms)
    if n == pred: eq += 1
    elif n < pred: lt += 1; diffs.append((core, n, pred))
    else: gt += 1; diffs.append((core, n, pred))
print('cores', len(gp), 'chain == 1 + sum(1 + m_k):', eq, '; chain < that:', lt, '; chain > that:', gt)
for d in diffs[:12]: print(d)
print('gaps needing 2 fillers:')
for core, A, y0, ms in gp:
    for k, b, a, m in ms:
        if m == 2: print(core, 'lap k', k, 'gap', (b, a), 'width', a - b, 'A', A, 'y0', y0)
