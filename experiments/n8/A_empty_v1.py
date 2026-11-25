"""E950: the 31 class-X readings with A empty (E949 item 5): which earlier six-window empties A, and how (exact).
L-type: that window is at least 1/(4 lo) long, so no zone of any position between the neighbours covers it.
P-type: its own pass set inside the neighbours is empty.  Else: its pass set misses the positions that passed the windows before it."""
exec(open('attain_pin_v2.py').read().split("step, off = int")[0])
from collections import Counter
c = Counter()
for idx, R0, closers, cls, att in rows:
    rs = sorted(Fr(x) for x in rec[idx][1]); T, path = cascade(rs, E)
    for k in range(1, 7):
        if cls[k + 1] != 'X': continue
        six = rs[:k] + rs[k + 1:]; lo = rs[k - 1]
        ws = windows(six, E, T1); n = next(i for i, (x, y, z) in enumerate(ws) if x <= T <= y); a, b = ws[n][0], ws[n][1]
        hi = rs[k + 1] if k < 6 else ((a + b) / (b - a) + 1) / (8 * b) + 1
        A = [(lo, hi)]; dead = None
        for jj in range(n):
            A2 = passes_in(ws[jj][0], ws[jj][1], A)
            if not A2: dead = jj; break
            A = A2
        if dead is None: continue
        x, y = ws[dead][0], ws[dead][1]
        how = 'L-type' if y - x >= Fr(1, 4) / lo else ('P-type' if not passes(x, y, lo, hi) else 'misses the earlier survivors')
        c[('A empty at earlier window', dead, 'R ~ %.1f' % float(8 * x), how, 'reading', k + 1)] += 1
        c[('A empty', how)] += 1
for kk, v in sorted(c.items(), key=str): print(v, '|', kk)
