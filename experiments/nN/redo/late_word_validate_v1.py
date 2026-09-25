"""Validate late_word_certificate_v1's rows: every real late climb must lie strictly inside its own word's
polytope (all rows strict at the real readings, and the LP margin tau > 0).  Exact."""
import re, ast
from fractions import Fraction as F
from math import floor
from arrangement_lib import readings, nd
from late_word_certificate_v1 import rows_of, lp, NV

def word_of(ds):
    dmin = min(ds); s = [F(d, dmin) for d in sorted(ds)]; t = F(1, 8 * dmin); w = []
    while True:
        way = [d for d in ds if nd(d * t) < F(1, 8)]
        if not way: return s, w
        cand = {d: (F(floor(d * t - F(1, 8)) + 1) + F(1, 8)) / d for d in way}
        d = max(cand, key=lambda x: cand[x]); tn = cand[d]
        w.append((sorted(ds).index(d) + 1, floor(d * tn)))
        if 8 * dmin * tn > 7: return s, w       # stop at the exit into (7,9)
        t = tn

cases = []
for line in open('late_event_S9_search_v1.out'):
    m = re.search(r'LATE seed \d+: .* V=(\[[^\]]*\]) subject (\d+)', line)
    if m: cases.append((ast.literal_eval(m.group(1)), int(m.group(2))))
cases += [([27,70,107,137,159,188,344,393], 393), ([1,31,75,97,128,160,176,225], 1),
          ([1,1975,5265,6910,8737,9589,11845,15135], 1), ([109,154,234,273,313,337,390,469], 109)]
ok = bad = skip = 0; words = set()
for V, sub in cases:
    ds = readings(V, V.index(sub))
    if len(ds) < 7: skip += 1; continue
    s, w = word_of(ds); words.add(tuple(w))
    B = F(max(s)) + 1
    rows = rows_of(w, B, F(1))
    jL, ML = w[-1]; ex = [F(0)] * NV; ex[jL - 2] = F(7); rows_x = rows + [(ex, F(1), F(8 * ML + 1))]
    strict = all(sum(a[i] * (s[i + 1]) for i in range(NV)) < b if at else sum(a[i] * s[i + 1] for i in range(NV)) <= b
                 for a, at, b in rows_x)
    tau = lp(rows_x, 'tau', True)
    if strict and tau is not None and tau > 0: ok += 1
    else: bad += 1; print("FAIL", V, sub, w, strict, tau)
print(f"late climbs inside their own word polytope, strictly: {ok}; failures {bad}; skipped (tied readings) {skip}")
print(f"distinct words among them: {len(words)}; lengths {sorted(len(w) for w in words)}")
