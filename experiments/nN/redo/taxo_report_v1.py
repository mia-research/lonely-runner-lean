# taxo_report_v1.py -- class sizes and violations (cascade label vs independent condition label; landing = least clear point).
import pickle
from collections import Counter, defaultdict
from taxo_lib_v1 import CLASSES, is_strip
rows = pickle.load(open('taxo_sample_v1.pkl', 'rb'))
print("sample", len(rows), "distinct arrangements", len(set(tuple(r[1]) for r in rows)))
cnt = Counter(r[2] for r in rows); cnt2 = Counter(r[3] for r in rows)
fam = defaultdict(Counter)
for r in rows: fam[r[0]][r[2]] += 1
print("\nclass sizes (cascade label | condition label)")
for c in CLASSES: print("  %-5s %6d | %6d" % (c, cnt[c], cnt2[c]))
viol = [r for r in rows if r[2] != r[3]]
print("\nclass-label violations (cascade vs conditions):", len(viol))
for r in viol[:5]: print("  ", [str(x) for x in r[1]], r[2], r[3])
v2 = [r for r in rows if not r[4]]
print("landing != least clear point of {1} U exits:", len(v2))
for r in v2[:5]: print("  ", [str(x) for x in r[1]])
print("\nper-family class counts")
for f, c in fam.items(): print("  %-12s %s" % (f, dict(c)))
# structural claims
nm1_nonstrip = [r for r in rows if r[5] == 1 and not is_strip(r[1][r[6][0] - 1])]
print("\nnm==1 with non-strip opener:", len(nm1_nonstrip))
for r in nm1_nonstrip[:5]: print("  ", [str(x) for x in r[1]])
bad_lap = [r for r in rows if r[5] >= 1 and r[9] * r[1][r[6][0]-1] != 8 * r[6][1] + 1]
print("landing != (8j+1)/rho_opener:", len(bad_lap))
bad_w = [r for r in rows if r[8] < 0]; print("negative width:", len(bad_w))
print("nm distribution", sorted(Counter(r[5] for r in rows).items()))
print("empty classes:", [c for c in CLASSES if cnt[c] == 0])
