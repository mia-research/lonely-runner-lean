"""E950: aggregate attain_lp_cert_v4_total.out (certificate rows in roles)."""
import ast
from collections import Counter
c = Counter(); tot = 0
for line in open('attain_lp_cert_v4_total.out'):
    n, k = line.split(' | ', 1); k = ast.literal_eval(k.strip()); n = int(n)
    if k[0] != 'pattern': continue
    tot += n; cells = k[1]; esc = k[3]
    c[('every escape row involves the closer', all('c' in e for e in esc))] += n
    c[('other readings in the escape rows', ''.join(sorted(set(ch for e in esc for ch in e if ch != 'c'))))] += n
    r9 = any(s == 'R=9' for s, kd, ro in cells); p1 = any(s == 'phase 1' for s, kd, ro in cells); p2 = any(s == 'phase 2' for s, kd, ro in cells)
    c[('cell rows at', 'R=9' if r9 else '-', 'phase 1' if p1 else '-', 'phase 2' if p2 else '-')] += n
    c[('every cell row involves reading 1 or the closer', all(('1' in ro or 'c' in ro) for s, kd, ro in cells))] += n
print(tot, 'certificates')
for k, v in sorted(c.items(), key=str): print(v, '|', k)
