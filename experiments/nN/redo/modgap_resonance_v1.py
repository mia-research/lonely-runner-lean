"""modgap_resonance_v1 (2026-10-06): owner's reading (2026-10-06): the unexplained landings are relations of the readings with
themselves (resonance / destructive resonance).  Tested on the 752 'class=not understood' lines of modgap_rule_v1_exceptions.out.
Resonance at modulus q = a relation among the residues that holds mod q but NOT as integers (integer relations hold at every
modulus and are no property of q):  W2: d_i = k d_j (mod q), k in {2,3}, d_i != k d_j;  W3: d_i + d_j = d_k (mod q) or
d_i - d_j = d_k (mod q) with the integer relation false.  Count per set at the landing modulus q_A, against the same count
at every other residue isolation a/q (gcd 1, q <= 2 d_max, q != q_A, a/q <= 2) of the SAME set (matched control).
Exact integers.  Output: per-set count at q_A, control mean, and whether q_A exceeds the control maximum / mean.
"""
import re, ast, itertools, collections, sys
sys.path.insert(0, '.')
from fractions import Fraction as F
from math import gcd
from modgap_lib_v1 import is_iso
def res(S, q):
    n = 0
    for i, j in itertools.permutations(range(7), 2):
        di, dj = S[i], S[j]
        for k in (2, 3):
            if (di - k * dj) % q == 0 and di != k * dj: n += 1
    for i, j, k in itertools.permutations(range(7), 3):
        a, b, c = S[i], S[j], S[k]
        if i < j and (a + b - c) % q == 0 and a + b != c: n += 1
        if (a - b - c) % q == 0 and a - b != c: n += 1
    return n
out = open('modgap_resonance_v1.out', 'w'); out.write(__doc__ + "\n")
rows = []
for line in open('modgap_rule_v1_exceptions.out'):
    if 'class=not understood' not in line: continue
    S = ast.literal_eval(re.search(r' S=(\([^)]*\))', line).group(1))
    qA = F(re.search(r' qA=(\d+/\d+|\d+)', line).group(1))
    rows.append((line.split()[0], S, qA))
cnt = collections.Counter(); ex = []
for pop, S, qA in rows:
    a, q = qA.numerator, qA.denominator
    here = res(S, q)
    ctrl = [res(S, qq) for qq in range(2, 2 * S[-1] + 1) if qq != q for aa in range(1, 2 * qq + 1)
            if gcd(aa, qq) == 1 and is_iso(S, aa, qq)]
    ctrl = ctrl[:200]
    if not ctrl: cnt['no control'] += 1; continue
    mean = F(sum(ctrl), len(ctrl)); mx = max(ctrl)
    cnt[('above control max', here > mx)] += 1; cnt[('above control mean', here > mean)] += 1
    cnt[('zero at q_A', here == 0)] += 1
    if len(ex) < 25: ex.append((pop, S, qA, here, float(mean), mx, len(ctrl)))
out.write("exceptions read: %d (%s)\n" % (len(rows), dict(collections.Counter(p for p, _, _ in rows))))
for k, v in sorted(cnt.items(), key=str): out.write("%s: %d\n" % (k, v))
out.write("first 25 (pop, S, q_A, count at q_A, control mean [float, display only], control max, controls):\n")
for e in ex: out.write("  %s\n" % (e,))
out.close(); print(open('modgap_resonance_v1.out').read()[len(__doc__):])
