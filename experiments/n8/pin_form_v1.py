# E951: number form of the rigid pins, from pin_ident_v1_total.out (exact strings).  For each listed pin: q_P and q_A
# as (8a+-1)/(8b+-1) (pin_ident_v1.pm8), the sign pattern, and whether q_A/q_P > 1 (side below: P under A).
import re, ast
from fractions import Fraction as Fr
from collections import Counter
c = Counter(); tot = 0
for line in open('pin_ident_v1_total.out'):
    if "'q_A/q_P'" not in line: continue
    n, rest = line.split(' | ', 1); n = int(n); t = ast.literal_eval(rest.strip())
    r, qP, qA = Fr(t[2]), t[4], t[6]
    def sig(s):
        a, b = map(int, s.split('/')); return ('+' if a % 8 == 1 else '-') + ('+' if b % 8 == 1 else '-'), a, b
    sP, aP, bP = sig(qP); sA, aA, bA = sig(qA)
    c[('q_A/q_P > 1', r > 1, 'q_P signs (num, den)', sP, 'q_A signs', sA)] += n; tot += n
for k, v in sorted(c.items(), key=str):
    if v: print(v, '|', k)
print(tot, 'rigid-pin escape rows')
