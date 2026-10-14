"""Why does the extremal word use only laps <= 6, while the lap bound L grows with S?

The certificate's sup R = 31/9 is attained at [(1,2),(2,1),(1,3),(3,1),(2,2),(1,6)] for every
ratio bound S from 10 to 26, with margin tau = 132/4165 fixed from S = 14.  If the sup over
words whose maximum lap exceeds some fixed M is provably below 31/9, the enumeration truncates
at M and the certificate closes for UNBOUNDED ratio.

This instruments the certificate's own LP: for each realisable word, record its maximum lap and
its sup R, and report the best R achievable at each maximum lap.
"""
import sys, importlib.util
_ARGV = list(sys.argv)
from fractions import Fraction as F
from collections import defaultdict

spec = importlib.util.spec_from_file_location("cert", "experiments/n8/order5_certificate_v3.py")
cert = importlib.util.module_from_spec(spec)
sys.argv = ["cert"]
spec.loader.exec_module(cert)

S = int(_ARGV[1]) if len(_ARGV) > 1 else 18
L = (4 * S - 1) // 5
best_by_maxlap = defaultdict(lambda: [None, None])

def extend(word):
    cons = cert.constraints(word)
    tau = cert.opt(cons, 3, 'max', S, True)
    if tau is None or tau <= 0: return
    x, Q = word[-1]
    m = cert.opt(cons, x - 1, 'min', S, False) if x > 0 else F(1)
    if m is not None and m > 0:
        R = F(5 * Q + 1) / m
        ml = max(q for _, q in word)
        cur = best_by_maxlap[ml]
        if cur[0] is None or R > cur[0]: best_by_maxlap[ml] = [R, list(word)]
    if len(word) >= 3 * L: return
    used = {xx: QQ for xx, QQ in word}
    for nx in (1, 2, 3):
        for nq in range(used.get(nx, 0) + 1, L + 1):
            extend(word + [(nx, nq)])

for x in (1, 2, 3):
    for q in range(1, L + 1):
        extend([(x, q)])

print(f"order 5, ratio bound S = {S}, lap bound L = {L}")
print(f"{'max lap':>8} {'best sup R':>14} {'float':>8}  extremal word")
for ml in sorted(best_by_maxlap):
    R, w = best_by_maxlap[ml]
    flag = "  <-- overall max" if R == max(v[0] for v in best_by_maxlap.values()) else ""
    print(f"{ml:>8} {str(R):>14} {float(R):>8.4f}  {w}{flag}")
