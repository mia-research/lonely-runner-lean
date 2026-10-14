"""Grouped by the variable that R actually depends on: the FINAL setter's lap Q_f.

R = (5 Q_f + 1) / u_{x_f}.  Two regimes:
  * x_f == x1 (final setter is also the first):  the first-move constraint pins
        u_{x1} >= 5 Q1 - 1,   so   R <= (5 Q_f + 1)/(5 Q1 - 1),  which is < 4 iff Q_f < 4 Q1 - 1.
  * x_f != x1: the first-move constraint does not apply to x_f, so the bound must come from the
        chain constraints.
Reports the best R at each final lap, in each regime, with the witnessing word.
"""
import sys, importlib.util
_ARGV = list(sys.argv)
from fractions import Fraction as F
from collections import defaultdict
spec = importlib.util.spec_from_file_location("cert", "experiments/n8/order5_certificate_v3.py")
cert = importlib.util.module_from_spec(spec); sys.argv = ["cert"]; spec.loader.exec_module(cert)

S = int(_ARGV[1]) if len(_ARGV) > 1 else 18
L = (4 * S - 1) // 5
best = defaultdict(lambda: [None, None, None])   # key (Qf, same) -> [R, word, u]

def extend(word):
    cons = cert.constraints(word)
    tau = cert.opt(cons, 3, 'max', S, True)
    if tau is None or tau <= 0: return
    x, Q = word[-1]
    m = cert.opt(cons, x - 1, 'min', S, False) if x > 0 else F(1)
    if m is not None and m > 0:
        R = F(5 * Q + 1) / m
        key = (Q, word[0][0] == x)
        if best[key][0] is None or R > best[key][0]: best[key] = [R, list(word), m]
    if len(word) >= 3 * L: return
    used = {xx: QQ for xx, QQ in word}
    for nx in (1, 2, 3):
        for nq in range(used.get(nx, 0) + 1, L + 1):
            extend(word + [(nx, nq)])

for x in (1, 2, 3):
    for q in range(1, L + 1):
        extend([(x, q)])

print(f"order 5, S = {S}, L = {L}   (R = (5Qf+1)/u_xf)")
print(f"{'Qf':>4} {'same?':>6} {'best R':>10} {'u_xf':>9} {'Q1':>3}  word")
overall = max(v[0] for v in best.values() if v[0] is not None)
for (Qf, same) in sorted(best):
    R, w, m = best[(Qf, same)]
    if R is None: continue
    mark = "  <== OVERALL MAX" if R == overall else ("  <-- R >= 4" if R >= 4 else "")
    print(f"{Qf:>4} {str(same):>6} {float(R):>10.4f} {float(m):>9.4f} {w[0][1]:>3}  {w}{mark}")
print()
print(f"overall max R = {overall} = {float(overall):.4f}")
