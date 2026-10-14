"""Sufficient condition:  R < 1 + 2*Sigma  where Sigma = sum over moves of 1/u(setter).
So  Sigma < 3/2  implies  R < 4.   What is max Sigma over realisable words?

Sigma is evaluated at the same LP configuration that minimises the final setter's reading
(the one that maximises R), so this is the adversary's own choice, not a separate optimum.
"""
import sys, importlib.util
from fractions import Fraction as F
_ARGV = list(sys.argv)
spec = importlib.util.spec_from_file_location("cert", "experiments/n8/order5_certificate_v3.py")
cert = importlib.util.module_from_spec(spec); sys.argv = ["cert"]; spec.loader.exec_module(cert)
n = 5
S = int(_ARGV[1]) if len(_ARGV) > 1 else 14
L = (4 * S - 1) // 5
best = [None, None, None]   # [max Sigma, word, R]
bestR = [None, None, None]

def extend(word):
    cons = cert.constraints(word)
    tau = cert.opt(cons, 3, 'max', S, True)
    if tau is None or tau <= 0: return
    x, Q = word[-1]
    m = cert.opt(cons, x - 1, 'min', S, False) if x > 0 else F(1)
    if m is not None and m > 0:
        R = F(n * Q + 1) / m
        us = {}
        ok = True
        for xx in set(a for a, _ in word):
            uu = cert.opt(cons, xx - 1, 'min', S, False)
            if uu is None or uu <= 0: ok = False; break
            us[xx] = uu
        if ok:
            Sig = sum(F(1) / us[a] for a, _ in word)
            if best[0] is None or Sig > best[0]: best[0], best[1], best[2] = Sig, list(word), R
            if bestR[0] is None or R > bestR[0]: bestR[0], bestR[1], bestR[2] = R, list(word), Sig
    if len(word) >= 3 * L: return
    used = {xx: QQ for xx, QQ in word}
    for nx in (1, 2, 3):
        for nq in range(used.get(nx, 0) + 1, L + 1):
            extend(word + [(nx, nq)])

for x in (1, 2, 3):
    for q in range(1, L + 1):
        extend([(x, q)])

print(f"order 5, S = {S}, L = {L}")
print(f"max Sigma = {best[0]} = {float(best[0]):.4f}   (target: < 3/2 = 1.5)")
print(f"   at word {best[1]}   its R = {best[2]} = {float(best[2]):.4f}")
print(f"   => R bound 1 + 2*Sigma = {float(1 + 2*best[0]):.4f}")
print()
print(f"max R     = {bestR[0]} = {float(bestR[0]):.4f}   at {bestR[1]}")
print(f"   its Sigma = {bestR[2]} = {float(bestR[2]):.4f}   bound 1+2*Sigma = {float(1+2*bestR[2]):.4f}")
print()
print(f"VERDICT: Sigma < 3/2 on this range?  {best[0] < F(3,2)}")
