"""The move-count efficiency alpha, and whether the bootstrap closes.

Bootstrap:  R < 1 + sum over setters of 2*m_x/u_x,  where m_x = number of moves by setter x.
If R < B then setter x can only occupy laps Q <= u_x*B/n, so its NOMINAL budget is u_x*B/n.
Write   alpha_x = m_x / (u_x*B/n)   (the fraction of the budget actually used).
Then contribution <= 2*alpha_x*B/n and  B = 1 + 2*k*alpha*B/n  has a fixed point below 4 iff

        2*k*alpha/n < 3/4        at n=5, k=3 setters:   alpha < 5/8 = 0.625.

At n=3, k=1: alpha < 9/8 -- always true, which is why order 3 closes.
At n=8, k=6: alpha < 1/2.
Measured here at B = 4 (n=5) over every realisable word of the certificate.
"""
import sys, importlib.util
from fractions import Fraction as F
from collections import Counter
_ARGV = list(sys.argv)
spec = importlib.util.spec_from_file_location("cert", "experiments/n8/order5_certificate_v3.py")
cert = importlib.util.module_from_spec(spec); sys.argv = ["cert"]; spec.loader.exec_module(cert)
n = 5; B = F(4)
S = int(_ARGV[1]) if len(_ARGV) > 1 else 14
L = (4 * S - 1) // 5
worst = [F(0), None, None]     # max alpha over all setters of all realisable words
worstR = [F(0), None]
hist = Counter()

def extend(word):
    cons = cert.constraints(word)
    tau = cert.opt(cons, 3, 'max', S, True)
    if tau is None or tau <= 0: return
    x, Q = word[-1]
    m = cert.opt(cons, x - 1, 'min', S, False) if x > 0 else F(1)
    if m is not None and m > 0:
        R = F(n * Q + 1) / m
        if R > worstR[0]: worstR[0], worstR[1] = R, list(word)
        cnt = Counter(a for a, _ in word)
        for xx, mx in cnt.items():
            ux = cert.opt(cons, xx - 1, 'min', S, False)
            if ux is None or ux <= 0: continue
            budget = ux * B / n
            if budget > 0:
                al = F(mx) / budget
                hist[min(int(al * 20), 40)] += 1
                if al > worst[0]: worst[0], worst[1], worst[2] = al, list(word), (xx, mx, ux)
    if len(word) >= 3 * L: return
    used = {xx: QQ for xx, QQ in word}
    for nx in (1, 2, 3):
        for nq in range(used.get(nx, 0) + 1, L + 1):
            extend(word + [(nx, nq)])

for x in (1, 2, 3):
    for q in range(1, L + 1):
        extend([(x, q)])

print(f"order 5, S = {S}, L = {L}, bootstrap bound B = 4, threshold alpha < 5/8 = 0.625")
print(f"max alpha observed = {worst[0]} = {float(worst[0]):.4f}")
print(f"   at word {worst[1]}   setter x={worst[2][0]} made {worst[2][1]} moves with u = {worst[2][2]}")
print(f"   -> bootstrap closes?  {'YES' if worst[0] < F(5,8) else 'NO -- alpha exceeds 5/8'}")
print()
print(f"extremal R word {worstR[1]}  R = {worstR[0]} = {float(worstR[0]):.4f}")
print()
print("alpha distribution (bucket = floor(20*alpha)):")
for b in sorted(hist):
    print(f"   alpha in [{b/20:.2f},{(b+1)/20:.2f}) : {hist[b]}")
