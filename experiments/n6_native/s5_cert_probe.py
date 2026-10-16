import sys, time, math
exec(open("s5_cert_v2.py").read().split("lo_a = float")[0])
a0, a1, cap = float(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3])
t = time.time()
st, kinds, fails = run((a0, a1, 0.0, 0.5, 0.0, INF, 1.0, INF), 40, cap)
print(f"[{a0},{a1}] cap {cap}: {st} {kinds} in {time.time()-t:.1f}s")
from collections import Counter
c = Counter((round(b[4], 2), b[5] if b[5] == INF else round(b[5], 2), round(b[6], 2), b[7] if b[7] == INF else round(b[7], 2)) for b in fails)
print("fail boxes by (b0,b1,n0,n1):", c.most_common(10))
print("sample fails:", [[round(x, 4) for x in b] for b in fails[:6]])
