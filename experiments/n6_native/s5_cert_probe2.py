import sys
exec(open("s5_cert_v2.py").read().split("lo_a = float")[0])
a0, a1, cap = float(sys.argv[1]), float(sys.argv[2]), int(sys.argv[3])
st, kinds, fails = run((a0, a1, 0.0, 0.5, 0.0, INF, 1.0, INF), 44, cap)
print(f"[{a0},{a1}]: {st} {kinds}")
fails.sort(key=lambda b: (b[1] - b[0]) + (b[3] - b[2]))
for b in fails[:8]: print("  fail", [round(x, 6) for x in b])
