import math, random
n = 8
def circ(x):
    f = x - math.floor(x); return min(f, 1-f)

# growth of one move: t_old = (N + delta - 1/n)/d, t_new = (N + 1/n)/d
#   growth = (N + 1/n)/(N + delta - 1/n),   log growth ~ (1/4 - delta)/N  for large N
# So a FLOOR delta >= c_* caps each term by (1/4 - c_*)/N. Convergence of the total is
# governed by sum 1/N_j; a constant factor cannot change it. Check that numerically.
def run(ds, maxsteps=3000):
    m=min(ds); t=1.0/(n*m); rows=[]
    for _ in range(maxsteps):
        iw=[d for d in ds if circ(d*t)<1.0/n]
        if not iw: return rows, True
        best=None
        for d in iw:
            N=round(d*t); nxt=(N+1.0/n)/d
            if nxt>t and (best is None or nxt>best[0]): best=(nxt,d,N)
        if best is None: return rows, False
        nxt,d,N=best
        delta=(d*t-N)+1.0/n
        rows.append((N, delta, nxt/t)); t=nxt
    return rows, False

rng=random.Random(3)
S_actual=[]; S_floor=[]; S_plain=[]
for _ in range(3000):
    ds=sorted(rng.uniform(1,40) for _ in range(7))
    rows,arr=run(ds)
    if not arr or len(rows)<3: continue
    S_actual.append(sum(math.log(g) for _,_,g in rows))
    S_floor.append(sum((0.25-max(d,0.05))/N for N,d,_ in rows))   # pretend c_*=0.05
    S_plain.append(sum(0.25/N for N,d,_ in rows))
import statistics as st
print("over 3,000 arriving cascades, totals per cascade (median):")
print(f"  actual  sum log(growth)          : {st.median(S_actual):.4f}")
print(f"  bound with a floor c_* = 0.05    : {st.median(S_floor):.4f}")
print(f"  bound with no floor at all       : {st.median(S_plain):.4f}")
print()
print("  ratio floor/no-floor :", round(st.median(S_floor)/st.median(S_plain), 3))
print()
print("  A floor multiplies every term by a constant < 1. Convergence of sum (1/4-delta)/N")
print("  is governed by sum 1/N, which the floor does not touch. So even a TRUE floor")
print("  lemma leaves the cap exactly where it was.")
