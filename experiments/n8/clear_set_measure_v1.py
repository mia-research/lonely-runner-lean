from fractions import Fraction as F
# exact clear set of t in (0,1] for a difference set: {t : ||d t|| >= 1/8 for all d}
# boundaries are at t = (k +- 1/8)/d ; between consecutive boundaries the predicate is constant.
def clear_measure(ds, T=1):
    bs={F(0),F(T)}
    for d in ds:
        k=0
        while True:
            for off in (F(1,8),F(-1,8)):
                x=(F(k)+off)/d
                if 0<x<=T: bs.add(x)
            if F(k)/d>T: break
            k+=1
    bs=sorted(bs); tot=F(0); pts=[]
    for a,b in zip(bs,bs[1:]):
        mid=(a+b)/2
        ok=all(min((d*mid)%1,1-(d*mid)%1)>=F(1,8) for d in ds)
        if ok: tot+=b-a
    for x in bs:
        if 0<x<=T and all(min((d*x)%1,1-(d*x)%1)>=F(1,8) for d in ds): pts.append(x)
    return tot,pts
for name,ds in [("AP 1..7",[1,2,3,4,5,6,7]),
                ("(2,6,8,9,11,14,15)",[2,6,8,9,11,14,15]),
                ("(2,3,5,7,8,13,16)",[2,3,5,7,8,13,16]),
                ("28-move {49,205,...}",[49,205,234,256,286,323,366])]:
    ds=[F(x) for x in ds]
    m,pts=clear_measure(ds,T=2)
    print(f"{name:24s} clear measure on (0,2] = {m}   isolated clear points found: {len(pts)}")
    if m==0: print(f"{'':24s}   -> the clear set is FINITE: {[str(p) for p in pts[:8]]}")
