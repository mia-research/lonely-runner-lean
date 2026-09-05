from collections import Counter
R.<u> = QQ[]
K = CyclotomicField(24)
for m in (-2,2,0,1,-1):
    rts=[]
    for r,e in (u**4+m*u**2+1).roots(K): rts += [r]*e
    A = Counter(rts); B = Counter([-r for r in rts])
    print("m=%2d  orders=%-16s  closed under u->-u: %s"
          % (m, sorted(r.multiplicative_order() for r in rts), A==B))
