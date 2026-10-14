"""Derive a target-speed region for a four-window AP deformation cover.

All inequalities are affine in arbitrary target coordinates y1,...,y6;
y0=0, y7=199. No cascade is used to construct or verify this region.
The four lap vectors are seeds from the earlier discovery, not a universal
selector. Exact arithmetic proves a whole target box satisfies the region.
"""
from fractions import Fraction as F
from collections import Counter
from window_transport_comparison_v1 import interval, gaps

TARGET = tuple(map(F, (1, 50, 105, 106, 136, 189)))
QS = [(0,0,1,1,1,2,2), (0,1,2,2,3,4,5),
      (0,4,9,9,12,17,18), (0,6,13,13,17,23,25)]
PINS = [(0,4), (0,5), (0,3)]


def add(u, v):
    return tuple(a+b for a,b in zip(u,v))


def mul(c, v):
    return tuple(c*a for a in v)


def const(c):
    return (F(c),)+(F(0),)*6


def value(v, x):
    return v[0]+sum(a*b for a,b in zip(v[1:],x))


def coord(i):
    return const(7) if i == 6 else (F(0),)+tuple(F(7,199) if j==i else F(0) for j in range(6))


def slack(q, i, j):
    A = F((8*q[j]+7)*(i+1)-(8*q[i]+1)*(j+1))
    E = add(mul(8*q[j]+7,coord(i)), mul(-(8*q[i]+1),coord(j)))
    return A,E


def derive():
    constraints = []
    pivots = [slack(q,*p) for q,p in zip(QS,PINS)]
    for n,(A,E) in enumerate(pivots):
        assert A > 0
        # E < 0 gives 0 < tau=A/(A-E) < 1.
        constraints.append((f'pinch {n} before endpoint',mul(-1,E)))
        for which in (n,n+1):
            for i in range(7):
                for j in range(7):
                    C,G = slack(QS[which],i,j)
                    H = add(mul(A,G),mul(-C,E))
                    constraints.append((f'pinch {n} window {which} pair {i+1},{j+1}',H))
    for n in range(2):
        A,E = pivots[n]
        C,G = pivots[n+1]
        # tau_n <= tau_(n+1): C(A-E)-A(C-G)=A G-C E.
        constraints.append((f'ordered pinches {n},{n+1}',add(mul(A,G),mul(-C,E))))
    for i in range(7):
        for j in range(7):
            A,E = slack(QS[-1],i,j)
            constraints.append((f'endpoint pair {i+1},{j+1}',E))
            assert slack(QS[0],i,j)[0] >= 0
    # Preserve distinct, positive, sorted target speeds throughout the box.
    for i in range(7):
        constraints.append((f'target gap {i}',add(coord(i),mul(-1,coord(i-1))) if i else coord(0)))
    return constraints,pivots


def run():
    constraints,pivots=derive()
    ratios=[]
    count=Counter()
    for label,v in constraints:
        margin=value(v,TARGET)
        sensitivity=sum(abs(c) for c in v[1:])
        if not any(v):
            count['identically_zero']+=1
            continue
        assert margin > 0, (label,margin,v)
        count['strict_at_target']+=1
        if sensitivity:
            ratios.append((margin/sensitivity,label))
    limit,limiter=min(ratios)
    radius=limit/2
    # Whole-box proof by the triangle inequality, not just perturbation samples.
    for label,v in constraints:
        if any(v):
            assert value(v,TARGET)-radius*sum(abs(c) for c in v[1:]) > 0
    print('CONSTRAINTS',len(constraints),dict(count))
    print('MAX_COMMON_BOX_RADIUS_FOR_THESE_CONSTRAINTS',limit,'limiter',limiter)
    print('PROVED_CLOSED_BOX_RADIUS',radius)
    print('PINCHES_AT_CENTRE',[str(A/(A-value(E,TARGET))) for A,E in pivots])
    print('Every target (0,y1,...,y6,199) in this six-dimensional box has a')
    print('complete endpoint-subject AP-deformation cover by the four lap vectors.')
    # Separate regression checks of the interval-cover implementation at 64 corners.
    for mask in range(64):
        x=[y+(radius if mask>>i&1 else -radius) for i,y in enumerate(TARGET)]
        a=list(map(F,range(1,8)))
        d=[F(7,199)*y for y in x]+[F(7)]
        windows=[interval(a,[v-u for u,v in zip(a,d)],q) for q in QS]
        assert all(w is not None for w in windows)
        assert not gaps(windows)
    print('CORNER_REGRESSIONS',64,'passed (not the basis of the whole-box proof)')


if __name__ == '__main__':
    run()
