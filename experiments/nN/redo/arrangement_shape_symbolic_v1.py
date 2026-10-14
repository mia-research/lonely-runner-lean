"""Symbolic input-space reduction. No census of speed sets or cascade histories.

The six variables are x1,...,x6 with 0<x1<...<x6<7. Generate the unique
reference-grid walls c*(xj-xi)=integer for c in {1,3,5,7}, x0=0,x7=7.
"""
from fractions import Fraction as F
from itertools import combinations
import json
import unittest


def normalize(v):
    w=sorted(map(F,v))
    assert len(w)==8 and len(set(w))==8
    A=w[0]
    D=(w[-1]-A)/7
    return tuple((x-A)/D for x in w)


def walls():
    out={}
    for i,j in combinations(range(8),2):
        if (i,j)==(0,7):
            continue  # This separation is fixed at seven, not a variable wall.
        co=[0]*6
        if 1<=j<=6:
            co[j-1]+=1
        if 1<=i<=6:
            co[i-1]-=1
        const=7 if j==7 else 0
        for c in (1,3,5,7):
            for q in range(1,7*c):
                rhs=F(q,c)-const
                coef=list(co)
                if next(x for x in coef if x)<0:
                    coef=[-x for x in coef]
                    rhs=-rhs
                out.setdefault((tuple(coef),rhs),[]).append((i,j,c,q))
    return out


def distance(y):
    r=y%1
    return min(r,1-r)


def reference_clear(y):
    k=y.__floor__()
    r=k%8
    return 1<=r<=6 or (r==7 and y==k)


class Tests(unittest.TestCase):
    def test_ap_scale_and_shift(self):
        tiny=[F(i,100000) for i in range(1,9)]
        huge=[F(1000000*i) for i in range(1,9)]
        self.assertEqual(normalize(tiny),normalize(huge))
        self.assertEqual(normalize(tiny),tuple(map(F,range(8))))
        self.assertEqual(normalize([13+17*x for x in tiny[::-1]]),normalize(tiny))

    def test_six_factors(self):
        x=normalize([27,70,107,137,159,188,344,393])
        g=[b-a for a,b in zip(x,x[1:])]
        self.assertTrue(all(t>0 for t in g))
        self.assertEqual(sum(g),7)
        self.assertEqual(tuple([F(0)]+[sum(g[:i]) for i in range(1,8)]),x)

    def test_symbolic_wall_count(self):
        levels={F(q,c) for c in (1,3,5,7) for q in range(1,7*c)}
        self.assertEqual(len(levels),90)
        self.assertEqual(len(walls()),1890)

    def test_reference_classifier(self):
        for k in range(50):
            for e in (F(0),F(1,7),F(1,2),F(6,7)):
                y=F(k)+e
                self.assertEqual(reference_clear(y),distance(y/8)>=F(1,8))

    def test_modulo_requires_time_context(self):
        self.assertEqual(distance(F(1,8)),distance(F(9,8)))
        self.assertNotEqual(distance(F(1,16)),distance(F(9,16)))


if __name__=='__main__':
    import sys
    if '--test' in sys.argv:
        unittest.main(argv=[__file__])
    else:
        w=walls()
        print(json.dumps({'free_real_factors':6,'positive_speed_gaps':7,
            'gap_sum':7,'unit_reference_classes':[1,3,5,7],
            'distinct_threshold_levels':90,'distinct_reference_hyperplanes':len(w),
            'interpretation':'Finite reference-grid cell structure, not a proved finite quotient of cascade histories.'},indent=2))
