"""Forced relabelling after a failed doubled-window intersection.

At the earliest upper deadline U, every feasible candidate time <=U has lap
labels <=floor(d_i*U-1/8). Replace the incompatible labels by these maxima.
The supplied OLD clear event is a lower witness: this finite diagnostic never
claims a new event must exist. Reaching the old window is reported separately.
"""
from fractions import Fraction as F
from math import floor
from collections import Counter
import random
from window_transport_comparison_v1 import interval,path,clear
from double_backtrack_selector_v1 import candidate


def relabel(ds,old,t,initial,cap=1000):
    p=initial
    trace=[]
    for step in range(cap):
        L=max((k+F(1,8))/d for k,d in zip(p,ds))
        U=min((k+F(7,8))/d for k,d in zip(p,ds))
        assert all(k>=j for k,j in zip(p,old))
        assert U>=t
        if L<=U:
            assert all(clear(d,U) for d in ds)
            return p,(L,U),trace
        next_p=tuple(floor(d*U-F(1,8)) for d in ds)
        assert all(j<=n<=k for j,n,k in zip(old,next_p,p))
        assert sum(next_p)<sum(p)
        closers=tuple(i+1 for i,(d,k) in enumerate(zip(ds,p)) if (k+F(7,8))/d==U)
        changed=tuple(i+1 for i,(k,n) in enumerate(zip(p,next_p)) if n<k)
        trace.append((p,U,closers,changed,next_p))
        p=next_p
    raise RuntimeError('diagnostic cap; no coverage conclusion')


def run():
    rng=random.Random(179)
    targets=[(0,1,50,105,106,136,189,199),(0,99,200,300,400,500,600,700)]
    targets += [(0,)+tuple(sorted(rng.sample(range(1,201),7))) for _ in range(12)]
    counts=Counter(); steps=Counter(); first=None; no_progress=None; triple_failure=None
    for target in targets:
        xs=[F(7)*(x-target[0])/(target[-1]-target[0]) for x in target]
        for subject in range(8):
            _,windows,_=path(target,subject)
            ids=[j for j in range(8) if j!=subject]
            a=[F(abs(j-subject)) for j in ids]
            b=[abs(xs[j]-xs[subject])-v for j,v in zip(ids,a)]
            for q,(lo,tau) in windows.items():
                if not lo<tau<1:continue
                ds=[d+tau*v for d,v in zip(a,b)]
                t=max(F(8*k+1,8)/d for k,d in zip(q,ds))
                initial,T,back,need,_=candidate(ds,q,t)
                if need<=back:continue
                p,(L,U),trace=relabel(ds,q,t,initial)
                w=interval(a,b,p)
                counts['failed_double_cases']+=1; steps[len(trace)]+=1
                if w[0]<=tau<w[1]:counts['right_extension']+=1
                else:
                    if p==q:
                        counts['returns_old_labels']+=1
                        if no_progress is None:no_progress=(target,subject,q,str(tau))
                    else:counts['different_labels_without_right_extension']+=1
                    # Tripling clears EVERY original middle-phase blocker of
                    # doubling: [7/16,9/16] maps to phase [5/16,11/16].
                    initial3=tuple(floor(3*d*t-F(1,8)) for d in ds)
                    p3,band3,trace3=relabel(ds,q,t,initial3)
                    w3=interval(a,b,p3)
                    if w3[0]<=tau<w3[1]:counts['triple_recovers_remaining']+=1
                    else:
                        counts['triple_still_no_extension']+=1
                        if triple_failure is None:triple_failure=(target,subject,q,str(tau),p3)
                        initial5=tuple(floor(5*d*t-F(1,8)) for d in ds)
                        p5,band5,trace5=relabel(ds,q,t,initial5)
                        w5=interval(a,b,p5)
                        counts['five_recovers_remaining' if w5[0]<=tau<w5[1]
                               else 'five_still_no_extension']+=1
                if first is None:first=(target,subject,q,tau,p,(L,U),w,trace)
    print('COUNTS',dict(counts),'RELABEL_STEPS',dict(sorted(steps.items())))
    print('FIRST_NO_PROGRESS',no_progress)
    print('FIRST_TRIPLE_FAILURE',triple_failure)
    target,subject,q,tau,p,band,w,trace=first
    print('FIRST_REPAIR',target,'subject',subject,'old',q,'pinch',tau)
    for old,U,closers,changed,new in trace:
        print(' deadline',U,'closers',closers,'forced earlier labels',changed,'new',new)
    print(' selected',p,'time band',tuple(map(str,band)),'parameter band',tuple(map(str,w)))


if __name__=='__main__':run()
