# v3_anchor_child_probe_v1 -- for B (argv1) and a root child (y, j) (argv2, argv3): is the child kept at the root, how many nodes does its subtree have, any cover.
# Same logic as v3_growth_profile_v2.profile, started from the single root child instead of the root.
import sys, time
from fractions import Fraction as F
sys.path.insert(0,'.')
from d0_points_only_k6_v2 import base_system
B=F(sys.argv[1]); Y=int(sys.argv[2]); J=int(sys.argv[3]); h=F(1); lo,hi=F(1),F(7); nread=7
s0=base_system(nread,B); assert s0.add(5,0,F(1,17),True); assert s0.add(6,0,F(1,25),False)
t=s0.copy(); ce=lo
ok1=t.add(Y,0,ce/(8*J-h),True); ok2=ok1 and t.add(0,Y,(8*J+h)/ce,True)
print('B',B,'child',(Y,J),'ENTRY',ok1,'PROGRESS',ok2)
if not ok2: sys.exit()
tf=t.copy(); cov=tf.add(0,Y,(8*J+h)/hi,True); print('covers at depth 1:',cov)
stack=[(t,(Y,J),(ce,0),[(0,Y,J)])]; nodes=0; covers=0; maxd=0
while stack:
    s,cur,prev,chain=stack.pop(); nodes+=1; maxd=max(maxd,len(chain))
    ce,cv=8*cur[1]+h,cur[0]; M=s.M
    xmin=ce/M[0][cv][0]; xmax=ce*M[cv][0][0]; jmax=int((hi*B+h)//8)+1
    for y in range(1,nread):
        uymin=1/M[0][y][0]; uymax=M[y][0][0]
        for j in range(max(1,int((xmin/uymax-h)//8)),min(jmax,int((xmax/uymin+h)//8)+1)+1):
            if (0,y,j) in chain: continue
            u=s.copy()
            if not u.add(y,cv,F(ce)/(8*j-h),True): continue
            if not u.add(cv,y,(8*j+h)/F(ce),True): continue
            pe,pv=prev
            if not u.add(pv,y,(8*j-h)/F(pe),True): continue
            uf=u.copy()
            if uf.add(0,y,(8*j+h)/hi,True): covers+=1; continue
            stack.append((u,(y,j),(ce,cv),chain+[(0,y,j)]))
print('subtree nodes',nodes,'max depth',maxd,'covers',covers)
