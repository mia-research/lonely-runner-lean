# Optimal face of the extremal cell: with rho7 pinned at its exact minimum, the exact range of every other reading (exact LP with exact certificates).
import sys; sys.path.insert(0,'.')
from b12_cell_lib_v1 import *
import pickle
(x0,)=pickle.load(open('b12_A_x0_v1.pkl','rb'))
rows,tags,_=cell_rows(x0)
opt=F(2209,297)
face=rows+[[2209,0,0,0,0,0,-297]]   # rho7 <= opt  (rho7 >= opt already forced)
for k in range(2,7):
    for sign in (1,-1):
        c=[0]*6; c[k-2]=sign
        r=min_rho_s_exact(face,0,cvec=c)
        if r is None: print('rho%d %s: undecided'%(k,'min' if sign==1 else 'max')); continue
        X,lam=r; print('rho%d %s = %s (%.9f)'%(k,'min' if sign==1 else 'max',X[k-1],float(X[k-1])), ' R*sup there =',F(89)/X[6])
