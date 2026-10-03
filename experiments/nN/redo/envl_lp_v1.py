# per-signature LP for per-rank infimum/supremum, with exact vertex verification
import sys, time, pickle
sys.path.insert(0,'.')
from envl_common_v1 import *
import numpy as np
from scipy.optimize import linprog
def lp(A,r,sense):
    Aub=np.array([c for c,b in A],float); bub=np.array([b for c,b in A],float)
    Aeq=np.zeros((1,7)); Aeq[0,0]=1
    c=np.zeros(7); c[r]=sense
    return linprog(c,A_ub=Aub,b_ub=bub,A_eq=Aeq,b_eq=[1],bounds=[(0,None)]*7,method='highs')
def exact_vertex(A,x):
    import sympy
    rowsA=[];rb=[]
    for c,b in A:
        if abs(sum(ci*xi for ci,xi in zip(c,x))-b)<1e-7: rowsA.append(c); rb.append(b)
    rowsA.append([1,0,0,0,0,0,0]); rb.append(1)
    M=sympy.Matrix(rowsA)
    if M.rank()<7: return None
    idx=[]; cur=sympy.zeros(0,7)
    for i in range(M.rows):
        t=cur.col_join(M[i,:])
        if t.rank()>cur.rows: cur=t; idx.append(i)
        if cur.rows==7: break
    sol=cur.solve(sympy.Matrix([rb[i] for i in idx]))
    return [F(int(v.p),int(v.q)) for v in sol]
def feasible(A,x):
    return all(sum(F(ci)*xi for ci,xi in zip(c,x))<=b for c,b in A) and x[0]==1
