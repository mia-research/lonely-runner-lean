# Per (2,1)/(1,1) tree cell: LP relaxation of "closer = (s,2)" : every y!=s has no entry (8j-1)/x_y in [9/x_s,15/x_s).
# Per y a threshold J_y>=1: entries j<J_y lie < 9/x_s, entries j>=J_y lie >= 15/x_s (linear, homogeneous).
# Region: the cell's reading box (ranks 2..5 and 6,7), with ranks 6,7 upper bound optionally raised to TOP; R*=9/x_s in [Rlo,Rhi].
# Infeasible LP => no K2s1 point in that region (cell path NOT imposed beyond the box: relaxation).
import pickle, sys, math
import numpy as np
from scipy.optimize import linprog
cells=pickle.load(open('terminals5_J2.pkl','rb'))
sel=[(i,c) for i,c in enumerate(cells) if c[0][-1] in ((2,1),(1,1))]
TOP=float(sys.argv[1]) if len(sys.argv)>1 else None
def solve(A,b,lo,hi):
    n=7
    # vars x0..x6, t ; maximise t
    c=np.zeros(n+1); c[n]=-1
    res=linprog(c,A_ub=np.array(A) if A else None,b_ub=np.array(b) if b else None,
        bounds=[(l,h) for l,h in zip(lo,hi)]+[(0,1)],method='highs')
    return res
nfeas=0; nnodes=0; maxdepth=0; out=[]
for idx,c in sel:
    path,Rlo,Rhi,rg,_=c; s=path[-1][0]-1
    lo=[float(a) for a,b in rg]; hi=[float(b) for a,b in rg]
    if TOP:
        for k in (5,6): hi[k]=max(hi[k],TOP)
    lo[s]=max(lo[s],9/Rhi); hi[s]=min(hi[s],9/Rlo)
    base=[];bb=[]
    for k in range(6):  # x_k <= x_{k+1}
        r=[0]*8; r[k]=1; r[k+1]=-1; base.append(r); bb.append(0)
    others=[y for y in range(7) if y!=s]
    feas=[False]
    def dfs(k,A,b):
        global nnodes
        if feas[0]: return
        nnodes+=1
        res=solve(A,b,lo,hi+[1] if False else hi) if False else solve(A,b,lo,hi)
        if res.status!=0 or -res.fun<=1e-9: return
        if k==len(others): feas[0]=True; out.append((idx,res.x)); return
        y=others[k]
        Jmax=int(math.ceil((9*hi[y]/lo[s]+9)/8))+1
        for J in range(1,max(Jmax,1)+1):
            A2=list(A); b2=list(b)
            if J>=2:  # entry j=J-1 < 9/x_s :  (8J-9) x_s + t <= 9 x_y
                r=[0]*8; r[s]+=(8*J-9); r[y]-=9; r[7]=1; A2.append(r); b2.append(0)
            r=[0]*8; r[y]=9.5; r[s]=-(8*J-1); r[7]=1; A2.append(r); b2.append(0)  # entry J >= 15/x_s
            dfs(k+1,A2,b2)
            if feas[0]: return
    dfs(0,list(base),list(bb))
    nfeas+=feas[0]
print("TOP",TOP,"cells",len(sel),"LP-feasible cells",nfeas,"LP nodes",nnodes)
for idx,x in out: print("feasible cell",idx,cells[idx][0][-3:],np.round(x[:7],4))
