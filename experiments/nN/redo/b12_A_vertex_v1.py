import sys; sys.path.insert(0,'.')
from b12_cell_lib_v1 import *
import pickle
d=pickle.load(open('terminals5_J2.pkl','rb'))
cell=d[109535]
v=[F(1),F(16715503,7123545),F(47,15),F(726761,173745),F(47,9),F(15463,2673),F(2209,297)]
# interior arrangement of the cell: use the float witness rationalised then check path
wit=cell[4]; P=cell[0]
import random
# find an exact interior arrangement: vertex + eps toward box centre, verify path
lo=[F(l) for l,h in cell[3]]; hi=[F(h) for l,h in cell[3]]
def pathkey(x):
    st,R=path(x); return tuple((s['setter']+1,s['lap']) for s in st),R
print('vertex itself path:',len(path(v)[0]),float(path(v)[1]))
found=None
for e in [F(1,10**k) for k in range(3,14)]:
    x=[F(1)]+[F(w).limit_denominator(10**12) for w in wit]
    # move toward the sorted-witness
    if pathkey(x)[0]==P: found=x;break
print('witness-rationalised in cell:',found is not None)
x0=found
rows,tags,(steps,R0)=cell_rows(x0)
print('constraint rows',len(rows),'path len',len(steps),'R*',float(R0))
print('x0 feasible exact',feasible_exact(rows,x0))
print('vertex feasible exact (closure)',feasible_exact(rows,v))
res=min_rho_s_exact(rows,7)
X,lam=res
print('LP exact vertex == given vertex:',X==v)
print('rho_7 min =',X[6],' R*sup = 89/rho7 =',F(89)/X[6],float(F(89)/X[6]))
tight=[i for i,a in enumerate(rows) if row_val(a,v)==0]
print('number of tight rows at the vertex (exact zero):',len(tight))
# distinct tight rows (dedupe by normalised row)
seen={}
for i in tight:
    a=rows[i]; g=__import__('math').gcd(*[abs(t) for t in a]); key=tuple(t//g for t in a)
    seen.setdefault(key,[]).append(i)
print('distinct tight constraints:',len(seen))
for key,ids in seen.items():
    i=ids[0]; print(key,'dual' if i in lam else '', float(lam.get(i,0)) if i in lam else '', tags[i])
import sympy
A=sympy.Matrix([[sympy.Rational(t.numerator,t.denominator) if isinstance(t,F) else t for t in k[1:]] for k in seen])
print('rank of tight rows in the 6 free readings:',A.rank())
print('dual-certificate multipliers (exact):',{i:str(l) for i,l in lam.items()})
pickle.dump((x0,),open('b12_A_x0_v1.pkl','wb'))
