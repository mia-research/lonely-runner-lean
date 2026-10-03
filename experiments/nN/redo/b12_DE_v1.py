# (E) Farkas support of each cell's exact supremum; (D) window relations at near-supremum arrangements.  Exact Fractions throughout.
import sys, time, pickle; sys.path.insert(0,'.')
from b12_cell_lib_v1 import *
from collections import Counter
d=pickle.load(open('terminals5_J2.pkl','rb')); m=pickle.load(open('cell_members_J2.pkl','rb'))
memb={}
for ci,x in m: memb.setdefault(ci,x)
(x0,)=pickle.load(open('b12_A_x0_v1.pkl','rb'))
starts=[('vertex-cell',x0)]
for i,c in enumerate(d):
    if c[2]>11 and any(s[0]==1 for s in c[0]):
        starts.append(('c%d'%i, memb[i] if i in memb else [F(1)]+[F(w).limit_denominator(10**12) for w in c[4]]))
seen={}; recs=[]
for lab,x in starts:
    info=cell_info(x)
    if info['n']==0 or info['sig'] in seen or info['sup'] is None: continue
    seen[info['sig']]=1
    # gate state index
    kg=next(k+1 for k,s in enumerate(info['steps']) if s['setter']==0)
    lam=info['lam']; sup_rows=[(i,l) for i,l in lam.items() if l>0]
    mean=[row_meaning(info['tags'][i]) for i,l in sup_rows]
    atgate=sum(1 for i,l in sup_rows if info['tags'][i][0]!='order' and len(info['tags'][i])>2 and info['tags'][i][2]==kg and info['tags'][i][0] in ('entry',) or (info['tags'][i][0] not in ('order','setter') and info['tags'][i][2]==kg))
    # near-supremum interior arrangement
    X=info['X']; xi=info['x']; y=None
    for k in range(5,16):
        e=F(1,10**k); z=[a+e*(b-a) for a,b in zip(X,xi)]
        i2=cell_info(z,with_sup=False)
        if i2['sig']==info['sig']: y=z; break
    o=outcome(y) if y else None
    recs.append(dict(lab=lab,sup=info['sup'],n=info['n'],kg=kg,nsup=len(sup_rows),mean=mean,atgate=atgate,o=o,eps=k if y else None,last=(info['steps'][-1]['setter']+1,info['steps'][-1]['lap'])))
print('distinct fine cells:',len(recs))
recs.sort(key=lambda r:-r['sup'])
print('top 12 exact cell suprema:')
for r in recs[:12]: print(' ',r['lab'],r['sup'],'=%.9f'%float(r['sup']),'moves',r['n'],'gate state',r['kg'],'Farkas rows',r['nsup'],'last setter',r['last'])
print('count of cells with sup > 12:',sum(1 for r in recs if r['sup']>12),' sup >= 11.9:',sum(1 for r in recs if r['sup']>=F(119,10)),' total',len(recs))
print('Farkas support size distribution:',sorted(Counter(r['nsup'] for r in recs).items()))
print('Farkas support rows at the gate state (R=9):',sorted(Counter(r['atgate'] for r in recs).items()))
print('\nFarkas rows of the top 6 cells:')
for r in recs[:6]:
    print(r['lab'],r['sup']); [print('    ',t) for t in r['mean']]
print('\n(D) window relations at near-supremum arrangements (exact):')
tw=Counter(); rows=[]
for r in recs:
    o=r['o']
    if o is None: tw['no near arrangement']+=1; continue
    R=o['R']; w=o['width']; mid=R+w/2; right=R+w
    rows.append((r['lab'],R,w,mid-12,12-R,right-12))
    tw[('12 in window' if R<=12<=right else ('window below 12' if right<12 else 'window above 12'))]+=1
print(dict(tw))
for lab,R,w,dm,dl,dr in rows[:6]:
    print(lab,'R*=',R,'w=',w,'(R*+w/2)-12=',dm,'=%.6f'%float(dm),' 12-R*=',dl,' right-12=',dr)
print('max R* over near-sup arrangements:',max(r[1] for r in rows),float(max(r[1] for r in rows)))
print('count window-centre > 12:',sum(1 for r in rows if r[3]>0),' <12:',sum(1 for r in rows if r[3]<0),' =12:',sum(1 for r in rows if r[3]==0))
print('count R*+right-end = 24 exactly:',sum(1 for r in rows if r[1]+r[1]+r[2]==24))
vr=[r for r in rows if r[0] in ('vertex-cell',)]
print('vertex family: R*=26433/2209 ; 12-R* = 75/2209 ; right end 12+141/2209=567/47 ; w = 216/2209')
