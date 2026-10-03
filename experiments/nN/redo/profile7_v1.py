import sys, pickle
from collections import Counter
exec(open('outcome_classes_v2.py').read().split('\nif __name__ ==')[0])
J=int(sys.argv[1]); T=pickle.load(open('terminals7_J%d.pkl'%J,'rb')); got=pickle.load(open('cell_members7_J%d.pkl'%J,'rb'))
op=Counter(); lf=Counter(); pr=Counter(); K=Counter(); win=Counter(); g1=0; maxR=0; kinds=Counter(); gmax7=0; gmax6=0; paths=set()
for i,rho in got:
    o=outcome(rho); kinds[T[i][5]]+=1
    if not o['opener']: K['K0 (no move)']+=1; win['A']+=1; continue
    s,j=o['opener']; w='A' if o['R']<=7 else 'B'
    op[o['opener']]+=1; lf[(s,o['closer'][0],w)]+=1; pr[(s,o['closer'][0])]+=1; win[w]+=1; maxR=max(maxR,o['R']); paths.add(o['path'])
    if o['R']>7: g1+=1; gmax7=max(gmax7,rho[6]); gmax6=max(gmax6,rho[5])
    strip=(8*j-1<rho[s-1]<8*j+1); nm=o['nmoves']
    K[('K1' if nm==1 else 'K2')+('z' if o['width']==0 else '')+('_strip' if strip else '')+('_lap1' if j==1 else '_lap>=2')+('_closer=opener' if o['closer'][0]==s else '')]+=1
print(f"J={J}: regions {len(T)} (leaf {sum(1 for t in T if t[5]=='T')}, stop {sum(1 for t in T if t[5]=='S')}), exact members {len(got)} (leaf {kinds['T']}, stop {kinds['S']}), distinct paths among members {len(paths)}")
print("openers (rank,lap):",len(op),"| lap-free classes (opener rank, closer rank, window):",len(lf),"| (opener rank, closer rank) pairs:",len(pr),"of 49 | max member landing %.4f"%float(maxR))
print("gate-crossing members:",g1,"(window A:",win['A'],", window B:",win['B'],") | largest rho_7 among gate crossers %.4f, rho_6 %.4f"%(float(gmax7),float(gmax6)))
for k,v in sorted(K.items(),key=lambda x:-x[1]): print("  ",k,v)
print("pairs missing of 49:",sorted({(a,b) for a in range(1,8) for b in range(1,8)}-set(pr)))
pickle.dump((op,lf,pr),open('profile7_sets_J%d.pkl'%J,'wb'))
