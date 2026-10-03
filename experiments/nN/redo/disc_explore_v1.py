import pickle, numpy as np
from fractions import Fraction as F
from collections import Counter
recs = pickle.load(open('disc_records_v1.pkl','rb'))
R = np.array([float(r[2]) for r in recs]); W = np.array([float(r[3]) for r in recs])
print("R* min max", R.min(), R.max(), "width min max", W.min(), W.max(), "zero width", (W==0).sum())
print("nmoves", sorted(Counter(len(r[6]) for r in recs).items()))
print("R*=1 (no move):", (R==1).sum())
h,e=np.histogram(R,bins=np.arange(1,12.01,0.1))
for a,b in zip(e,h): print("%.1f %d"%(a,b),end=" | ")
print()
c=Counter(r[2] for r in recs); print("top exact R*:",[(str(k),v) for k,v in c.most_common(15)])
