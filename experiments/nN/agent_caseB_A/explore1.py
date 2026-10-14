from core import *
from collections import Counter
import time
t=time.time()
cnt=Counter(); lev=Counter(); none=[]; mism=0
sets=list(integer_band_sets(24))
print("n sets", len(sets))
for ns in sets:
    L=landing(ns)
    iv=lonely_intervals(ns)
    lm = min(a for a,b in iv) if iv else None
    if (L is None) != (lm is None) or (L and L[0]!=lm): mism+=1
    if L is None: none.append(ns); continue
    ll=least_level(ns); lev[ll[0]]+=1
    cnt['R<=7' if L[0]<=7 else 'R>=9']+=1
print("mismatch landing vs intervals", mism, "none", len(none), none[:5])
print(cnt, sorted(lev.items()), time.time()-t)
late=(10000,23509,32412,41886,52223,57871,74378)
print("late", landing(late), least_level(late), lonely_intervals(late))
