import re,json
import os
SRC=os.environ.get('SRC','/home/user/lrc-n8-lean/LonelyRunner/LRC/Spec/OrderSixPropElevenN.lean')
L=open(SRC).read().split('\n')
D=json.load(open(os.environ.get('DJ','decls.json')))
cov={d['name']:d for d in D if d['cov']}
def concl(d):
    s=d['sig']
    # conclusion: after the last top-level ':' (depth 0)
    depth=0;last=None
    for i,c in enumerate(s):
        if c in '([{⟨':depth+=1
        elif c in ')]}⟩':depth-=1
        elif c==':' and depth==0 and s[i+1:i+2]!='=' : last=i
    return re.sub(r'\s*:=\s*(by)?\s*$','',s[last+1:]).strip()
for d in D:
    if d['cov']: d['concl']=concl(d)
names=set(cov)
for d in D:
    if not d['cov']: 
        # non-cov decl calling cov lemma?
        body='\n'.join(L[d['sigend']+1:d['end']]) if 'sigend' in d else ''
        hits=[n for n in names if re.search(r'\b'+re.escape(n)+r'\b',body)]
        if hits: print('NONCOV CALLER',d['name'],hits)
json.dump(D,open(os.environ.get('DJ','decls.json'),'w'),indent=0)
from collections import Counter
print(Counter('False' if cov[n]['concl']=='False' else 'P' for n in cov))
for n in cov:
    if cov[n]['concl']!='False': print(n,'::',cov[n]['concl'][:150].replace('\n',' '))
