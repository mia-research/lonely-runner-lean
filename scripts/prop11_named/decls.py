import re,sys,json
import os
SRC=os.environ.get('SRC','/home/user/lrc-n8-lean/LonelyRunner/LRC/Spec/OrderSixPropElevenN.lean')
L=open(SRC).read().split('\n')
# find decl starts (line idx of 'theorem'/'lemma' keyword); include preceding docstring/set_option block
starts=[i for i,l in enumerate(L) if re.match(r'(private )?(theorem|lemma|def|noncomputable def|abbrev) ',l)]
decls=[]
for k,s in enumerate(starts):
    # block begins after previous decl end: back up over docstring and set_option lines
    b=s
    j=s-1
    while j>=0 and L[j].startswith('set_option') : j-=1
    # docstring
    if j>=0 and L[j].rstrip().endswith('-/'):
        while not L[j].lstrip().startswith('/--'): j-=1
        b=j
        while b-1>=0 and L[b-1].startswith('set_option'): b-=1
    else:
        b=j+1
    e=(starts[k+1] if k+1<len(starts) else len(L))
    name=re.match(r'(?:private )?(?:theorem|lemma|def|noncomputable def|abbrev) (\S+)',L[s]).group(1)
    decls.append(dict(name=name,begin=b,kw=s,end=e))
# fix ends: end = begin of next
for k in range(len(decls)-1): decls[k]['end']=decls[k+1]['begin']
# signature: from kw until line containing ':= by' or ':=' at top
for d in decls:
    sig=[]
    for i in range(d['kw'],d['end']):
        sig.append(L[i])
        if re.search(r':=\s*(by)?\s*$',L[i]) or re.search(r':= by\b',L[i]): d['sigend']=i;break
    d['sig']='\n'.join(sig)
    m=re.search(r'\((hcov\w*|hcover\w*|hcon)\s*:',d['sig'])
    d['cov']=m.group(1) if m else None
    if d['cov']:
        d['six']= 'circDist (2 *' in d['sig'].split(d['cov']+' :')[1][:200]
json.dump(decls,open(os.environ.get('DJ','decls.json'),'w'),indent=0)
cov=[d for d in decls if d['cov']]
print(len(decls),len(cov))
