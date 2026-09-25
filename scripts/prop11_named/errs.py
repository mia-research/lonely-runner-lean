import re,sys
log=open(sys.argv[1]).read(); F=open(sys.argv[2]).read().split('\n')
starts=[(i,re.match(r'(?:theorem|lemma) (\S+)',l).group(1)) for i,l in enumerate(F) if re.match(r'(theorem|lemma) ',l)]
def owner(n):
    o=None
    for i,nm in starts:
        if i<n: o=nm
    return o
from collections import OrderedDict
g=OrderedDict()
for m in re.finditer(r':(\d+):(\d+): error: (.*)',log):
    ln=int(m.group(1)); g.setdefault(owner(ln),[]).append((ln,m.group(3)[:70]))
for k,v in g.items():
    print(k,len(v),v[0], F[v[0][0]-1].strip()[:90])
