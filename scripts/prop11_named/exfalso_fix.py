import re,sys
p=sys.argv[1]; L=open(p).read().split('\n')
ind=lambda l: len(l)-len(l.lstrip())
starts=[i for i,l in enumerate(L) if re.match(r'(theorem|lemma) ',l)]+[len(L)]
n=0
for a,b in zip(starts[:-1],starts[1:]):
    head='\n'.join(L[a:a+30]); isP=' : Found speeds ∨' in head or ' : Found w ∨' in head or ' : Found6 w ∨' in head
    i=a
    while i<b:
        l=L[i]; s=l.strip()
        if s in ('exfalso','· exfalso'):
            c=ind(l)+(2 if s.startswith('·') else 0)
            j=i+1
            while j<b and (not L[j].strip() or ind(L[j])>=c): j+=1
            br=range(i+1,j)
            if any(re.search(r'exact (Or\.inl )?hF\s*$',L[k]) for k in br):
                for k in br: L[k]=L[k].replace('exact Or.inl hF','exact hF')
                if isP: L[i]=l.replace('exfalso','left')
                else: L[i]=l.replace('exfalso','skip')
                n+=1
        i+=1
open(p,'w').write('\n'.join(L)); print('exfalso branches',n)
