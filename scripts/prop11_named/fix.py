"""Error-driven fixes on the ported file (applied in place)."""
import re,sys
log=open(sys.argv[1]).read(); path=sys.argv[2]; F=open(path).read().split('\n')
ind=lambda l: len(l)-len(l.lstrip())
done=set(); n=0
blocks=re.split(r'\n(?=\S+\.lean:\d+:\d+: )',log)
for b in blocks:
    m=re.match(r'\S+\.lean:(\d+):(\d+): error: Type mismatch\n(.*)',b,re.S)
    if not m: continue
    L=int(m.group(1))-1; body=m.group(3)
    mm=re.search(r'has type\n\s*(.*?)\nbut is expected to have type\n\s*(.*?)(\n|$)',body,re.S)
    if not mm: continue
    have,exp=mm.group(1).strip(),mm.group(2).strip()
    if have=='False' and exp.startswith('Found'):
        for k in (L,L-1):
            if k in done: break
            l=F[k]
            r=re.sub(r'\b(exact|refine) ',lambda x: x.group(1)+' False.elim <| ',l,count=1)
            if r!=l: F[k]=r; done.add(k); n+=1; break
    elif have.startswith('Found') and exp=='False':
        # nested `have h : ∀ x : T, ¬ (A) := by intro x hx …`
        k=L
        while k>0 and not re.match(r'\s*have (\S+) : ∀ ',F[k]): k-=1
        if k in done: continue
        mh=re.match(r'(\s*)have (\S+) : (∀ .*)$',F[k])
        j=k
        while not F[j].rstrip().endswith(':= by'): j+=1
        # the intro line after the header
        mi=re.match(r'(\s*)intro (\S+) (\S+)\s*$',F[j+1])
        if not mi: print('skip nested at',k+1); continue
        base=mh.group(1)
        F[k]=f"{base}obtain hF | {mh.group(2)} : Found w ∨ ({mh.group(3)}"
        F[j]=F[j].rstrip()[:-len(':= by')].rstrip()+') := by'
        F[j+1]=f"{mi.group(1)}rw [or_iff_not_imp_right]\n{mi.group(1)}intro hQ\n{mi.group(1)}obtain ⟨{mi.group(2)}, {mi.group(3)}⟩ := not_forall_not.mp hQ"
        # end of the have block: next line with indentation <= base
        e=j+2
        while e<len(F) and (not F[e].strip() or ind(F[e])>len(base)): e+=1
        F.insert(e,f"{base}· exact hF")
        done.add(k); n+=1
open(path,'w').write('\n'.join(F))
print('fixed',n)
