"""Port BHK Prop 11 (covering form) to named-instant form.

For every lemma taking the time covering `hcover`/`hcov6`:
  * the covering binder is dropped;
  * conclusion `False` becomes `Found w` (`Found6 w` for the six-runner covering);
  * any other conclusion `P` becomes `Found w ∨ P`;
  * `hcover τ` at a named instant becomes `found_or_blocked w τ`: either `τ` is
    lonely (`hF`, the named instant) or some runner blocks it, as before;
  * a call to a converted lemma drops the covering argument, and a call whose
    conclusion is `Found w ∨ P` is split, the `Found` branch returned at once.
Sites the rules do not reach are left for hand edits (reported on stdout).
"""
import json,re,sys
import os
SRC=os.environ.get('SRC','/home/user/lrc-n8-lean/LonelyRunner/LRC/Spec/OrderSixPropElevenN.lean')
L=open(SRC).read().split('\n')
D=json.load(open(os.environ.get('DJ','decls.json')))
WV=os.environ.get('WV','w')
TIME=lambda d: bool(d['cov']) and 'orbit' not in d['name'] and 'no_double' not in d['name']
conv={d['name']:d for d in D if TIME(d)}
callable_=dict(conv)
if os.environ.get('EXTRA'):
    for d in json.load(open(os.environ['EXTRA'])):
        if TIME(d): callable_.setdefault(d['name'],d)
isP=lambda n: callable_[n]['concl']!='False'
ind=lambda l: len(l)-len(l.lstrip())
out_decls=[]
report=[]
def binder_span(sig,var):
    i=sig.index('('+var+' :')
    depth=0
    for j in range(i,len(sig)):
        if sig[j]=='(':depth+=1
        elif sig[j]==')':
            depth-=1
            if depth==0: return i,j+1
def new_sig(d):
    sig=d['sig']; v=d['cov']
    i,j=binder_span(sig,v)
    # remove binder plus following whitespace / leading space
    pre=sig[:i].rstrip(' '); post=sig[j:]
    if pre.endswith('\n'):  # binder alone on its line(s)
        post=post.lstrip(' ')
        if post.startswith('\n'): post=post[1:]
        elif post: post=' '*4+post
    else:
        pre=pre+('' if post.startswith(' ') or post.startswith('\n') else ' ')
        if post.startswith(' '): pass
    sig=pre+post
    sig=re.sub(r'\n\s*\n','\n',sig)
    F=('Found6 ' if d['six'] else 'Found ')+WV
    if d['concl']=='False':
        sig=re.sub(r':\s*False\s*:=(\s*by)?\s*$',lambda m: ': '+F+' :='+(' by' if m.group(1) else ''),sig)
        assert F in sig,(d['name'],sig[-80:])
    else:
        # wrap conclusion: find the colon that starts it
        c=d['concl']
        k=sig.rindex(':=')
        body=sig[:k]
        # the conclusion text is the tail of body after the last top-level ' :'
        depth=0;last=None
        for p,ch in enumerate(body):
            if ch in '([{⟨':depth+=1
            elif ch in ')]}⟩':depth-=1
            elif ch==':' and depth==0 and body[p+1:p+2]!='=': 
                last=p; break_=True
        # first top-level colon after all binders: binders end at last top-level ')' before conclusion
        # find last binder close: scan binder groups at depth 0
        depth=0;pos=None;p=0
        # skip the head 'lemma name'
        while p<len(body):
            ch=body[p]
            if ch in '([{⟨':depth+=1
            elif ch in ')]}⟩':depth-=1
            elif ch==':' and depth==0: pos=p;break
            p+=1
        concl=body[pos+1:]
        term=not re.search(r':=\s*by\s*$',d['sig'])
        sig=body[:pos+1]+' '+F+' ∨\n      ('+concl.strip()+') :='+('' if term else ' by')
    return sig
esc=lambda d: 'hF' if d['concl']=='False' else 'Or.inl hF'
def stmt_end(lines,i):
    """last line index of the tactic statement starting at i (continuation = deeper indent)."""
    base=ind(lines[i]) + (2 if lines[i].lstrip().startswith('· ') else 0)
    j=i
    while j+1<len(lines) and lines[j+1].strip() and ind(lines[j+1])>=base+(0 if lines[i].lstrip().startswith('· ') else 1):
        j+=1
    return j
def convert_body(d,lines):
    v=d['cov']; e=esc(d)
    six=d['six']
    out=[];i=0
    pending={}  # line index -> escape line to insert after
    # pass 1: textual rewrites per line
    res=list(lines)
    inserts={}
    for i,l in enumerate(res):
        s=l.strip()
        if not s: continue
        eff_ind=ind(l)+(2 if s.startswith('· ') else 0)
        # direct use of the covering at an instant
        m=re.search(r'obtain (⟨[^⟩]*⟩) := '+v+r' (.+)$',l)
        if m and not six:
            res[i]=l[:m.start()]+f'obtain hF | {m.group(1)} := found_or_blocked {WV} {m.group(2)}'
            inserts.setdefault(stmt_end(res,i),[]).append(' '*eff_ind+'· exact '+e); continue
        m=re.search(r'rcases '+v+r' (.+?) with (.+)$',l)
        if m:
            fn='found6_or_blocked' if six else 'found_or_blocked'
            res[i]=l[:m.start()]+f'rcases {fn} {WV} {m.group(1)} with hF | {m.group(2)}'
            inserts.setdefault(stmt_end(res,i),[]).append(' '*eff_ind+'· exact '+e); continue
        # calls to converted lemmas
        callees=[n for n in re.findall(r'[A-Za-z_][\w.]*',l) if n in callable_]
        if not callees: 
            if re.search(r'\b'+v+r'\b',l) and not s.startswith('--') and '`' not in s: report.append((d['name'],i,'direct',s))
            continue
        callee=callees[-1]
        # drop the covering argument (may be on this or the next line)
        hit=False
        for k in (i,i+1,i+2):
            if k<len(res) and re.search(r' '+v+r'\b',res[k]):
                res[k]=re.sub(r' '+v+r'\b','',res[k],count=1); hit=True; break
        if not hit: report.append((d['name'],i,'no-arg',s)); continue
        if not isP(callee): continue
        s0=i
        if not re.match(r'\s*(· )?(have|obtain|rcases|exact|refine|·)\b',res[i]):
            k=i-1
            while k>=0 and (not res[k].strip() or ind(res[k])>=ind(res[i])): k-=1
            s0=k
        i0=i; i=s0
        eff_ind=ind(res[i])+(2 if res[i].strip().startswith('· ') else 0)
        l=res[i]
        m=re.match(r'(\s*(?:· )?)have (\S+) : (.*?) :=\s*$',l)
        if m:
            FF=('Found6 ' if d['six'] else 'Found ')+WV
            res[i]=f'{m.group(1)}obtain hF | {m.group(2)} : {FF} ∨ ({m.group(3)}) :='
            inserts.setdefault(stmt_end(res,i),[]).append(' '*eff_ind+'· exact '+e); continue
        m=re.match(r'(\s*(?:· )?)have (\S+) : (.*?) := (.+)$',l)
        if m:
            FF=('Found6 ' if d['six'] else 'Found ')+WV
            res[i]=f'{m.group(1)}obtain hF | {m.group(2)} : {FF} ∨ ({m.group(3)}) := {m.group(4)}'
            inserts.setdefault(stmt_end(res,i),[]).append(' '*eff_ind+'· exact '+e); continue
        m=re.match(r'(\s*(?:· )?)have (\S+) := (.*)$',l)
        if m:
            res[i]=f'{m.group(1)}obtain hF | {m.group(2)} := {m.group(3)}'
            inserts.setdefault(stmt_end(res,i),[]).append(' '*eff_ind+'· exact '+e); continue
        m=re.match(r'(\s*(?:· )?)obtain (.*)$',l)
        if m:
            res[i]=f'{m.group(1)}obtain hF | {m.group(2)}'
            inserts.setdefault(stmt_end(res,i),[]).append(' '*eff_ind+'· exact '+e); continue
        m=re.match(r'(\s*(?:· )?)rcases (.*) with (.+)$',l)
        if not m and re.match(r'\s*(· )?rcases',l):
            j=stmt_end(res,i)
            mm=re.match(r'(.*) with (.+)$',res[j])
            if mm:
                res[j]=f'{mm.group(1)} with hF | {mm.group(2)}'
                inserts.setdefault(j,[]).append(' '*eff_ind+'· exact '+e); continue
        if m:
            res[i]=f'{m.group(1)}rcases {m.group(2)} with hF | {m.group(3)}'
            inserts.setdefault(stmt_end(res,i),[]).append(' '*eff_ind+'· exact '+e); continue
        if re.match(r'\s*(· )?(exact|refine) ',l) and d['concl']!='False':
            continue  # Found ∨ P into Found ∨ P' — hand-check the P part
        report.append((d['name'],i,'P-call',res[i].strip()[:120]))
    out=[]
    for i,l in enumerate(res):
        out.append(l)
        for x in inserts.get(i,[]): out.append(x)
    # hoist an escape that opens a top-level `have … := by` block
    k=1
    while k<len(out):
        l=out[k]; prev=out[k-1]
        if re.match(r'    (obtain hF \||rcases found)',l) and re.match(r'  have .*:= by\s*$',prev) and k+1<len(out) and out[k+1].startswith('    · exact '):
            o=l[2:]; x='  · exact '+e
            del out[k:k+2]
            out[k-1:k-1]=[o,x]
            k+=1
        k+=1
    if d['concl']!='False':
        first=next(k for k,l in enumerate(out) if l.strip() and not l.strip().startswith('--'))
        m=re.match(r'  by_contra (\S+)\s*$',out[first])
        if m:
            out[first:first+1]=['  rw [or_iff_not_imp_right]','  intro '+m.group(1)]
        m=re.match(r'  intro (\S+) (\S+)\s*$',out[first])
        if m and 'pent_no_good' in d['name']:
            out[first:first+1]=['  rw [or_iff_not_imp_right]','  intro hQ',
                f'  obtain ⟨{m.group(1)}, {m.group(2)}⟩ := not_forall_not.mp hQ']
    if d['concl']!='False':
        tops=[k for k,l in enumerate(out) if l=='  · exact Or.inl hF']
        if tops:
            out.insert(tops[-1]+1,'  right')
        else:
            report.append((d['name'],0,'P-needs-hand',''))
    return out
body_out=[]
for d in D:
    if not TIME(d): continue
    blk=L[d['begin']:d['end']]
    sigoff=d['kw']-d['begin']; sigend=d['sigend']-d['begin']
    head=blk[:sigoff]
    sig=new_sig(d)
    body=convert_body(d,blk[sigend+1:])
    body_out.append('\n'.join(head)+('\n' if head else '')+sig+'\n'+'\n'.join(body))
WV=os.environ.get('WV','w')
hdr=open(os.environ.get('HDR','header.lean')).read()
open(sys.argv[1] if len(sys.argv)>1 else 'EN.lean','w').write(hdr+'\n'.join(body_out)+'\nend LRC.OrderSixN.S7.Named\n')
for r in report: print(r)
print(len(report),'sites for hand edits')
