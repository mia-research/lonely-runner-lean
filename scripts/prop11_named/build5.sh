set -e
cd /tmp/claude-0/-home-user-phi-law-lrc/5da3c994-64cf-54ee-96ba-1beb4c642a5c/scratchpad/en
SRC=/home/user/lrc-n8-lean/LonelyRunner/LRC/Spec/OrderSixSecFiveN.lean DJ=d5.json HDR=header5.lean WV=speeds EXTRA=decls.json python3 convert.py S5.lean >/dev/null
python3 patches5.py S5.lean >/dev/null
python3 - <<'PY'
import json,re
def concl(sig):
    k=sig.rfind(':=')
    body=sig[:k]; depth=0
    for p,ch in enumerate(body):
        if ch in '([{⟨':depth+=1
        elif ch in ')]}⟩':depth-=1
        elif ch==':' and depth==0: return body[p+1:].strip()
fl=set(json.load(open('false_noncov.json')))
for d in json.load(open('d5.json')):
    if not d['cov'] and 'sig' in d and concl(d['sig'])=='False': fl.add(d['name'])
p='S5.lean'; s=open(p).read()
for name in fl:
    s=re.sub(r'\b(exact|refine) '+name+r'\b',r'\1 False.elim <| '+name,s)
s=s.replace("\n  right\n  · ","\n  all_goals right\n  · ")
s=s.replace('(revert hcop; decide)','(exfalso; revert hcop; decide)')
open(p,'w').write(s)
PY
[ -f patches5b.py ] && python3 patches5b.py S5.lean
echo generated
