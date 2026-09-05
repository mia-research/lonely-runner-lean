import csv, random
from collections import Counter
rnd=random.Random(7)
def d_recursion(N,e):
    s=[]; e=abs(e)
    while e>0:
        D=N//e
        if D==0: break
        s.append(D); e=abs(e-N//D)
    return s
# real keys: D-signature of the band-offset (position within band), early terms
real=[]
for r in csv.DictReader(open("puzzles_verified.csv")):
    P=int(r["bits"]);
    if P<24: continue
    off=int(r["private_key"],16)-(1<<(P-1))
    if off<=0: continue
    real.append((P,d_recursion(1<<(P-1),off)))
print(f"real keys (P>=24): {len(real)}")
def early(sigs,i): return [s[i] for _,s in sigs if len(s)>i]
# compare D_1,D_2 value repetition: real vs matched-random
for i in (0,1,2):
    rv=early(real,i)
    # matched random: same bit-lengths, random offset
    rand=[]
    for P,_ in real:
        off=rnd.randrange(1,1<<(P-1)); s=d_recursion(1<<(P-1),off)
        if len(s)>i: rand.append(s[i])
    def top(vals): 
        c=Counter(vals); return c.most_common(4), len(set(vals)), len(vals)
    rt,ru,rn=top(rv); at,au,an=top(rand)
    print(f"D_{i+1}: real distinct={ru}/{rn} top={rt}")
    print(f"      rand distinct={au}/{an} top={at}")
