# Direct-use scan: which LRC/Spec modules mention the order 5/6/7 results, and their Spec import closure (a proxy: import is not use).
import re,os,glob
d='LonelyRunner/LonelyRunner/LRC/Spec'
mods={os.path.basename(f)[:-5]:f for f in glob.glob(d+'/*.lean')}
pat=re.compile(r'(OrderSevenN|OrderSixN|OrderFiveN|lonely_(five|six|seven)_nat|existenceAtN_(five|six|seven)|lonely_eight_of_card_le_six)')
for m in sorted(mods):
    t=open(mods[m]).read(); u=sorted(set(x.group(0) for x in pat.finditer(t)))
    if u: print(m,'|',','.join(u))
