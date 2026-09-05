#!/usr/bin/env python3
"""Cost of DECIDING 'does m_p have a root beyond the threshold', three exact ways:
  (S) Sturm sequence           -- the method the ADDITION names
  (I) exact real-root isolation (sympy intervals(), Descartes/VAS, exact rationals)
  (D) integer Taylor shift + Descartes sign count -- exact BECAUSE m_p is totally real
All three are float-free."""
import sys,time,random
import sympy as sp
random.seed(3)
Y=sp.Symbol('Y')
print(f"{'d':>5} {'p':>6} {'bits':>7} {'shift_s':>9} {'Descartes_s':>12} {'isolate_s':>11} {'Sturm_s':>10}  agree")
for d,p in [(21,127),(52,349),(102,577),(213,1237),(426,2503),(766,4513),(1027,6007)]:
    roots=sorted(random.randint(-6*p,6*p) for _ in range(d))
    c=[1]
    for r in roots:
        c=[0]+c
        for i in range(len(c)-1): c[i]-=r*c[i+1]
    bits=max(abs(x).bit_length() for x in c)
    thr=-2*p
    true_cnt=sum(1 for r in roots if r<thr)
    # (D) shift + Descartes
    t0=time.time()
    sh=list(c)
    for k in range(d):
        for i in range(d-1,k-1,-1): sh[i]+=thr*sh[i+1]
    tsh=time.time()-t0
    t0=time.time()
    def V(co):
        ch=0;prev=0
        for x in co:
            s=(x>0)-(x<0)
            if s==0: continue
            if prev and s!=prev: ch+=1
            prev=s
        return ch
    alt=[sh[i]*(1 if i%2==0 else -1) for i in range(len(sh))]
    dneg=V(alt); dpos=V(sh)
    td=time.time()-t0
    tot_ok = (dpos+dneg+sum(1 for x in sh if False))==d
    # (I) isolation
    P=sp.Poly(list(reversed(c)),Y)
    t0=time.time()
    try:
        iv=P.intervals(); icnt=sum(k for (a,b),k in iv if b< thr) ; ti=time.time()-t0
    except Exception as e:
        ti=float('nan'); icnt='ERR'
    # (S) Sturm  -- skipped past d=102, measured separately
    if d<=102:
        t0=time.time(); scnt=int(P.count_roots(None,sp.Integer(thr))); ts=time.time()-t0
    else:
        ts=float('nan'); scnt='skipped'
    print(f"{d:>5} {p:>6} {bits:>7} {tsh:>9.2f} {td:>12.4f} {ti:>11.2f} {ts:>10.2f}"
          f"   true={true_cnt} D={dneg} I={icnt} S={scnt} realcert={dpos+dneg==d}", flush=True)
