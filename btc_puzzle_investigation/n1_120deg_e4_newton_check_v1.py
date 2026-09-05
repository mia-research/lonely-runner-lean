from fractions import Fraction as Fr
p=43; n=31; chi_m1=-1  # 43==3 mod4 -> chi2(-1)=-1
V={}
for line in open('v4_out.txt'):
    t=line.split(); V[t[0]]=[int(x) for x in t[1:]]
def cyF(u,v):
    w=[Fr(0)]*n
    for i in range(n):
        if u[i]:
            for j in range(n):
                if v[j]: w[(i+j)%n]+=u[i]*v[j]
    return w
def toF(u):return [Fr(x) for x in u]
def sub(u,v):return [u[i]-v[i] for i in range(n)]
def add(u,v):return [u[i]+v[i] for i in range(n)]
def eq_rational(vec,c):
    # vec == integer c in Z[zeta_n]  iff  vec[1..]==t all equal and vec[0]==c+t
    t=vec[1]
    if any(vec[j]!=t for j in range(1,n)): return False
    return vec[0]==c+t
def eq_vec(u,v):
    d=[u[i]-v[i] for i in range(n)]; return all(x==d[0] for x in d)
print("p=43 n=31  chi2(-1)=-1   e4 target = p^2 = 1849")
for a in (1,2):
    p1=toF(V[f'V1_{a}']);p2=toF(V[f'V2_{a}']);p3=toF(V[f'V3_{a}']);p4=toF(V[f'V4_{a}'])
    e1=p1
    e2=[x/2 for x in sub(cyF(e1,p1),p2)]
    e3=[x/3 for x in add(sub(cyF(e2,p1),cyF(e1,p2)),p3)]
    e4=[x/4 for x in sub(add(sub(cyF(e3,p1),cyF(e2,p2)),cyF(e1,p3)),p4)]
    integral=all(x.denominator==1 for x in e2+e3+e4)
    e3_forced=cyF(toF([chi_m1*p]+[0]*(n-1)),e1)
    e3_ok=eq_vec(e3,e3_forced)
    e4_is_p2=eq_rational(e4,1849)
    print(f" a={a}:  e_k integral={integral}   e3==chi2(-1)*p*e1: {e3_ok}   e4==p^2(=1849): {e4_is_p2}")
    if not e4_is_p2:
        print("     e4 canon=",[x-e4[0] for x in e4][:8],"...")
