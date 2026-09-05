# Recount of the "34/34" claim in RESULT_jacobi_closed_form_m_law_v1..v3.
# Drill rule: count DISTINCT configurations of the group before claiming invariance over N.
P7  = [7,19,31,43,67,79]
P11 = [11,23,47,59,71,83]
Bs  = [7,2,11]
tot=distinct=0
for p in P7:
    cls={pow(B,(p-1)//3,p)==1 for B in Bs if B%p}
    tot+=sum(1 for B in Bs if B%p); distinct+=len(cls)
for p in P11:                      # F2: chi3 trivial on F_p^* => S is B-independent => 1 cell
    tot+=sum(1 for B in Bs if B%p); distinct+=1
print("reported %d/%d ; distinct %d ; forced %d (%.0f%%)"%(tot,tot,distinct,tot-distinct,
      100*(tot-distinct)/tot))
