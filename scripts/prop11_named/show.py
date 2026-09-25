import sys,re
L=open(sys.argv[1]).read().split('\n')
for name in sys.argv[2:]:
    for i,l in enumerate(L):
        if re.match(r'(theorem|lemma) '+re.escape(name)+r'\b',l):
            j=i+1
            while j<len(L) and not re.match(r'(/--|theorem |lemma |set_option|end LRC)',L[j]): j+=1
            print('\n'.join(f'{k+1}: {L[k]}' for k in range(i,j)))
