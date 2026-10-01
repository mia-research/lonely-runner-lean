"""E259 (2026-10-02): E118's Case C residual members, regenerated exactly (residual_members_C_v1.py's construction, seed
118, unchanged) and saved as a list, with every member re-checked against all 22 EightResidual fields
(residual_fields_v1.FIELDS).  Output: residual_members_C_list_v1.json (members by mode) and .out (counts, check)."""
import json
src = open('residual_members_C_v1.py').read()
exec(src.split("# through the cascade, exact")[0])
bad = {m: sum(1 for S in found[m] if not all(f(S) for _, f in FIELDS)) for m in 'AB'}
json.dump({m: [list(S) for S in found[m]] for m in 'AB'}, open('residual_members_C_list_v1.json', 'w'))
with open('residual_members_C_list_v1.out', 'w') as o:
    o.write(__doc__ + "\n")
    o.write("members: mode A %d, mode B %d; failing any of the %d fields on re-check: %s\n" % (len(found['A']), len(found['B']), len(FIELDS), bad))
print(open('residual_members_C_list_v1.out').read())
