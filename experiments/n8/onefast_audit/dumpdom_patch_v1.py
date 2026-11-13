# dumpdom_patch_v1.py -- applies the round-3 source fixes to dumpdom_gen_v1.py.
src = open('dumpdom_gen_v1.py').read()

old = "(row['y1'] - 1, row['x1'] - 1, row['P'], row['Q'],"
assert old in src, 1
src = src.replace(old, "(row['x1'] - 1, row['y1'] - 1, row['P'], row['Q'],")

old = (
    "    subst e1\n"
    "    simp at hc\n"
    "    rcases hc with hvlt | \u27e8heq1, _\u27e9\n"
    "    \u00b7 exact le_of_lt (by exact_mod_cast hvlt)\n"
    "    \u00b7 exact le_of_eq (by exact_mod_cast heq1)")
new = (
    "    subst e1\n"
    "    rcases Bool.or_eq_true_iff.mp hc with hv | hand\n"
    "    \u00b7 exact le_of_lt (by exact_mod_cast (Bool.of_decide_eq_true hv))\n"
    "    \u00b7 have heq : v = c\u2080 := Bool.of_decide_eq_true (Bool.and_eq_true_iff.mp hand).1\n"
    "      rw [heq]\n"
    "      exact le_refl _")
assert old in src, 2
src = src.replace(old, new)

old = (
    "    obtain \\u27e8c, s\\u27e9 := p\\n'\n"
    "            '    refine \\u27e8c, s, hj, ?_\\u27e9\\n'")
new = (
    "    obtain \\u27e8c, s\\u27e9 := p\\n'\n"
    "            '    refine \\u27e8c, s, rfl, ?_\\u27e9\\n'")
assert old in src, 3
src = src.replace(old, new)

open('dumpdom_gen_v1.py', 'w').write(src)
print('edits applied')
