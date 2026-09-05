# Float-exactify report — per-line disposition (2026-08-27)

Working the 68-line backlog in `FLOAT_EXACTIFY_BACKLOG_v1.md`, in order. Two lines done in a
prior (interrupted) session, carried here for a complete record:

| file:line | class | what changed | verdict unchanged? |
|---|---|---|---|
| d2_twist_rigidity_certificate_v1.py:268-269 | EXACTIFIED | `abs(r)==sqp` magnitude and `(r/sqp)**m==1` root-of-unity checks rewritten to exact integer/`Fraction`/`sympy` comparison | yes (prior session) |
| subrayleigh_deficit_locus_v1.py:166,168 | NOQA-STAT | primary check `pair_ok` is exact; `eqerr` is a secondary numerical guard alongside it — noqa applied | yes (prior session) |

Remaining ~66 lines worked below, one file section per completed file.
