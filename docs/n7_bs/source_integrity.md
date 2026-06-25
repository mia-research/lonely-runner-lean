# n = 7 source integrity

| Artifact | SHA-256 | Captured |
|---|---|---|
| `sources_barajas_serra_2008.txt` | `3687fc4b3dfbae2bbd8d82b0b6e4ca2d5a13c7f9b624a7a43f02019f50d0c2c8` | 2026-06-25 |

Bibliographic source: J. Barajas, O. Serra, *The Lonely Runner with Seven
Runners*, The Electronic Journal of Combinatorics 15 (2008), #R48.
<https://www.combinatorics.org/Volume_15/PDF/v15i1r48.pdf>

Re-verify before relying on the text:

```sh
shasum -a 256 sources_barajas_serra_2008.txt
```

If the hash changes, the extracted text was edited or re-generated — re-pin and
note why.
