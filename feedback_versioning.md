# Versioning Rules — Math Ex / Lonely Runners Paper

## Hard rule: never overwrite
Always write revisions to a NEW versioned filename.
`v35.tex` → work in `v36.tex` → submit as `v37.tex`. Never touch the previous file.

---

## Two-track version numbering (CRITICAL)

| Track | Purpose | Naming | Example |
|---|---|---|---|
| **Internal working** | In-session edits, fixes, experiments | consecutive integers | `v36.tex` |
| **Preprint / submission** | Uploaded to arXiv / Zenodo | next integer AFTER the internal working version | `v37.tex` |

### Rule
> The internal working version and the preprint version are NEVER the same file.

If the last submitted preprint was **v35**, then:
- Internal fix session produces **v36** (internal only — never submitted)
- The new preprint upload is **v37**

If the last submitted preprint was **v30** (n=11 AP paper), then:
- Internal revisions are v31, v32, … (internal)
- Next preprint is the version AFTER the last internal: e.g. if internal stopped at v33, preprint is v34

### Decimal sub-versions
Use `vN.1`, `vN.2` only for minor patch iterations within the same session before a preprint bump.
Example: `v36.1`, `v36.2` are intra-session drafts; `v37` is the preprint.

---

## Checklist before creating a preprint file

- [ ] Internal working version is N (e.g. v36)
- [ ] Preprint filename is N+1 (e.g. v37)
- [ ] `\date{}` contains only the date — no version tag
- [ ] No `v36` / version number visible anywhere in the PDF
- [ ] All cross-references verified
- [ ] No markup asterisks, TODO comments, or draft language
