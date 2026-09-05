# Combinatorial Theory — Author Guidelines
# Source: https://escholarship.org/uc/combinatorial_theory/authorGuidelines
# Also derived from ct-sample.tex (the canonical template)

## Review Process
- **Doubly anonymous**: referees do not know author names; authors do not know referee names.
- Referees are asked not to do additional research to identify authors.
- Authors must remove all identifying information from submission.

## LaTeX Template (MANDATORY)
- Must use the official CT LaTeX package: `ct.zip` (contains `ct.sty`, `ct-sample.tex`, `ct-sample.bib`)
- Start every file with exactly:
  ```latex
  \documentclass[12pt]{article}
  \usepackage{ct}
  ```
- **Do not erase comments in the head of the sample file** — used for semi-automatic processing.
- **Do not modify ct.sty** — the journal uses its own copy.

## Formatting Rules
- No commands that change margins or page sizes (`\geometry`, `\textheight`, etc.)
- No `\vspace`, `\hspace`, `\newpage`, `\clearpage`, `\pagebreak`, `\enlargethispage`
- No `\tableofcontents`, `\listoffigures`, `\listoftables` (ct.sty redefines and removes them)

## Packages Already Loaded by ct.sty (do not reload)
- `amssymb`, `amsmath`, `amsthm`, `amsfonts`
- `graphicx`
- `hyperref`
- `cleveref`

## Theorem Environments Already in ct.sty (do not redefine)
- Theorem-like: `theorem`, `lemma`, `corollary`, `proposition`, `fact`, `observation`, `claim`
- Definition-like: `definition`, `example`, `conjecture`, `open`, `problem`, `question`
- Remark-like: `remark`, `note`

## Metadata Commands
```latex
\specs{n}{vol (issue)}{year}{}          % editors fill in
\dateline{Month DD, YYYY}{TBD}{TBD}     % submission date; editors fill acceptance + publication
\keywords{word1, word2, ...}            % no dot at end
\MSC{XXXXX, XXXXX}                      % AMS codes; no dot at end
\title{...}
\author[1]{Name\thanks{Grant info.}}    % grants in \thanks, not in acknowledgements
\affil[1]{Department, Institution, Country\n\email{...}}
```
- Date format: `Month DD, YYYY` (e.g. `April 10, 2026`) — abbreviated or full month, day, year
- For double-blind: use `Anonymous` / `Anonymous Institution` / `anonymous@example.com`

## Abstract Requirements
- Must be included
- Must be entirely **self-contained** (may be distributed separately)
- No `\cite{}`, no `[23]`-style bracket references, no `\ref{}` to items outside abstract
- No user-defined macros
- Prefer "we prove that..." over "we investigate..." or "we study..."

## Acknowledgements
- Use `\section*{Acknowledgements}` for colleague/referee thanks
- Grants and funding go in `\thanks{}` in the `\author` command (appear as footnotes on page 1)

## Bibliography
- Provide a `.bib` file
- Use `\bibliographystyle{alphaurl}` (included in ct.zip)
- Use `\bibliography{your-bib-file}`
- Use correct BibTeX entry types (article, book, misc, etc.)
- Add `doi` field when DOI exists — shown as hyperlink in PDF
- Add `eprint` + `archivePrefix = {arXiv}` for arXiv preprints
- **Do not give both URL and DOI** for the same entry

## Files to Submit
Submit source files including:
- `.tex` main file
- `.bib` bibliography
- `.bbl` processed bibliography (recommended)
- `ct.sty` style file
- `alphaurl.bst` bibliography style
- Any figure files (`.tex`, `.pdf`, `.eps`, etc.)
- Do NOT include build artifacts: `.aux`, `.log`, `.blg`, `.out`, `missfont.log`

## Contact
editors@combinatorial-theory.org
