#!/usr/bin/env python3
"""Convert LRC-style Markdown proof files to LaTeX with proper amsthm environments."""

import re
import sys

PREAMBLE = r"""\documentclass[11pt,a4paper]{article}
\usepackage[utf8]{inputenc}
\usepackage[T1]{fontenc}
\usepackage{amsmath,amssymb,amsthm,mathtools}
\usepackage{geometry}
\geometry{margin=2.5cm}
\usepackage{hyperref}
\hypersetup{colorlinks=true,linkcolor=blue,citecolor=blue,urlcolor=blue}
\usepackage{booktabs,array,lmodern}

% Theorem environments
\theoremstyle{plain}
\newtheorem{theorem}{Theorem}[section]
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{corollary}[theorem]{Corollary}
\newtheorem{proposition}[theorem]{Proposition}
\theoremstyle{definition}
\newtheorem{definition}[theorem]{Definition}
\newtheorem{example}[theorem]{Example}
\theoremstyle{remark}
\newtheorem{remark}[theorem]{Remark}
\newtheorem*{remark*}{Remark}

% Custom macros
\DeclareMathOperator{\lcm}{lcm}

"""

POSTAMBLE = "\n\\end{document}\n"


def split_table_row(row):
    """Split a markdown table row on | respecting math mode."""
    cells = []
    current = []
    in_math = False
    i = 0
    while i < len(row):
        c = row[i]
        if c == '$':
            in_math = not in_math
            current.append(c)
        elif c == '|' and not in_math:
            cells.append(''.join(current).strip())
            current = []
        else:
            current.append(c)
        i += 1
    last = ''.join(current).strip()
    if last:
        cells.append(last)
    # Remove empty leading/trailing cells from | at start/end of row
    if cells and cells[0] == '':
        cells = cells[1:]
    if cells and cells[-1] == '':
        cells = cells[:-1]
    return cells


def unicode_to_latex(text):
    """Replace unicode chars that pdflatex cannot handle."""
    replacements = [
        ('\u2713', r'$\checkmark$'),   # ✓
        ('\u2717', r'$\times$'),        # ✗
        ('\u2014', '--'),               # —
        ('\u2013', '-'),                # –
        ('\u2026', r'\ldots{}'),        # …
        ('\u00b7', r'\cdot{}'),         # ·
        ('\u03c6', r'$\varphi$'),       # φ
        ('\u03c1', r'$\rho$'),          # ρ
        ('\u2264', r'$\leq$'),          # ≤
        ('\u2265', r'$\geq$'),          # ≥
        ('\u2208', r'$\in$'),           # ∈
        ('\u2209', r'$\notin$'),        # ∉
        ('\u2260', r'$\neq$'),          # ≠
        ('\u2192', r'$\to$'),           # →
        ('\u21d2', r'$\Rightarrow$'),   # ⇒
    ]
    for u, l in replacements:
        text = text.replace(u, l)
    return text


def remove_square(text):
    """Remove $\\square$ or \\square from end of text."""
    text = re.sub(r'\s*\$\\square\$\s*$', '', text)
    text = re.sub(r'\s*\\square\s*$', '', text)
    return text.rstrip()


def process_inline(text):
    """Convert inline Markdown to LaTeX: bold, italic, code. Preserves math."""
    math_blocks = []

    def save_math(m):
        math_blocks.append(m.group(0))
        return 'MATHBLOCK%dXX' % (len(math_blocks) - 1)

    # Save all math (display then inline)
    text = re.sub(r'\$\$[\s\S]*?\$\$', save_math, text)
    text = re.sub(r'\$[^$\n]+?\$', save_math, text)

    # Bold+italic
    text = re.sub(r'\*\*\*(.+?)\*\*\*', r'\\textbf{\\textit{\1}}', text)
    # Bold
    text = re.sub(r'\*\*(.+?)\*\*', r'\\textbf{\1}', text)
    # Italic (not inside words)
    text = re.sub(r'(?<!\*)\*([^*\n]+?)\*(?!\*)', r'\\textit{\1}', text)
    # Inline code
    text = re.sub(r'`([^`]+)`', r'\\texttt{\1}', text)

    # Escape special chars outside math (after math saved)
    parts = re.split(r'(MATHBLOCK\d+XX)', text)
    escaped_parts = []
    for part in parts:
        if re.match(r'MATHBLOCK\d+XX', part):
            escaped_parts.append(part)
        else:
            # Escape _ and # outside math
            part = re.sub(r'(?<!\\)_', r'\\_', part)
            part = re.sub(r'(?<!\\)#', r'\\#', part)
            escaped_parts.append(part)
    text = ''.join(escaped_parts)

    # Restore math
    for i, m in enumerate(math_blocks):
        text = text.replace('MATHBLOCK%dXX' % i, m)

    return text


def get_env_type(keyword):
    k = keyword.lower()
    if 'theorem' in k:
        return 'theorem'
    elif 'lemma' in k:
        return 'lemma'
    elif 'corollary' in k:
        return 'corollary'
    elif 'proposition' in k:
        return 'proposition'
    elif 'definition' in k:
        return 'definition'
    elif 'remark' in k:
        return 'remark'
    elif 'example' in k:
        return 'example'
    elif 'claim' in k:
        return 'proposition'
    return 'theorem'


def process_lines(lines):
    out = []
    i = 0
    in_proof = False
    in_itemize = False
    in_enumerate = False

    while i < len(lines):
        line = lines[i]
        line = unicode_to_latex(line)

        # --- Horizontal rule ---
        if re.match(r'^---+\s*$', line):
            out.append('')
            out.append('\\medskip')
            out.append('')
            i += 1
            continue

        # --- Multi-line display math block ---
        stripped = line.strip()
        if stripped == '$$':
            # Start of block display math
            i += 1
            math_lines = []
            while i < len(lines) and lines[i].strip() != '$$':
                math_lines.append(lines[i])
                i += 1
            i += 1  # skip closing $$
            out.append('\\[')
            out.extend(math_lines)
            out.append('\\]')
            continue

        # Single-line $$...$$
        if stripped.startswith('$$') and stripped.endswith('$$') and len(stripped) > 4:
            inner = stripped[2:-2].strip()
            out.append('\\[' + inner + '\\]')
            i += 1
            continue

        # --- Section headers ---
        m = re.match(r'^(#{1,4})\s+(.*)', line)
        if m:
            level = len(m.group(1))
            title = m.group(2).strip()
            # Close open list envs
            if in_itemize:
                out.append('\\end{itemize}')
                in_itemize = False
            if in_enumerate:
                out.append('\\end{enumerate}')
                in_enumerate = False
            # Close proof on new section? Usually no — just emit
            title_tex = process_inline(title)
            if title.lower() == 'abstract':
                out.append('\\begin{abstract}')
                i += 1
                while i < len(lines):
                    l = unicode_to_latex(lines[i])
                    if re.match(r'^#{1,3}\s', l) or re.match(r'^---+\s*$', l):
                        break
                    if l.strip():
                        out.append(process_inline(l))
                    i += 1
                out.append('\\end{abstract}')
                continue
            cmds = {1: '\\section', 2: '\\section', 3: '\\subsection', 4: '\\subsubsection'}
            cmd = cmds.get(level, '\\paragraph')
            out.append('')
            out.append(f'{cmd}{{{title_tex}}}')
            out.append('')
            i += 1
            continue

        # --- Theorem/Lemma/etc. ---
        thm_match = re.match(
            r'^\*\*\s*(Theorem|Lemma|Corollary|Proposition|Definition|Remark|Example|'
            r'Claim|Supplementary Remark)\s*([0-9A-Za-z._\-]*)\s*(\([^)]*\))?\s*[.:]?\s*\*\*\s*(.*)',
            line
        )
        if thm_match:
            keyword = thm_match.group(1)
            name_paren = thm_match.group(3)
            rest = thm_match.group(4).strip()
            env = get_env_type(keyword)
            name = name_paren[1:-1] if name_paren else None
            opt = f'[{name}]' if name else ''

            if in_proof:
                out.append('\\end{proof}')
                in_proof = False

            out.append('')
            out.append(f'\\begin{{{env}}}{opt}')

            # Strip italic wrapping from statement
            rest = re.sub(r'^\*(.+)\*$', r'\1', rest).strip()
            if rest:
                out.append(process_inline(rest))

            # Collect statement continuation lines
            i += 1
            while i < len(lines):
                nl = unicode_to_latex(lines[i])
                if re.match(r'^\*\*\s*(Proof|Proof for)', nl):
                    break
                if re.match(r'^\*\*\s*(Theorem|Lemma|Corollary|Proposition|Definition|'
                            r'Remark|Example|Claim|Supplementary)', nl):
                    break
                if re.match(r'^#{1,4}\s', nl):
                    break
                if re.match(r'^---+\s*$', nl):
                    break
                if nl.strip():
                    out.append(process_inline(nl))
                else:
                    # One blank line OK, two blanks = end of statement
                    out.append('')
                i += 1
            out.append(f'\\end{{{env}}}')
            out.append('')
            continue

        # --- Proof environment ---
        proof_match = re.match(
            r'^\*\*Proof(\s+for\s+[^*]+|[^*]*)?\*\*\s*[.:]?\s*(.*)',
            line
        )
        if proof_match:
            proof_label = (proof_match.group(1) or '').strip()
            rest = (proof_match.group(2) or '').strip()

            if in_proof:
                out.append('\\end{proof}')
            if proof_label:
                out.append(f'\\begin{{proof}}[Proof {proof_label}]')
            else:
                out.append('\\begin{proof}')
            in_proof = True

            if rest:
                has_square = (r'\square' in rest)
                if has_square:
                    clean = remove_square(rest)
                    if clean:
                        out.append(process_inline(clean))
                    if in_itemize:
                        out.append('\\end{itemize}')
                        in_itemize = False
                    if in_enumerate:
                        out.append('\\end{enumerate}')
                        in_enumerate = False
                    out.append('\\end{proof}')
                    in_proof = False
                else:
                    out.append(process_inline(rest))
            i += 1
            continue

        # --- Lines with \square at end (closes proof) ---
        if in_proof and r'\square' in line:
            clean = remove_square(line)
            if clean.strip():
                out.append(process_inline(clean))
            # Close any open list environments before closing proof
            if in_itemize:
                out.append('\\end{itemize}')
                in_itemize = False
            if in_enumerate:
                out.append('\\end{enumerate}')
                in_enumerate = False
            out.append('\\end{proof}')
            in_proof = False
            i += 1
            continue

        # --- Blockquote ---
        if line.startswith('>'):
            content = line[1:].strip()
            out.append('\\begin{quote}')
            if content:
                out.append(process_inline(content))
            i += 1
            while i < len(lines) and lines[i].startswith('>'):
                c = unicode_to_latex(lines[i][1:].strip())
                if c:
                    out.append(process_inline(c))
                i += 1
            out.append('\\end{quote}')
            continue

        # --- Markdown table ---
        if '|' in line and re.match(r'^\s*\|', line):
            table_rows = []
            while i < len(lines) and '|' in lines[i] and re.match(r'^\s*\|', lines[i]):
                table_rows.append(unicode_to_latex(lines[i]))
                i += 1
            # Filter separator rows (---|---|---)
            data_rows = [r for r in table_rows if not re.match(r'^\s*\|[\s\-:|]+\|\s*$', r)]
            if data_rows:
                ncols = len(split_table_row(data_rows[0]))
                col_spec = 'l' * ncols
                out.append('')
                out.append('\\begin{center}\\begin{tabular}{' + col_spec + '}')
                out.append('\\toprule')
                for ri, row in enumerate(data_rows):
                    cells = split_table_row(row)
                    while len(cells) < ncols:
                        cells.append('')
                    cells_tex = [process_inline(c) for c in cells[:ncols]]
                    out.append(' & '.join(cells_tex) + r' \\')
                    if ri == 0:
                        out.append('\\midrule')
                out.append('\\bottomrule')
                out.append('\\end{tabular}\\end{center}')
                out.append('')
            continue

        # --- Unordered list ---
        if re.match(r'^\s*[-*]\s+', line):
            if not in_itemize:
                if in_enumerate:
                    out.append('\\end{enumerate}')
                    in_enumerate = False
                out.append('\\begin{itemize}')
                in_itemize = True
            content = re.sub(r'^\s*[-*]\s+', '', line)
            out.append('\\item ' + process_inline(content))
            i += 1
            continue

        # --- Numbered list ---
        if re.match(r'^\s*\d+\.\s+', line):
            if not in_enumerate:
                if in_itemize:
                    out.append('\\end{itemize}')
                    in_itemize = False
                out.append('\\begin{enumerate}')
                in_enumerate = True
            content = re.sub(r'^\s*\d+\.\s+', '', line)
            out.append('\\item ' + process_inline(content))
            i += 1
            continue

        # Close list environments on blank line
        if line.strip() == '':
            if in_itemize:
                out.append('\\end{itemize}')
                in_itemize = False
            if in_enumerate:
                out.append('\\end{enumerate}')
                in_enumerate = False
            out.append('')
            i += 1
            continue

        # --- Regular line ---
        out.append(process_inline(line))
        i += 1

    # Close any open environments
    if in_proof:
        out.append('\\end{proof}')
    if in_itemize:
        out.append('\\end{itemize}')
    if in_enumerate:
        out.append('\\end{enumerate}')

    return out


def extract_metadata(lines):
    title = author = date = ''
    for line in lines[:15]:
        if line.startswith('# ') and not title:
            title = line[2:].strip()
        m = re.match(r'\*\*Author:\*\*\s*(.*)', line)
        if m:
            author = m.group(1).strip()
        m = re.match(r'\*\*Date:\*\*\s*(.*)', line)
        if m:
            date = m.group(1).strip()
    return title, author, date


def convert(md_path, tex_path):
    with open(md_path, 'r', encoding='utf-8') as f:
        content = f.read()

    lines = content.split('\n')
    title, author, date = extract_metadata(lines)

    # Skip metadata header (up to first ---)
    start = 0
    for j, l in enumerate(lines):
        if re.match(r'^---+\s*$', l) and j < 20:
            start = j + 1
            break

    body_lines = lines[start:]
    body = process_lines(body_lines)

    tex = [PREAMBLE]
    if title:
        tex.append('\\title{' + title + '}')
    if author:
        tex.append('\\author{' + author + '}')
    if date:
        tex.append('\\date{' + date + '}')
    tex.append('\\begin{document}')
    if title:
        tex.append('\\maketitle')
    tex.append('\\tableofcontents')
    tex.append('\\newpage')
    tex.extend(body)
    tex.append(POSTAMBLE)

    with open(tex_path, 'w', encoding='utf-8') as f:
        f.write('\n'.join(tex))

    print(f'Written: {tex_path}')


if __name__ == '__main__':
    if len(sys.argv) < 3:
        print(f'Usage: {sys.argv[0]} input.md output.tex')
        sys.exit(1)
    convert(sys.argv[1], sys.argv[2])
