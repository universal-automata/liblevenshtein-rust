#!/usr/bin/env python3
"""
Advanced converter: RHOLANG_STRUCTURAL_CORRECTION.md → Org-mode with LaTeX
Handles mathematical notation, code blocks, tables, and special formatting
"""

import re
import sys

# Unicode to LaTeX mappings for mathematical symbols
UNICODE_TO_LATEX = {
    '₀': '_0', '₁': '_1', '₂': '_2', '₃': '_3', '₄': '_4',
    '⊕': r'\oplus', '⊗': r'\otimes', '∘': r'\circ',
    '→': r'\rightarrow', '←': r'\leftarrow', '↔': r'\leftrightarrow',
    '⇒': r'\Rightarrow', '⇐': r'\Leftarrow',
    '≡': r'\equiv', '≈': r'\approx', '≠': r'\neq',
    '≤': r'\leq', '≥': r'\geq',
    '∈': r'\in', '∉': r'\notin', '⊆': r'\subseteq', '⊂': r'\subset',
    '∪': r'\cup', '∩': r'\cap',
    '∑': r'\sum', '∏': r'\prod', '∫': r'\int',
    '∀': r'\forall', '∃': r'\exists', '∄': r'\nexists',
    '∅': r'\emptyset', '∞': r'\infty',
    'α': r'\alpha', 'β': r'\beta', 'γ': r'\gamma', 'δ': r'\delta',
    'ε': r'\varepsilon', 'ζ': r'\zeta', 'η': r'\eta', 'θ': r'\theta',
    'λ': r'\lambda', 'μ': r'\mu', 'ν': r'\nu', 'π': r'\pi',
    'ρ': r'\rho', 'σ': r'\sigma', 'τ': r'\tau', 'ω': r'\omega',
    'Σ': r'\Sigma', 'Δ': r'\Delta', 'Γ': r'\Gamma', 'Ω': r'\Omega',
    '×': r'\times', '·': r'\cdot', '÷': r'\div',
    '⊤': r'\top', '⊥': r'\bot',
    '⊢': r'\vdash', '⊨': r'\models',
    '⟨': r'\langle', '⟩': r'\rangle',
    '⌊': r'\lfloor', '⌋': r'\rfloor', '⌈': r'\lceil', '⌉': r'\rceil',
    '◦': r'\circ',
    '∧': r'\land', '∨': r'\lor', '¬': r'\lnot',
    '⁰': '^0', '¹': '^1', '²': '^2', '³': '^3', '⁴': '^4',
    'ℝ': r'\mathbb{R}', 'ℕ': r'\mathbb{N}', 'ℤ': r'\mathbb{Z}',
    '𝒫': r'\mathcal{P}',
}

def convert_unicode_to_latex(text):
    """Convert Unicode math symbols to LaTeX"""
    for unicode_char, latex in UNICODE_TO_LATEX.items():
        text = text.replace(unicode_char, latex)
    return text

def is_mathematical_content(text):
    """Detect if text contains mathematical notation"""
    math_indicators = [
        '→', '∘', '⊗', '⊕', '∈', '≡', '∑', '∏', '∀', '∃',
        '≤', '≥', '⊆', '∪', '∩', 'λ', 'δ', 'σ', 'π', 'ρ',
        '_lexical', '_syntactic', '_total', 'T_', 'Q_', 'w_',
        'edit_distance', 'max_distance', 'G.allows',
        'O(', r'\mathbb', r'\times', r'\cdot'
    ]
    return any(indicator in text for indicator in math_indicators)

def convert_inline_math(text):
    """Convert inline code that contains math to LaTeX inline math"""
    def replace_inline(match):
        content = match.group(1)
        if is_mathematical_content(content):
            latex_content = convert_unicode_to_latex(content)
            return f"${latex_content}$"
        else:
            return f"~{content}~"  # org-mode verbatim

    text = re.sub(r'`([^`\n]+)`', replace_inline, text)
    return text

def convert_code_block(match):
    """Convert code blocks appropriately"""
    lang = match.group(1) if match.group(1) else ''
    content = match.group(2)

    # Check if it's mathematical notation (not code)
    if not lang and is_mathematical_content(content):
        # It's a math block
        latex_content = convert_unicode_to_latex(content)
        # Try to format as align if it has multiple lines with equations
        if '\n' in latex_content and ('=' in latex_content or '→' in latex_content):
            lines = [line.strip() for line in latex_content.split('\n') if line.strip()]
            formatted = ' \\\\\n  '.join(lines)
            return f"\\begin{{align*}}\n  {formatted}\n\\end{{align*}}"
        else:
            return f"\\[ {latex_content} \\]"
    else:
        # It's actual code
        if lang:
            return f"#+begin_src {lang}\n{content}\n#+end_src"
        else:
            return f"#+begin_example\n{content}\n#+end_example"

def process_content(content):
    """Main processing function"""
    # Extract and save metadata
    version_match = re.search(r'\*\*Version:\*\* (.+)', content)
    date_match = re.search(r'\*\*Date:\*\* (.+)', content)
    status_match = re.search(r'\*\*Status:\*\* (.+)', content)

    version = version_match.group(1) if version_match else '1.8'
    date = date_match.group(1) if date_match else '2025-10-26'
    status = status_match.group(1) if status_match else 'Complete'

    # Remove markdown header section
    content = re.sub(
        r'^# Rholang.*?\n\n\*\*Version:\*\*.*?---\n\n',
        '',
        content,
        flags=re.DOTALL
    )

    # Convert headers: ## Header -> ** Header
    def convert_header(match):
        level = len(match.group(1))
        title = match.group(2)
        return '*' * level + ' ' + title

    content = re.sub(r'^(#{2,})\s+(.+)$', convert_header, content, flags=re.MULTILINE)

    # Convert code blocks (before inline to avoid conflicts)
    content = re.sub(
        r'```(\w+)?\n(.*?)\n```',
        lambda m: convert_code_block(m),
        content,
        flags=re.DOTALL
    )

    # Convert inline math/code
    content = convert_inline_math(content)

    # Convert bold/italic
    content = re.sub(r'\*\*([^*\n]+)\*\*', r'*\1*', content)  # **bold** -> *bold*

    # Convert links: [text](url) -> [[url][text]]
    content = re.sub(r'\[([^\]]+)\]\(([^)]+)\)', r'[[\2][\1]]', content)

    # Convert tables (markdown to org)
    def convert_table(match):
        table = match.group(0)
        lines = table.split('\n')
        org_lines = []
        for i, line in enumerate(lines):
            if '|' in line:
                # Remove leading/trailing pipes and spaces
                cells = [cell.strip() for cell in line.split('|')[1:-1]]
                org_line = '| ' + ' | '.join(cells) + ' |'
                org_lines.append(org_line)
                # Add hline after header
                if i == 0:
                    org_lines.append('|' + '-' * (len(org_line) - 2) + '|')
        return '\n'.join(org_lines)

    # Find and convert tables
    content = re.sub(
        r'(\|.+\|\n)+',
        convert_table,
        content,
        flags=re.MULTILINE
    )

    return version, date, status, content

def create_org_header(version, date, status):
    """Create org-mode document header"""
    return f"""#+TITLE: Rholang Structural Error Correction via Hierarchical Automata Composition
#+AUTHOR: Claude (AI Assistant) & Dylon Edwards
#+DATE: {date}
#+OPTIONS: toc:3 num:3 ^:{{}}
#+LATEX_CLASS: article
#+LATEX_CLASS_OPTIONS: [11pt,a4paper]
#+LATEX_HEADER: \\usepackage{{amsmath}}
#+LATEX_HEADER: \\usepackage{{amssymb}}
#+LATEX_HEADER: \\usepackage{{amsthm}}
#+LATEX_HEADER: \\usepackage{{mathtools}}
#+LATEX_HEADER: \\usepackage{{unicode-math}}
#+LATEX_HEADER: \\usepackage{{listings}}
#+LATEX_HEADER: \\usepackage{{xcolor}}
#+LATEX_HEADER: \\usepackage{{hyperref}}
#+LATEX_HEADER: \\usepackage{{geometry}}
#+LATEX_HEADER: \\usepackage{{fancyvrb}}
#+LATEX_HEADER: \\usepackage{{tikz}}
#+LATEX_HEADER: \\geometry{{left=1in,right=1in,top=1in,bottom=1in}}
#+LATEX_HEADER: \\lstset{{basicstyle=\\ttfamily\\small,breaklines=true,columns=flexible}}
#+LATEX_HEADER: \\newtheorem{{theorem}}{{Theorem}}
#+LATEX_HEADER: \\newtheorem{{definition}}{{Definition}}
#+LATEX_HEADER: \\newtheorem{{lemma}}{{Lemma}}
#+LATEX_HEADER: \\newtheorem{{corollary}}{{Corollary}}

#+begin_abstract
*Version:* {version}

*Status:* {status}

*Related Documents:*
- ~docs/HIERARCHICAL_CORRECTION_DESIGN.md~ - Multi-level correction framework
- ~docs/PREFIX_MATCHING_DESIGN.md~ - Levenshtein automata foundation
- ~docs/SUFFIX_AUTOMATON_DESIGN.md~ - Substring matching extension

This document presents a comprehensive, theoretically-grounded hierarchical
error correction system for Rholang (the RChain smart contract language) that
integrates automata theory, formal language theory, compiler design, and
program analysis to provide multi-level error correction spanning lexical,
syntactic, structural, and semantic dimensions.
#+end_abstract

#+TOC: headlines 3

"""

def main():
    input_file = 'docs/RHOLANG_STRUCTURAL_CORRECTION.md'
    output_file = 'docs/RHOLANG_STRUCTURAL_CORRECTION.org'

    print(f"Converting {input_file} to Org-mode...")

    with open(input_file, 'r', encoding='utf-8') as f:
        content = f.read()

    version, date, status, processed_content = process_content(content)
    org_header = create_org_header(version, date, status)

    final_content = org_header + processed_content

    with open(output_file, 'w', encoding='utf-8') as f:
        f.write(final_content)

    lines = len(final_content.splitlines())
    print(f"✓ Converted successfully!")
    print(f"  Output: {output_file}")
    print(f"  Lines: {lines}")
    print(f"  Original: {len(content.splitlines())} lines")
    print()
    print("To compile to PDF:")
    print("  1. In Emacs: Open file, then C-c C-e l p")
    print("  2. Command line: emacs --batch \\")
    print(f"       --eval \"(require 'ox-latex)\" \\")
    print(f"       --visit={output_file} \\")
    print(f"       --funcall org-latex-export-to-pdf")
    print()
    print("Note: Requires LaTeX distribution (TeXLive, MiKTeX, etc.)")

if __name__ == '__main__':
    main()
