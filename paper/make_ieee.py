#!/usr/bin/env python3
"""Generate the IEEE Transactions on Information Theory version (paper/ieee/stgc-ieee.tex) from paper/stgc.tex.

Content is identical; only the format changes: IEEEtran journal class (single column for review, per T-IT's
Information for Authors; switch the class option to two-column for the final version), IEEE author footnote, index
terms, IEEEproof, the AI-use disclosure in the Acknowledgment (IEEE policy), and "Supplementary material" in place of
the arXiv "Ancillary files" section.
"""
import pathlib
import re

here = pathlib.Path(__file__).resolve().parent
s = (here / 'stgc.tex').read_text()

pre_end = s.index('\\begin{document}')
body = s[pre_end + len('\\begin{document}'):]

preamble = r"""% IEEE Transactions on Information Theory version. Review copy: single column, as required by T-IT.
% For the final version replace [journal,onecolumn,11pt] by [journal].
\documentclass[journal,onecolumn,11pt]{IEEEtran}
\usepackage[T1]{fontenc}
\usepackage{amsmath,amssymb}
\usepackage{booktabs}
\usepackage{hyperref}
\newtheorem{theorem}{Theorem}
\newtheorem{lemma}{Lemma}
\newtheorem{conjecture}{Conjecture}
\newtheorem{theoremA}{Theorem}
\renewcommand{\thetheoremA}{A}
\newtheorem{theoremB}{Theorem}
\renewcommand{\thetheoremB}{B}
\newcommand{\rk}{\operatorname{rk}}
\begin{document}
\title{Optimal Single-Track Gray Codes from Gray-Ordered Necklaces}
\author{Chris~Dzoba%
\thanks{C. Dzoba is an independent researcher (e-mail: chris@dzoba.com).}}
\maketitle
"""

body = body.replace('\\maketitle\n', '', 1)
# abstract + index terms
body = body.replace('\\end{abstract}', '\\end{abstract}\n\n\\begin{IEEEkeywords}\nSingle-track Gray codes, necklaces, '
                    'reflected Gray code, Hamilton cycles, absolute rotary encoders, formal verification, Lean.\n'
                    '\\end{IEEEkeywords}', 1)
# proofs
body = re.sub(r'\\begin\{proof\}\[([^\]]*)\]', r'\\begin{IEEEproof}[\1]', body)
body = body.replace('\\begin{proof}', '\\begin{IEEEproof}').replace('\\end{proof}', '\\end{IEEEproof}')
# IEEEtran adds a colon after run-in paragraph heads: drop their trailing periods
body = re.sub(r'\\paragraph\{([^{}]*(?:\{[^{}]*\}[^{}]*)*)\.\}', r'\\paragraph{\1}', body)
# first paragraph drop cap is optional in IEEEtran; keep plain text.
# ancillary files -> supplementary material
body = body.replace('\\section*{Ancillary files}\nThe arXiv ancillary files contain',
                    '\\section*{Supplementary material}\nThe supplementary material (also posted as ancillary files '
                    'with the arXiv version) contains')
body = body.replace('(ancillary files)', '(supplementary material)')
body = body.replace("exceed arXiv's size limit and are\navailable at", 'are available at')
# AI disclosure -> Acknowledgment (IEEE requires disclosure of AI-generated content in the acknowledgments)
body = body.replace('\\section*{Use of AI tools}', '\\section*{Acknowledgment}')
# IEEE reference style is close enough to the existing thebibliography; keep it.
out = here / 'ieee' / 'stgc-ieee.tex'
out.parent.mkdir(exist_ok=True)
out.write_text(preamble + body)
print('wrote', out)
