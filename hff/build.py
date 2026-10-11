#!/usr/bin/env python3
"""Build the Lean-friendly HFF document, measure proof lengths, check the HFF conditions, and
write the map (JSON + HTML viewer) from the single source in blocks.py / overview.py.

Lean-friendly version: every non-remark block carries the names of its Lean declarations
(blocks.py, argument lean=), printed in grey under the statement and stored in the map JSON
("lean"). If hff/lean_status.json exists (block number -> "proved" / "sorry" / "definition"),
the status is added to the map JSON ("lean_status") and shown by the viewer. If the Lean sources
../PalindromicPowers/*.lean are present, the names are checked against their [HFF n] docstrings
(read only)."""
import json
import os
import re
import shutil
import subprocess
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import blocks as SRC          # noqa: E402
import overview as OV         # noqa: E402
import viewer_patch           # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, 'out')
BUDGET = 300
STMT_BUDGET = 2 * BUDGET
BASENAME = 'palindromic_powers_hff_lean'
LEAN_DIR = os.path.join(os.path.dirname(HERE), 'PalindromicPowers')
LEAN_STATUS_FILE = os.path.join(HERE, 'lean_status.json')

KINDWORD = {'def': 'Definition', 'lem': 'Lemma', 'thm': 'Theorem', 'rem': 'Remark'}
ENV = {'def': 'hffdef', 'lem': 'hfflem', 'thm': 'hffthm', 'rem': 'hffrem'}
IDPRE = {'def': 'D', 'lem': 'L', 'thm': 'T', 'rem': 'R'}
JSONKIND = {'def': 'definition', 'lem': 'lemma', 'thm': 'theorem'}

BLOCKS = SRC.BLOCKS
NUM, KIND = {}, {}
for i, b in enumerate(BLOCKS, 1):
    b['number'] = i
    b['id'] = IDPRE[b['kind']] + str(i)
    assert b['label'] not in NUM, b['label']
    NUM[b['label']] = i
    KIND[b['label']] = b['kind']

LABEL = r'@[DLTR]:[A-Za-z0-9]+'
RUN = re.compile(LABEL + r'(?:(?:, and |, | and |--)' + LABEL + r')*')
PIECE = re.compile(r'(' + LABEL + r')|(, and |, | and |--)')


def render_run(run, mode):
    labels, seps = [], []
    for lab, sep in PIECE.findall(run):
        if lab:
            labels.append(lab[1:])
        else:
            seps.append(sep)
    for l in labels:
        if l not in NUM:
            raise SystemExit('unknown label ' + l)
    kinds = {KIND[l] for l in labels}

    def numtxt(l):
        return (r'\hyperref[%s]{%d}' % (l, NUM[l])) if mode == 'tex' else str(NUM[l])

    def septxt(s):
        if s == '--':
            return '--' if mode == 'tex' else '\u2013'
        return s
    if len(kinds) == 1:
        word = KINDWORD[kinds.pop()] + ('s' if len(labels) > 1 else '')
        out = word + ('~' if mode == 'tex' else ' ') + numtxt(labels[0])
        for s, l in zip(seps, labels[1:]):
            out += septxt(s) + numtxt(l)
        return out
    parts = []
    for l in labels:
        parts.append(KINDWORD[KIND[l]] + ('~' if mode == 'tex' else ' ') + numtxt(l))
    out = parts[0]
    for s, p in zip(seps, parts[1:]):
        out += septxt(s) + p
    return out


def refs_in(text):
    return [m[1:] for m in re.findall(LABEL, text)]


BLOCKRANGE = re.compile(r'blocks @([DLTR]:[A-Za-z0-9]+)--@([DLTR]:[A-Za-z0-9]+)')


def to_tex(text):
    text = re.sub(r'[ \t]*\n[ \t]*', ' ', text.strip())
    text = BLOCKRANGE.sub(lambda m: r'blocks~\hyperref[%s]{%d}--\hyperref[%s]{%d}'
                          % (m.group(1), NUM[m.group(1)], m.group(2), NUM[m.group(2)]), text)
    return RUN.sub(lambda m: render_run(m.group(0), 'tex'), text)


def to_json_text(text):
    """LaTeX source -> text for the map viewer (MathJax handles $...$)."""
    s = BLOCKRANGE.sub(lambda m: 'blocks %d--%d' % (NUM[m.group(1)], NUM[m.group(2)]),
                       re.sub(r'\s+', ' ', text.strip()))
    s = RUN.sub(lambda m: render_run(m.group(0), 'json'), s)
    s = re.sub(r'\\cite(\[[^\]]*\])?\{([^}]*)\}', lambda m: '[' + m.group(2) + ']', s)
    s = s.replace('\\[', '$$').replace('\\]', '$$')
    s = s.replace("Fej\\'er", 'Fejér').replace("\\'e", 'é')
    s = re.sub(r'\\allowbreak\s*', '', s)
    s = re.sub(r'\\texttt\{([^}]*)\}', lambda m: m.group(1).replace('\\_', '_'), s)
    s = s.replace('i.e.\\ ', 'i.e. ')
    # text-mode replacements outside math only (inside math, '' is a second derivative)
    parts = re.split(r'(\$[^$]*\$)', s)
    for i in range(0, len(parts), 2):
        parts[i] = (parts[i].replace('~', ' ').replace('--', '\u2013')
                    .replace('``', '\u201c').replace("''", '\u201d').replace('\\dots', '\u2026'))
    s = ''.join(parts)
    s = re.sub(r'\s+', ' ', s).strip()
    return s


PREAMBLE = r"""\documentclass[11pt]{article}
\IfFileExists{lmodern.sty}{\usepackage[T1]{fontenc}\usepackage{lmodern}}{\PassOptionsToPackage{expansion=false}{microtype}}
\usepackage[margin=1.1in]{geometry}
\usepackage{amsmath,amssymb,amsthm}
\usepackage{microtype}
\setlength{\emergencystretch}{2.5em}
\usepackage{xcolor}
\usepackage[colorlinks=true,linkcolor=blue!50!black,citecolor=blue!50!black,urlcolor=blue!50!black]{hyperref}
\newcounter{hffc}
\theoremstyle{definition}\newtheorem{hffdef}[hffc]{Definition}
\theoremstyle{plain}\newtheorem{hfflem}[hffc]{Lemma}\newtheorem{hffthm}[hffc]{Theorem}
\theoremstyle{remark}\newtheorem{hffrem}[hffc]{Remark}
\newcommand{\HFFmark}{\par\medskip\begin{center}{\Large$\maltese$}\end{center}\medskip\par}
\newcommand{\hffcost}{}
\newcommand{\setcost}[1]{\renewcommand{\hffcost}{#1}}
\newcommand{\rev}{\operatorname{rev}}
\newcommand{\cP}{\mathcal{P}}\newcommand{\cQ}{\mathcal{Q}}\newcommand{\cB}{\mathcal{B}}\newcommand{\cT}{\mathcal{T}}
\newcommand{\Z}{\mathbb{Z}}\newcommand{\R}{\mathbb{R}}\newcommand{\N}{\mathbb{N}}
"""


def compile_tex(name, runs=2):
    for _ in range(runs):
        r = subprocess.run(['pdflatex', '-interaction=nonstopmode', '-halt-on-error', name + '.tex'],
                           cwd=OUT, capture_output=True, text=True)
    log = open(os.path.join(OUT, name + '.log'), errors='replace').read()
    errors = [l for l in log.splitlines() if l.startswith('!')]
    over = [l for l in log.splitlines() if l.startswith('Overfull')]
    if errors or r.returncode != 0:
        print('\n'.join(errors[:10]) or r.stdout[-2000:])
        raise SystemExit('LaTeX failed: ' + name)
    return over


def page_texts(name, npages):
    out = []
    for p in range(1, npages + 1):
        t = subprocess.run(['pdftotext', '-f', str(p), '-l', str(p), name + '.pdf', '-'],
                           cwd=OUT, capture_output=True, text=True).stdout
        out.append(t)
    return out


def measure():
    """Typeset every proof (and statement) on its own page with the final line width and count
    the non-space characters of the extracted text."""
    provable = [b for b in BLOCKS if b['kind'] in ('lem', 'thm')]
    body = [PREAMBLE, r'\pagestyle{empty}\renewcommand{\qedsymbol}{}', r'\begin{document}']
    for b in provable:
        body.append(r'\begin{proof}' + to_tex(b['proof']) + r'\end{proof}\newpage')
    body.append(r'\end{document}')
    open(os.path.join(OUT, 'measure_proofs.tex'), 'w').write('\n'.join(body))
    compile_tex('measure_proofs', runs=1)
    texts = page_texts('measure_proofs', len(provable))
    for b, t in zip(provable, texts):
        t = t.replace('\f', '')
        # pdftotext may put a superscript fragment of the first line before "Proof."
        t = re.sub(r'Proof\.', '', t, count=1)
        b['length'] = len(re.sub(r'\s+', '', t))
    # statements (soft budget 2L)
    body = [PREAMBLE, r'\pagestyle{empty}', r'\begin{document}']
    stmts = [b for b in BLOCKS if b['kind'] != 'rem']
    for b in stmts:
        body.append((r'{\itshape ' if b['kind'] in ('lem', 'thm') else '{') + to_tex(b['statement']) + r'\par}\newpage')
    body.append(r'\end{document}')
    open(os.path.join(OUT, 'measure_stmts.tex'), 'w').write('\n'.join(body))
    compile_tex('measure_stmts', runs=1)
    texts = page_texts('measure_stmts', len(stmts))
    for b, t in zip(stmts, texts):
        b['stmt_length'] = len(re.sub(r'\s+', '', t.replace('\f', '')))


def check_structure():
    problems = []
    for b in BLOCKS:
        cites = []
        for l in refs_in(b['statement'] + ' ' + b['proof']):
            if l not in cites:
                cites.append(l)
        if b['kind'] != 'rem':
            for l in cites:
                if KIND[l] == 'rem':
                    problems.append('%s cites remark %s' % (b['label'], l))
        for l in cites:
            if NUM[l] >= b['number']:
                problems.append('%s (%d) cites later/self %s (%d)' % (b['label'], b['number'], l, NUM[l]))
        b['cites'] = [l for l in cites if KIND[l] != 'rem']
        if b['kind'] in ('lem', 'thm') and not b['proof']:
            problems.append('%s has no proof' % b['label'])
        if b['kind'] in ('def', 'rem') and b['proof']:
            problems.append('%s has a proof' % b['label'])
        words = re.sub(r'\$[^$]*\$', 'X', b['header']).split()
        if len(words) > 6:
            problems.append('%s header has %d words' % (b['label'], len(words)))
    thm = [b for b in BLOCKS if b['kind'] == 'thm']
    if len(thm) != 1:
        problems.append('need exactly one theorem')
    T = thm[0]
    last_nonrem = [b for b in BLOCKS if b['kind'] != 'rem'][-1]
    if last_nonrem is not T:
        problems.append('theorem is not the last lemma')
    seen, stack = {T['label']}, [T['label']]
    bylab = {b['label']: b for b in BLOCKS}
    while stack:
        for c in bylab[stack.pop()]['cites']:
            if c not in seen:
                seen.add(c)
                stack.append(c)
    for b in BLOCKS:
        if b['kind'] != 'rem' and b['label'] not in seen:
            problems.append('%s does not lead to the theorem' % b['label'])
    return problems


def lean_tex(names):
    """The grey line under a statement naming its Lean declarations (not part of the statement)."""
    tt = ', '.join(r'\texttt{%s}' % n.replace('_', r'\_') for n in names)
    return r'\par\nopagebreak\noindent{\upshape\footnotesize\color{black!55}Lean: %s\par}' % tt


def lean_declarations():
    """{block number: [declaration names]} from the [HFF n] docstrings of the Lean sources, or None."""
    if not os.path.isdir(LEAN_DIR):
        return None
    decl = re.compile(r'/--\s*\*\*\[HFF (\d+)\](?:(?!-/).)*-/\s*(?:@\[[^\]]*\]\s*)?'
                      r'(?:(?:noncomputable|private|protected|partial|unsafe)\s+)*'
                      r'(?:def|theorem|lemma|abbrev|structure|instance|class|inductive)\s+([^\s:({\[]+)', re.S)
    found = {}
    for fn in sorted(os.listdir(LEAN_DIR)):
        if fn.endswith('.lean'):
            for n, name in decl.findall(open(os.path.join(LEAN_DIR, fn), encoding='utf-8').read()):
                found.setdefault(int(n), []).append(name)
    return found


def check_lean_names():
    found = lean_declarations()
    if found is None:
        return 'Lean sources not found (%s); names not checked' % LEAN_DIR
    problems = []
    for b in BLOCKS:
        want, got = b['lean'], found.get(b['number'], [])
        if b['kind'] == 'rem':
            if got:
                problems.append('remark %d has Lean declarations %s' % (b['number'], got))
        elif sorted(want) != sorted(got):
            problems.append('%d %s: blocks.py %s, Lean %s' % (b['number'], b['label'], want, got))
    for n in sorted(set(found) - {b['number'] for b in BLOCKS}):
        problems.append('Lean declarations for unknown block %d: %s' % (n, found[n]))
    return '; '.join(problems) or 'match the [HFF n] docstrings (%d declarations)' % sum(map(len, found.values()))


def load_lean_status():
    """{block number: status} from hff/lean_status.json, or {} if the file does not exist.
    Keys may be numbers or strings containing the number ("5", "HFF 5"); values are strings
    ("proved", "sorry", "definition") or objects with a "status" field."""
    if not os.path.exists(LEAN_STATUS_FILE):
        return {}
    raw = json.load(open(LEAN_STATUS_FILE, encoding='utf-8'))
    if isinstance(raw, dict) and isinstance(raw.get('blocks'), dict):
        raw = raw['blocks']
    out = {}
    for k, v in raw.items():
        m = re.search(r'\d+', str(k))
        if isinstance(v, dict):
            v = v.get('status')
        if m and isinstance(v, str):
            out[int(m.group(0))] = v
    return out


def write_document():
    lines = [PREAMBLE]
    lines.append(r'\renewcommand{\qedsymbol}{{\footnotesize\color{black!55}[\hffcost]}\enspace\openbox}')
    lines.append(r'\title{%s\\[0.4em]\large %s}' % (OV.TITLE, OV.SUBTITLE))
    lines.append(r'\author{}\date{October 2026}')
    lines.append(r'\begin{document}')
    lines.append(r'\maketitle')
    lines.append(r'\section*{Overview}')
    for head, text in OV.OVERVIEW:
        lines.append(r'\paragraph{%s.} %s' % (head, to_tex(text.strip())))
        lines.append('')
    lines.append(r'\HFFmark')
    lines.append('')
    for b in BLOCKS:
        env = ENV[b['kind']]
        lines.append(r'\begin{%s}[%s]\label{%s}' % (env, b['header'], b['label']))
        lines.append(to_tex(b['statement']))
        if b['lean']:
            lines.append(lean_tex(b['lean']))
        lines.append(r'\end{%s}' % env)
        if b['proof']:
            lines.append(r'\begin{proof}\setcost{length %d/%d}%s' % (b['length'], BUDGET, to_tex(b['proof'])))
            lines.append(r'\end{proof}')
        lines.append('')
    lines.append(r'\begin{thebibliography}{DMRSS}')
    for key, text in OV.REFERENCES:
        lines.append(r'\bibitem[%s]{%s} %s' % (key, key, text))
    lines.append(r'\end{thebibliography}')
    lines.append(r'\end{document}')
    open(os.path.join(OUT, BASENAME + '.tex'), 'w').write('\n'.join(lines) + '\n')
    over = compile_tex(BASENAME, runs=2)
    # plain-text copy of the final PDF, regenerated on every build so it cannot go stale
    subprocess.run(['pdftotext', BASENAME + '.pdf', 'full.txt'], cwd=OUT, check=True)
    return over


def write_map():
    """Returns the number of blocks with a Lean status (0 if lean_status.json is absent)."""
    data = {
        'slug': 'palindromic-perfect-powers-lean',
        'title': 'Palindromic perfect powers (Lean-friendly)',
        'theorem': [b['id'] for b in BLOCKS if b['kind'] == 'thm'][0],
        'budget': BUDGET,
        'overview': {
            'theorem': to_json_text(OV.OVERVIEW_THEOREM),
            'method': ' '.join(to_json_text(t) for t in (OV.OVERVIEW_START, OV.OVERVIEW_STRATEGY,
                                                         OV.OVERVIEW_ERROR, OV.OVERVIEW_PARAMS)),
            'structure': to_json_text(OV.OVERVIEW_ROUTINE) + ' Prerequisites: ' + to_json_text(OV.OVERVIEW_PREREQ),
        },
        'blocks': [],
        'references': [{'key': k, 'text': to_json_text(t)} for k, t in OV.REFERENCES],
    }
    bylab = {b['label']: b for b in BLOCKS}
    status = load_lean_status()
    for b in BLOCKS:
        if b['kind'] == 'rem':
            continue
        e = {'id': b['id'], 'kind': JSONKIND[b['kind']], 'number': b['number'],
             'header': to_json_text(b['header']), 'statement': to_json_text(b['statement']),
             'lean': b['lean']}
        if b['number'] in status:
            e['lean_status'] = status[b['number']]
        if b['proof']:
            e['proof'] = to_json_text(b['proof'])
            e['length'] = b['length']
        e['cites'] = [bylab[c]['id'] for c in b['cites']]
        data['blocks'].append(e)
    js = json.dumps(data, ensure_ascii=False, indent=1)
    open(os.path.join(OUT, BASENAME + '_map.json'), 'w').write(js + '\n')

    html = open(os.path.join(HERE, 'viewer_template.html')).read()
    a = html.index('<script type="application/json" id="hff-data">')
    a = html.index('>', a) + 1
    z = html.index('</script>', a)
    html = html[:a] + '\n' + js.replace('</', '<\\/') + '\n' + html[z:]
    nblocks = len(data['blocks'])
    subs = [
        ('<title>Primes 3 mod 4 Proof Map</title>', '<title>Palindromic Powers Proof Map (Lean)</title>'),
        ('<span class="eyebrow">HFF map · worked example</span>', '<span class="eyebrow">HFF map · Lean-friendly</span>'),
        ('<h1 id="docTitle">Infinitely many primes ≡ 3 (mod 4)</h1>', '<h1 id="docTitle">Palindromic perfect powers</h1>'),
        ('<span id="progressText">Verified 0/5</span>', '<span id="progressText">Verified 0/%d</span>' % nblocks),
        ("ab.innerHTML = 'This map accompanies the note <em>Checking AI-Generated Proofs: The Human Friendly Form</em> by Siddharth Iyer. It renders the worked example of Section 7 from the block data embedded in this file.';",
         "ab.innerHTML = 'This map accompanies the Lean-friendly version of the document <em>Palindromic perfect powers in Human Friendly Form</em>, whose statements match the Lean formalization, and renders its blocks from the data embedded in this file. Under each statement the reading panel names the corresponding Lean declarations (and their status in Lean, when known). The viewer is the prototype from the note <em>Checking AI-Generated Proofs: The Human Friendly Form</em> by Siddharth Iyer.';"),
        ("tex: { inlineMath: [['$', '$']], displayMath: [['$$', '$$']] },",
         "tex: { inlineMath: [['$', '$']], displayMath: [['$$', '$$']], macros: { rev: '\\\\operatorname{rev}', cP: '\\\\mathcal{P}', cQ: '\\\\mathcal{Q}', cB: '\\\\mathcal{B}', cT: '\\\\mathcal{T}', Z: '\\\\mathbb{Z}', R: '\\\\mathbb{R}', N: '\\\\mathbb{N}' } },"),
        ("""      s = s.replace(/\\b(Definition|Lemma|Theorem)s (\\d+) and (\\d+)/g, function (m0, kind, a, c) {
        return kind + 's ' + refLink(a, a) + ' and ' + refLink(c, c);
      });
      s = s.replace(/\\b(Definition|Lemma|Theorem) (\\d+)/g, function (m0, kind, a) { return refLink(a, m0); });""",
         """      s = s.replace(/\\b(Definition|Lemma|Theorem)s ((?:\\d+(?:, and |, | and |\\u2013))+\\d+)/g, function (m0, kind, list) {
        return kind + 's ' + list.replace(/\\d+/g, function (n) { return refLink(n, n); });
      });
      s = s.replace(/\\b(Definition|Lemma|Theorem) (\\d+)/g, function (m0, kind, a) { return refLink(a, m0); });"""),
    ]
    for o, n in subs:
        if html.count(o) != 1:
            raise SystemExit('viewer patch failed: ' + o[:60])
        html = html.replace(o, n)
    html = viewer_patch.patch(html)   # layout fixes, and the Lean line under the statement
    open(os.path.join(OUT, BASENAME + '_map.html'), 'w').write(html)
    return sum(1 for e in data['blocks'] if 'lean_status' in e)


def main():
    os.makedirs(OUT, exist_ok=True)
    problems = check_structure()
    measure()
    over = [b for b in BLOCKS if b.get('length', 0) >= BUDGET]
    long_st = [b for b in BLOCKS if b.get('stmt_length', 0) >= STMT_BUDGET]
    of = write_document()
    nstatus = write_map()
    lean_check = check_lean_names()
    n = {k: sum(1 for b in BLOCKS if b['kind'] == k) for k in KINDWORD}
    print('blocks: %d (definitions %d, lemmas %d, theorems %d, remarks %d)'
          % (len(BLOCKS), n['def'], n['lem'], n['thm'], n['rem']))
    lens = [b['length'] for b in BLOCKS if 'length' in b]
    print('proof lengths: max %d, mean %.0f; over budget: %s' % (max(lens), sum(lens) / len(lens),
          ', '.join('%s=%d' % (b['label'], b['length']) for b in over) or 'none'))
    print('statements over %d: %s' % (STMT_BUDGET, ', '.join('%s=%d' % (b['label'], b['stmt_length'])
                                                               for b in long_st) or 'none'))
    print('structure problems: %s' % ('; '.join(problems) or 'none'))
    print('Lean names: %s' % lean_check)
    print('Lean status: %s' % (('%d blocks from %s' % (nstatus, os.path.basename(LEAN_STATUS_FILE)))
                               if os.path.exists(LEAN_STATUS_FILE) else 'no lean_status.json (not shown)'))
    print('overfull boxes: %d' % len(of))
    for l in of[:10]:
        print('  ', l)
    for b in sorted(BLOCKS, key=lambda b: -b.get('length', 0))[:12]:
        if 'length' in b:
            print('  %-12s %3d' % (b['label'], b['length']))


if __name__ == '__main__':
    main()
