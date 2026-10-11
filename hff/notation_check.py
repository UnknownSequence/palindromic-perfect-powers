#!/usr/bin/env python3
"""Heuristic check that every block cites the block defining each symbol it uses.

For each (pattern, definers) pair: if a block's statement or proof matches the pattern, the block
must be one of the definers or cite one of them directly. Prints the violations; a few may be false
positives (local variables with the same letter), which are listed in ALLOW."""
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import blocks as SRC  # noqa: E402

B = SRC.BLOCKS
NUM = {b['label']: i for i, b in enumerate(B, 1)}
LAB = r'@([DLTR]:[A-Za-z0-9]+)'

SYMBOLS = [
    # conventions
    (r'(?<![A-Za-z\\])e\(', ('D:conv',)),
    (r'\\\|', ('D:conv',)),
    (r'\\log(?!_)', ('D:conv',)),
    (r'\\ll(?![a-z])', ('D:conv',)),
    (r'\$L\$ large', ('D:conv',)),
    (r'\\bmod', ('D:conv',)),
    # digits
    (r'\\rev', ('D:digits',)),
    (r'[Dd]igits', ('D:digits', 'L:digits')),
    # reversal transform
    (r'\\Psi', ('D:psi',)),
    (r'M\(\\ell\)', ('D:psi',)),
    (r'S\(s\)', ('D:psi',)),
    (r'(?<![A-Za-z\\])f\(', ('D:psi',)),
    (r'\\theta_i|\\theta_\{i', ('D:psi',)),
    (r'(?<![A-Za-z\\])Q(?![A-Za-z_])', ('D:psi', 'D:phase', 'D:setB')),
    (r'u_\*', ('L:gap',)),
    (r'\\varepsilon_\*', ('L:gap',)),
    (r"\\ell'", ('D:bad',)),
    (r'b\(\\ell\)', ('D:bad',)),
    (r'\\beta_[ns]\(', ('D:bad',)),
    (r'(?<![a-z])bad(?![a-z])', ('D:bad',)),
    (r'\\rho', ('L:twsum',)),
    (r'(?<![A-Za-z\\_])c(?![A-Za-z_])', ('L:saving', 'D:par')),
    # palindromes, nodes
    (r'\\cP', ('D:pal',)),
    (r'\\cQ', ('D:pal',)),
    (r'(?<![A-Za-z\\])X(?![A-Za-z])', ('D:pal',)),
    (r'(?<![a-z])node', ('D:node',)),
    (r'T_b|T_\{b', ('D:node',)),
    (r'I_b', ('D:node',)),
    (r'Z_b', ('D:node',)),
    (r'x_b', ('D:node',)),
    (r'y_0|y_1(?!,\\dots)', ('D:node',)),
    (r'Z\(t', ('D:node',)),
    # phases
    (r'\\alpha_b', ('D:phase',)),
    (r'\\beta_b', ('D:phase',)),
    (r'd_b|d_\{b', ('D:phase',)),
    (r'\\delta_b', ('D:phase',)),
    (r'\\theta_\{b', ('D:phase',)),
    (r'n_b', ('D:phase',)),
    (r'\\Lambda', ('D:phase', 'D:setB')),
    (r'(?<![A-Za-z\\])Z(?![A-Za-z_(+])', ('D:phase', 'D:setB')),
    (r'\\phi_b', ('D:arch',)),
    (r'\\lambda_b', ('D:arch',)),
    (r'\\delta\(', ('D:arch',)),
    # detection
    (r'(?<![A-Za-z\\])K(?![A-Za-z])', ('L:K',)),
    (r'(?<![A-Za-z\\])F(?![A-Za-z])', ('D:maj',)),
    (r'\\hat F', ('D:maj',)),
    (r'E\(\\cB', ('D:err',)),
    # g-parts
    (r'm_g', ('D:gpart',)),
    (r'v_p', ('D:gpart',)),
    (r'\\omega\(g\)', ('D:gpart',)),
    (r'\\tau', ('D:gpart',)),
    (r'(?<![A-Za-z\\])P(?![A-Za-z])', ('D:gpart',)),
    # counting data
    (r'Z_\+', ('D:count',)),
    (r'y_b', ('D:count',)),
    (r'\\Phi_b', ('D:count',)),
    (r'W_\\ell', ('D:count',)),
    (r'h_d|h_\{d', ('D:curve',)),
    (r'\\cT', ('D:curve',)),
    (r'\\mu(?![a-z])', ('D:curve',)),
    (r'\\Delta', ('D:curve',)),
    (r'\\cB_2', ('L:large',)),
    (r'(?<![A-Za-z\\])V(?![A-Za-z])', ('L:E',)),
    # parameters
    (r'\\eta', ('D:par',)),
    (r'\\nu(?![a-z])', ('D:par',)),
    (r'(?<![A-Za-z\\])C(?![A-Za-z\'_])', ('L:saving', 'D:par')),
]

# (block, pattern) pairs where the letter is a local variable of that block
ALLOW = {
    ('L:fejer', 'K'), ('L:fejerlow', 'K'), ('L:digits', 'igits'),
    ('L:strings', 'igits'), ('L:dist', 'R'), ('L:mdiv', 'P'),
    # Lean-friendly version: Lemma 56 is stated for any integer Q >= 1 (as in Lean), and the spacing
    # lemmas 80-81 are general statements with their own mu and Delta (as in Lean)
    ('L:mult', 'Q'), ('L:space1', 'mu'), ('L:space', 'mu'), ('L:space', 'Delta'),
}


def main():
    bad = []
    for b in B:
        if b['kind'] == 'rem':
            continue
        text = b['statement'] + ' ' + b['proof']
        cites = set(re.findall(LAB, text))
        clean = re.sub(LAB, ' ', text)
        # math segments with macro names removed, so that products such as kQ or dZ are seen
        math = ' '.join(re.findall(r'\$[^$]*\$|\\\[.*?\\\]', clean, flags=re.S))
        math = re.sub(r'\\[A-Za-z]+', ' ', math)
        for pat, definers in SYMBOLS:
            if b['label'] in definers:
                continue
            relaxed = pat.replace('(?<![A-Za-z\\\\])', '(?<![\\\\])').replace('(?<![A-Za-z\\\\_])', '(?<![\\\\_])')
            if not (re.search(pat, clean) or (relaxed != pat and re.search(relaxed, math))):
                continue
            if any(d in cites for d in definers):
                continue
            # used before it is defined: a local symbol of the same name
            if all(NUM[d] > NUM[b['label']] for d in definers):
                continue
            key = (b['label'], re.sub(r'[^A-Za-z]', '', pat)[:5])
            if any(b['label'] == a and k in pat for a, k in ALLOW):
                continue
            bad.append((NUM[b['label']], b['label'], pat, definers))
    for n, lab, pat, d in bad:
        print('%3d %-12s uses %-28s but cites none of %s' % (n, lab, pat, ', '.join(d)))
    print('%d possible omissions' % len(bad))


if __name__ == '__main__':
    main()
