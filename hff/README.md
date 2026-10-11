# Scripts for the Lean-friendly HFF version of the palindromic-powers proof

These files generate `out/palindromic_powers_hff_lean.tex/.pdf` and the map
(`out/palindromic_powers_hff_lean_map.json/.html`) from a single source. They are adapted from the
scripts that build the original HFF document, edited so that the document matches the Lean formalization in `../PalindromicPowers/`:
the 102 blocks keep their order, labels and numbers, their statements are those of the Lean
declarations, and every definition, lemma and theorem names its Lean declarations (those whose
docstring begins `**[HFF n]**`). `LEAN_CONVENTIONS.md` has the table of notation and the list of
the Lean-friendly changes.

| File | Purpose |
|---|---|
| `blocks.py` | The blocks of Part II (definitions, lemmas, remarks, theorem), in order. Cross references are written `@D:label`, `@L:label`, `@T:label`. The argument `lean=` of `B()` lists the Lean declarations of the block. |
| `overview.py` | Part I (the overview) and the reference list. |
| `build.py` | Numbers the blocks, renders the references, measures every proof length (each proof typeset alone, text extracted with `pdftotext`, non-space characters counted), checks the HFF conditions (backward citations only, no citations of remarks, theorem last and the only sink, headers of at most 6 words, proofs under 300, statements under 600), checks the `lean=` names against the `[HFF n]` docstrings of `../PalindromicPowers/*.lean` (read only; skipped if the sources are absent), and writes the `.tex`, `.pdf`, `full.txt`, map JSON and map HTML into `out/`. |
| `notation_check.py` | Heuristic check that every block cites the block defining each symbol it uses (reports possible omissions). |
| `viewer_template.html` | The map viewer from `hff_map_example.html`; `build.py` embeds the JSON into a copy of it. |
| `viewer_patch.py` | Changes to the viewer applied by `build.py`: the page never gets wider than the window, the reading panel is wider and resizable, wide formulas are scaled or scroll; and (Lean version) the panel shows the Lean names under the statement, with the Lean status when known, and the search box matches Lean names. |
| `tools/pdftotext.swift` | A PDFKit replacement for poppler's `pdftotext` (see below). |
| `LEAN_CONVENTIONS.md` | HFF notation ↔ Lean names, the conventions, and the list of Lean-friendly changes. |

## Building

Needs `pdflatex` and the `pdftotext` replacement in `tools/`:

```
cd hff
swiftc -O -o tools/pdftotext tools/pdftotext.swift     # once
export PATH="$PWD/tools:/Library/TeX/texbin:$PATH"      # tools/ first
python3 build.py            # build everything into out/ and print the checks
python3 notation_check.py   # should report 0 possible omissions
```

`build.py` prints the block counts, the maximum and mean proof length, the proofs and statements
over budget, the structure problems (should be `none`), the result of the Lean name check and
whether a Lean status file was used.

**Lengths are measured with a PDFKit text extractor.** poppler is not installed here, so
`tools/pdftotext` (compiled from `tools/pdftotext.swift`) stands in for it. It supports exactly the
two invocations `build.py` uses: `pdftotext -f P -l P file.pdf -` (text of page `P` to stdout) and
`pdftotext file.pdf out.txt` (all pages, each followed by a form feed). Ligatures are expanded into
their letters. PDFKit does not extract some large-operator glyphs (such as `∑` and `∏`), so its
counts can differ from poppler's by a few characters: on the original document
(`palindromic_powers_hff.tex`, measured with poppler) the PDFKit counts were equal for 50 of the 84
proofs and lower by 1–6 characters for the others, never higher. The proofs here stay far below 300
(the maximum is printed by the build).

## Lean names and Lean status

* The Lean names of a block appear in the PDF as a small grey line directly under the statement
  ("Lean: `rev_involution`"; not counted in the statement length), and in the map JSON as the field
  `"lean": [names]`.
* If `hff/lean_status.json` exists, it maps block numbers to `"proved"`, `"sorry"` or
  `"definition"`, e.g. `{"5": "proved", "6": "sorry", "9": "definition"}` (keys may also be
  numbers or strings such as `"HFF 5"`; values may be objects with a `"status"` field). The build
  then adds `"lean_status"` to the blocks in the map JSON, and the reading panel shows it next to the
  names: "Lean: rev_involution · proved in Lean". Without the file the build works the same and no
  status is shown. The file is written by `#hff_status` in `../PalindromicPowers/Audit.lean`
  (`lake env lean PalindromicPowers/Audit.lean`, run from `palindromic_powers_lean/`); rebuild the
  map afterwards with `python3 build.py`.

The map loads MathJax from a CDN, so formulas render only with an internet connection
(otherwise a plain-text fallback is shown).
