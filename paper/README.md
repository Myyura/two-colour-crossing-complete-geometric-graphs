# Manuscript

The new manuscript is **Two-colour crossing minimization in complete geometric graphs is NP-hard**, by **Myyura**, **The Kai Project**, dated 22 October 2026. The editable [LaTeX project](tex/main.tex) is accompanied by [manuscript.pdf](manuscript.pdf). The source was newly written from the verified construction and its effective-reduction argument; it is not a reconstruction of the earlier reference draft's missing TeX.

The paper and its accompanying documentation are licensed under **CC BY 4.0**, as selected by the author; see the [license](../LICENSES/CC-BY-4.0.txt). The code has the separate license described in the [repository license notice](../LICENSE). The public edition identifies the author as Myyura and the affiliation as The Kai Project.

## Source layout

`tex/main.tex` supplies the preamble, abstract and document structure, and loads author metadata with `\input{metadata}`. Its dependencies are:

- `tex/metadata.tex`: the public author Myyura, affiliation The Kai Project, and an empty email field;
- `tex/sections/introduction.tex`: problem statement, related work, main theorem, proof outline and repository link;
- `tex/sections/stability.tex`: continuous stability, finite grids and probe freezing;
- `tex/sections/geometry.tex`: geometric construction and deterministic rational coordinates;
- `tex/sections/core.tex`: source encoding, palette fields and local costs;
- `tex/sections/reduction.tex`: all-edge accounting, scale separation and complexity;
- `tex/sections/formalization.tex`: formal statement, verification and trust boundary;
- `tex/sections/completion.tex`: a concrete obstruction to naive completion;
- `tex/references.bib`: the bibliography.

These are ten source files in total: `main.tex`, `metadata.tex`, seven section files and `references.bib`. The project uses standard LaTeX packages and no external figures, private paths or custom style files. A conventional build uses pdfLaTeX, BibTeX, then two further pdfLaTeX passes from `tex/`. The release build and PDF checks are recorded with the [manuscript review](../audit/new-manuscript-review.md).

From a maintained Git checkout, run `python3 tools/build_paper.py` at the repository root, inspect the resulting PDF, then run `python3 tools/repository.py refresh` and `python3 tools/repository.py export`. The refresh deliberately updates the public byte manifest after an accepted rebuild; generated PDF metadata can change between runs. The exported `.local/build/releases/public-source.tar.gz` contains the public edition's ten source files and generated `main.bbl`, for eleven archive entries. The current 34-page manuscript was compiled with Tectonic. Its introduction and 12-entry bibliography were expanded, the formalization discussion was moved out of the abstract, and the prose was reviewed. Both source archives were independently extracted, compiled and compared with their respective PDFs. Current source and PDF bytes are bound by the release manifest. See the [build and package checks](../audit/README.md#manuscript-build-and-package-checks).

The default `python3 tools/build_paper.py` builds the public edition. For an optional local submission edition, run `python3 tools/build_paper.py --edition arxiv`. It copies the current public source into `.local/arxiv/tex/`, replaces the author metadata using the ignored `.local/arxiv/metadata.json`, and generates `.local/arxiv/manuscript.pdf` and `.local/arxiv/arxiv-source.tar.gz`. The mathematical body is copied from the public edition rather than maintained separately. The entire `.local/arxiv/` directory is ignored, and `repository.py export` neither processes nor includes it.

Read the [formalization notes](formalization-notes.md), [formalization scope](../docs/formalization.md), [effective reduction](../docs/effective-reduction.md), and [audit overview](../audit/README.md) for the precise claims and verification boundaries. The new manuscript consistently uses the conservative local bound `2 S W^4` and strict error bound `2^18 (E_minus + E_plus) < Delta`.

[Submission notes](submission-notes.md) describe the official arXiv requirements checked on 22 October 2026 and the final author-controlled submission steps. No arXiv upload or submission has been performed.
