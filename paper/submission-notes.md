# arXiv preparation

Checked against official arXiv documentation on **22 October 2026**. No upload, account action, endorsement request, or submission has been performed.

The newly authored manuscript is available as a [LaTeX source project](tex/main.tex) and [compiled PDF](manuscript.pdf). arXiv requires TeX source for TeX-authored articles; its PDF guidance says exceptions to PDF-only submission are considered case by case. The new editable source, rather than the earlier reference PDF, is therefore the submission material. [Submission overview](https://info.arxiv.org/help/submit/index.html), [PDF guidance](https://info.arxiv.org/help/submit_pdf.html).

## Public-edition metadata

| Field | Value |
| --- | --- |
| Title | Two-colour crossing minimization in complete geometric graphs is NP-hard |
| Author | Myyura |
| Affiliation | The Kai Project |
| Manuscript license | CC BY 4.0, selected by the author |
| Main source | `tex/main.tex` |
| Included source | `tex/metadata.tex`, seven files in `tex/sections/`, and `tex/references.bib` |
| arXiv identifier / submission | None |

These are the public edition's metadata. An optional local submission edition may use separate metadata from the ignored `.local/arxiv/metadata.json`; this public document does not record those values. Run `python3 tools/build_paper.py --edition arxiv` to create that edition's TeX source, PDF and `arxiv-source.tar.gz` under the ignored `.local/arxiv/` directory. These files are excluded from the public export, which produces `.local/build/releases/github.zip` and `.local/build/releases/public-source.tar.gz`.

The manuscript's CC BY 4.0 license is separate from the code's Apache-2.0 license. arXiv requires the submitter to hold the rights needed to grant the selected license, and a license on an announced version is irrevocable. This note records the author's choice; it does not execute an arXiv license grant. [arXiv license information](https://info.arxiv.org/help/license/index.html).

## Submission bundle and final checks

The source archive should contain `main.tex`, every included section, and `references.bib` or an appropriate generated `main.bbl`, with relative paths preserved. This manuscript has no external figures or custom styles. Exclude build products, the earlier reference draft, review reports, Lean files, and unrelated repository material. arXiv supports ZIP or TAR source uploads. [TeX submission instructions](https://info.arxiv.org/help/submit_tex.html).

Local compilation and the [manuscript review](../audit/new-manuscript-review.md) support preparation, but do not replace review of arXiv's generated output. The submitter must review that PDF before completing submission. A PDF-only file, if an exception is granted, must be one machine-readable document with embedded outline fonts and no embedded JavaScript. [TeX processing](https://info.arxiv.org/help/submit_tex.html), [PDF requirements](https://info.arxiv.org/help/submit_pdf.html).

The author still needs to confirm the submission title, abstract, author metadata, category, account eligibility and any endorsement requirement in the actual submission workflow. arXiv accepts registered submitters, may require endorsement for a new category, and moderates submissions. This local package does not establish endorsement or acceptance. [Submission overview](https://info.arxiv.org/help/submit/index.html).

The [formalization notes](formalization-notes.md) record the conservative constants used throughout the new manuscript and the external mathematical and machine-complexity boundaries. The source project is newly authored; the missing original TeX of the earlier reference PDF is no longer a dependency of this submission package.
