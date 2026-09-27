# Paper

LaTeX source of *The Burr–Erdős–Graham–Sós conjecture for the seven-cycle*
by Asad Shahab. The compiled PDF is
[`erdos809_manuscript.pdf`](erdos809_manuscript.pdf).

The paper proves f(n, ⌊n²/4⌋ + 1, C₇) = (1/8 + o(1)) n². Together with the
theorem of Bucić, Chen, and Ma for k ≥ 4, this settles the conjecture for
every fixed odd cycle C₂ₖ₊₁ with k ≥ 3. Section 10 describes the Lean
formalization and the certificate verifier in this repository.

## Build

With a standard TeX Live, MacTeX, or MiKTeX installation:

```sh
sh build.sh
```

This runs pdfLaTeX, BibTeX, and pdfLaTeX twice, and writes `main.pdf` and
`erdos809_manuscript.pdf`. `main.tex` is the root file; the sections are in
`sections/`. Edit citations in `references.bib`; `main.bbl` is generated
by BibTeX and is included for convenience.
