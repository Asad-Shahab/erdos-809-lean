#!/bin/sh
# Run from this directory or any other working directory.
set -eu
cd "$(dirname "$0")"
if ! command -v pdflatex >/dev/null 2>&1; then
    echo "Missing pdflatex. Install a standard TeX Live, MacTeX, or MiKTeX distribution." >&2
    exit 1
fi
if command -v bibtex >/dev/null 2>&1; then
    BIBTEX=bibtex
elif command -v bibtex.original >/dev/null 2>&1; then
    BIBTEX=bibtex.original
else
    echo "Missing BibTeX (bibtex or bibtex.original)." >&2
    exit 1
fi
pdflatex -recorder -interaction=nonstopmode -halt-on-error main.tex
"$BIBTEX" main
pdflatex -recorder -interaction=nonstopmode -halt-on-error main.tex
pdflatex -recorder -interaction=nonstopmode -halt-on-error main.tex
cp main.pdf erdos809_manuscript.pdf
printf '\nBuilt %s/erdos809_manuscript.pdf\n' "$(pwd)"
