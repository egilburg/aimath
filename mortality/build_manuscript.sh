#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
stem=exponential_mortality_bound_for_finite_real_matrix_monoids
pdflatex -interaction=nonstopmode -halt-on-error "$stem.tex"
bibtex "$stem"
pdflatex -interaction=nonstopmode -halt-on-error "$stem.tex"
pdflatex -interaction=nonstopmode -halt-on-error "$stem.tex"
