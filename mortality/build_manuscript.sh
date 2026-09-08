#!/bin/sh
set -eu
cd "$(dirname "$0")"
mkdir -p recheck/tex
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=recheck/tex exponential_mortality_bound_for_finite_real_matrix_monoids.tex
printf '%s\n' 'Rendered PDF is in recheck/tex; retained release PDF is unchanged.'
