#!/bin/sh
set -eu
cd "$(dirname "$0")"
mkdir -p recheck/tex
latexmk -pdf -interaction=nonstopmode -halt-on-error -outdir=recheck/tex sharp_finite_markov_order_in_intrinsic_sofic_dimension.tex
printf '%s\n' 'Rendered PDF is in recheck/tex; retained release PDF is unchanged.'
