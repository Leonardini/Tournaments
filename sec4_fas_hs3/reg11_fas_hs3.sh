#!/usr/bin/env bash
# FAS versus HS3 on all regular tournaments on 11 vertices, split by 3-inducibility
# (the sentence after Counterexample 4.2). Reads the committed catalogue
# ../data/regulartournaments11.RData; downloads nothing.
#
#   1. reg11_catalogue.R  checks the catalogue (regular, pairwise non-isomorphic), finds T*
#                         in it, and writes it as McKay bit strings;
#   2. margin1_scan.c     decides 3-inducibility of every entry;
#   3. hs3fas.c           computes FAS and HS3 of every entry;
#   4. reg11_fas_hs3.py   recomputes all three independently and checks the paper's counts.
#
# Needs a C compiler, R with igraph, and Python 3 with ortools. Uses at most 4 cores
# (WORKERS=1..4, default 4) and well under 1 GB; about 30 s on 4 cores of a laptop.
# Usage (from anywhere): ./reg11_fas_hs3.sh
set -euo pipefail
cd "$(dirname "$0")"
WORKERS=${WORKERS:-4}
WORK=$(mktemp -d "${TMPDIR:-/tmp}/reg11_fas_hs3.XXXXXX")
trap 'rm -rf "$WORK"' EXIT

cc -O3 -o "$WORK/margin1_scan" ../appendices/margin1_scan.c
cc -O3 -o "$WORK/hs3fas" hs3fas.c

Rscript reg11_catalogue.R "$WORK/reg11.txt" | tee "$WORK/catalogue.out"
TSTAR=$(sed -n 's/^T\* = catalogue entry \([0-9][0-9]*\) *$/\1/p' "$WORK/catalogue.out")
[ -n "$TSTAR" ] || { echo "reg11_catalogue.R did not report T*" >&2; exit 1; }

"$WORK/margin1_scan" 11 emitn < "$WORK/reg11.txt" > "$WORK/margin1_scan.out"
PROGRESS=0 "$WORK/hs3fas" "$WORK/reg11.txt" 11 > "$WORK/hs3fas.out"
cat "$WORK/hs3fas.out"

python3 reg11_fas_hs3.py "$WORK/reg11.txt" "$WORK/margin1_scan.out" "$WORK/hs3fas.out" "$TSTAR" "$WORKERS"
