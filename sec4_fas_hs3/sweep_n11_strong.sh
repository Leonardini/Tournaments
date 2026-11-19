#!/usr/bin/env bash
# FAS versus HS3 on every strong tournament on 11 vertices (a long run: 1,000 slices; our run took
# 2 h 05 min with WORKERS=5 on an Apple M-series laptop, about 10 core-hours).
# A tournament that is not strong has FAS and HS3 equal to the sums over its strong
# components, which have at most 10 vertices, where FAS = HS3 (Theorem 4.1), so only the
# strong ones can violate. nauty's gentourng -c 11 r/1000 generates slice r of the strong
# tournaments; hs3fas.c checks each. Resumable: a slice whose log is complete is skipped.
# Output: n11_sweep.log, ending in a TOTAL line, and n11_violators_found.txt, the bit strings
# of the violators, which must equal n11_violators.txt (checked at the end).
# Usage: GENTOURNG=/path/to/gentourng ./sweep_n11_strong.sh
set -euo pipefail
cd "$(dirname "$0")"
: "${GENTOURNG:?set GENTOURNG to the gentourng program of nauty}"
cc -O3 -o hs3fas hs3fas.c
# WORKERS=k runs k slices at a time (default 1); each slice writes n11_slices/<r>.log, and a slice
# counts as done only once its log ends with hs3fas's summary line.
mkdir -p n11_slices
export GENTOURNG
one_slice() {
  r=$1; f=n11_slices/$r.log
  grep -q 'tournaments;' "$f" 2>/dev/null && return 0
  "$GENTOURNG" -q -c 11 "$r/1000" | PROGRESS=0 ./hs3fas /dev/stdin 11 | sed "s/^/[slice $r] /" > "$f.tmp"
  mv "$f.tmp" "$f"
  echo "$(date +%H:%M:%S) slice $r done ($(ls n11_slices/*.log | wc -l | tr -d ' ')/1000)" >&2
}
export -f one_slice
seq 0 999 | xargs -P "${WORKERS:-1}" -I{} bash -c 'one_slice {}'
for r in $(seq 0 999); do
  grep -q 'tournaments;' "n11_slices/$r.log" || { echo "slice $r incomplete" >&2; exit 1; }
done
for r in $(seq 0 999); do cat "n11_slices/$r.log"; done > n11_sweep.log
awk '/tournaments;/{t+=$4; m+=$6; h+=$9} END{print "n=11 strong TOTAL:", t, "tournaments;", m, "HS3<FAS;", h, "HARD"}' n11_sweep.log | tee -a n11_sweep.log
sed -n 's/.*MISMATCH idx [0-9]*: .*bits=\([01]*\)$/\1/p' n11_sweep.log | sort > n11_violators_found.txt
if sort n11_violators.txt | cmp -s - n11_violators_found.txt; then echo "violators match n11_violators.txt"
else echo "MISMATCH: the sweep's violators differ from n11_violators.txt"; exit 1; fi
