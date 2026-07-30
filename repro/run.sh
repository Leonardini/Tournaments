#!/usr/bin/env bash
# =====================================================================================
# S7-B — the exhaustive level-0 razor screen.               [HEADLINE LINE, step 2]
#
# S7-A established the premises: MAS(Paley43) >= 543, so alpha* = 181/301 > 3/5, the
# realization slack 5*MAS - 3C is 6, and the two highest-agreement voters of any
# 5-realization are forced to level <= 1. The co-backing lemma (a 3-line counting
# argument, no computation) then says the five voters' double-back sets are pairwise
# disjoint. So a 5-realization requires TWO level-<=1 orders with DISJOINT double-back
# sets, and the whole result reduces to showing no such pair exists.
#
# This node runs that screen on the COMPLETE level-0 shell — all 17,744,853 maximum-
# acyclic orders, expanded by razor_screen from the 19,651 committed orbit reps
# (expand=1). It is the Appendix A.4 ledger entry "Level-0 proved exhaustively", and
# needs no layer tables, so it fits this machine.
#
# Two devices make an exhaustive check over ~1.6e14 order pairs finish in seconds; both
# are proved sound in PALEY43_NONREALIZABLE.md §6 and neither can create a false
# negative:
#   razor (§6.1)  rmask(O) = DB(O) restricted to triangles inside W = {0..23}, which
#                 depends only on O|_W. Overlapping rmasks => overlapping DBs, so only
#                 razor-disjoint pairs can be DB-disjoint. The shell collapses to a few
#                 million distinct rmasks.
#   Aut (§6.2)    |DB(sigma O1) ∩ DB(sigma O2)| is G-invariant, so it suffices to test
#                 orbit representatives against the full pool — a factor 903 on one side.
#
# Expected (Appendix A.4): TRUE_DISJOINT = 0, min_overlap = 68 over razor-disjoint
# candidates, 333,809 candidate (rep, pool) pairs, |R| = 538.
#
# SCOPE: level 0 is a sub-shell of the level-<=1 shell the full proof needs. This node
# settles the obstruction on the MAS layer; the level-1 layer is ~93x larger and needs
# the q=43 layer tables. Reported as such — not as the complete proof.
# =====================================================================================
source "$(dirname "$0")/env.sh"
cd "$REPRO_ROOT"

sysinfo
watchdog_start
trap watchdog_stop EXIT

banner "build"
cc -O3 -march=native -pthread -o "$SCRATCH/razor_screen" sec7_paley43/razor_screen.c
echo "built razor_screen"

banner "exhaustive screen over the complete level-0 shell"
echo "input: sec7_paley43/d0_reps.txt (19,651 delta=0 orbit reps, expand=1 => 17,744,853 orders)"
t0=$SECONDS
cd sec7_paley43
MCAP=300000 "$SCRATCH/razor_screen" d0_reps.txt 1 24 0 "$THREADS" 2>&1 | tee "$SCRATCH/d0.out"
el=$((SECONDS - t0))
cd "$REPRO_ROOT"

res=$(grep '^RESULT ' "$SCRATCH/d0.out" | tail -1)
echo; echo "RESULT line: $res"
f() { sed -n "s/.*[ ]$1=\([0-9-]*\).*/\1/p" <<<"$res"; }
M=$(f M); pool=$(f pool); cand=$(f rmask_cand_pairs); dang=$(f dangerous)
K=$(f K); checked=$(f pairs_checked); td=$(f TRUE_DISJOINT); mo=$(f min_overlap)
nR=$(sed -n 's/.*|R|=\([0-9]*\).*/\1/p' "$SCRATCH/d0.out" | tail -1)

metric wall_seconds "$el"
metric razor_triangles "$nR"
metric distinct_rmasks "$M"
metric pool_orders "$pool"
metric candidate_rmask_pairs "$cand"
metric dangerous_rmasks "$dang"
metric dangerous_pool_orders "$K"
metric pairs_checked "$checked"
metric true_disjoint "$td"
metric min_overlap "$mo"

# total order-pairs the razor rules out without inspecting them
awk -v p="${pool:-0}" 'BEGIN{ if(p>0) printf "METRIC\ttotal_order_pairs_in_shell\t%.3e\n", p*(p-1)/2 }'

eq() { [ "$1" = "$2" ] && echo aligned || echo divergent; }
banner "claims"
claim "sec7.razor-size"            "|R| = 538 razor triangles for W = {0..23}" "|R| = $nR" "$(eq "$nR" 538)"
claim "sec7.level0-pool"           "17744853 level-0 orders screened"          "$pool"     "$(eq "$pool" 17744853)"
claim "sec7.level0-pairs-checked"  "333809 razor-disjoint candidate pairs"     "$checked"  "$(eq "$checked" 333809)"
claim "sec7.level0-true-disjoint"  "TRUE_DISJOINT = 0"                        "TRUE_DISJOINT = $td" "$(eq "$td" 0)"
claim "sec7.level0-min-overlap"    "min overlap = 68"                         "min overlap = $mo"   "$(eq "$mo" 68)"

banner "what this establishes"
if [ "$td" = 0 ]; then
  awk -v p="${pool:-0}" -v c="${checked:-0}" 'BEGIN{
    printf "  no two of the %d maximum-acyclic orders of Paley(43) have disjoint\n", p;
    printf "  double-back sets: all %.3e order pairs are settled, %d of them by the\n", p*(p-1)/2, c;
    printf "  exact full-DB check and the rest by the razor (they share a razor triangle).\n" }'
  echo "  => the co-backing pair obstruction holds on the MAS layer."
  echo "  => a 5-realization of Paley(43) cannot have both top voters at level 0."
  echo "  NOT YET the full result: level 1 (1,821,652 further orbits) is untested here."
else
  echo "  $td disjoint pair(s) found — see razor_disjoint_hits.txt"
fi

banner "verdict"
ok=1
for pair in "$nR 538" "$pool 17744853" "$checked 333809" "$td 0" "$mo 68"; do
  set -- $pair; [ "$1" = "$2" ] || ok=0
done
echo "screen finished in ${el}s"
[ "$ok" = 1 ] || { echo "S7-B: the level-0 screen did not reproduce the published counts" >&2; exit 1; }
echo "S7-B OK: exhaustive level-0 screen reproduces TRUE_DISJOINT=0 and min_overlap=68 exactly"
