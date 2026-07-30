#!/usr/bin/env bash
# =====================================================================================
# S6-D1 — the n = 11 census: every 11-vertex tournament is 5-inducible, so N(5) >= 12.
#
# The paper's lower bound on N(5), at full published scale: all D_11 = 903,753,248
# tournaments on 11 vertices, decided solver-free. S6-D validated the same three C tools
# over the complete n = 9 catalogue, matching the paper's tally on every line.
#
# Pipeline per slice (the shipped n11_worker.sh, streamed end to end, nothing buffered):
#   gentourng 11 RES/MOD -> margin1_scan (3-inducibility triple-local CSP)
#     -> the non-3-inducible lines -> cert_m1k5 (margin-1 five-voter CSP, emits a witness)
#     -> verify_m1k5 (independent witness check) -> anything still UNSAT lands in .residual
# A tournament reaching .residual would need the 5-inducibility ILP; the paper reports 0.
#
# n11_aggregate.sh then enforces the guards that make this a proof rather than a tally:
# every slice present, each slice's three stage tallies mutually consistent, and the
# completeness identity sum of slice totals == D_11 exactly.
#
# COMPUTE NOTE. The documented local run used xargs -P 8. Each slice is a 4-process
# pipeline whose stages run concurrently, so -P 8 draws more than 8 cores; this machine
# is held to at most 10, so N_WORKERS defaults to 7 here. Same computation, same slice
# count, only the wall clock differs.
# =====================================================================================
source "$(dirname "$0")/env.sh"
cd "$REPRO_ROOT"

SLICES="${SLICES:-256}"
N_WORKERS="${N_WORKERS:-7}"

sysinfo
[ -x "$GENTOURNG" ] || { echo "gentourng not found at $GENTOURNG" >&2; exit 1; }
watchdog_start
trap 'watchdog_stop; kill 0 2>/dev/null || true' EXIT

banner "build"
BIN="$SCRATCH/n11bin"; RES="$SCRATCH/n11_results"
mkdir -p "$BIN" "$RES"
cc -O3 -o "$BIN/margin1_scan" sec6_bounds/triple_local_csp/margin1_scan.c
cc -O3 -o "$BIN/cert_m1k5"    sec6_bounds/triple_local_csp/cert_m1k5.c
cc -O3 -o "$BIN/verify_m1k5"  sec6_bounds/triple_local_csp/verify_m1k5.c
echo "built margin1_scan, cert_m1k5, verify_m1k5 into $BIN"
echo "slices=$SLICES  parallel workers=$N_WORKERS  results=$RES"

# ---------------------------------------------------------------------------
banner "census — $SLICES gentourng res/mod slices on $N_WORKERS workers"
# progress reporter: count .done markers every 120 s and extrapolate
( start=$SECONDS
  while :; do
    sleep 120
    d=$(ls "$RES"/w_*.done 2>/dev/null | wc -l | tr -d ' ')
    el=$((SECONDS - start))
    awk -v d="$d" -v s="$SLICES" -v el="$el" 'BEGIN{
      pct = s>0 ? 100*d/s : 0;
      eta = d>0 ? el*(s-d)/d : 0;
      printf "PROGRESS  %d/%d slices done (%.1f%%)  elapsed %dm  eta %dm\n", d, s, pct, el/60, eta/60 }'
  done ) &
PROG_PID=$!

t0=$SECONDS
seq 0 $((SLICES - 1)) | xargs -P "$N_WORKERS" -I{} \
  bash sec6_bounds/n11_census/n11_worker.sh {} "$SLICES" "$RES" "$BIN" "$GENTOURNG"
census_s=$((SECONDS - t0))
kill "$PROG_PID" 2>/dev/null || true
echo "census finished in $((census_s / 60))m $((census_s % 60))s"
metric census_wall_seconds "$census_s"
metric census_core_hours "$(awk -v s="$census_s" -v w="$N_WORKERS" 'BEGIN{printf "%.1f", s*w/3600}')"

# ---------------------------------------------------------------------------
banner "aggregate — completeness + per-slice consistency guards"
set +e
bash sec6_bounds/n11_census/n11_aggregate.sh "$RES" "$SLICES" 2>&1 | tee "$SCRATCH/agg.out"
agg_rc=${PIPESTATUS[0]}
set -e

g() { sed -n "s/^ *$1: *//p" "$SCRATCH/agg.out" | tail -1 | tr -d ' ,' ; }
tot=$(g 'total tournaments')
m1=$(g 'margin-1 3-inducible')
r3=$(g '3-inducible, not margin-1')
n3=$(g 'not 3-inducible')
sat=$(sed -n 's/.*margin-1 5-inducible: *\([0-9,]*\).*/\1/p' "$SCRATCH/agg.out" | tail -1 | tr -d ' ,')
ver=$(sed -n 's/.*all witnesses verified: *\([0-9,]*\).*/\1/p' "$SCRATCH/agg.out" | tail -1 | tr -d ' ,')
res=$(sed -n 's/.*residual (need ILP): *\([0-9,]*\).*/\1/p' "$SCRATCH/agg.out" | tail -1 | tr -d ' ,')
comp=$(grep -c 'COMPLETENESS CHECK PASSED' "$SCRATCH/agg.out" || true)
proven=$(grep -c 'N(5) >= 12  \[PROVEN' "$SCRATCH/agg.out" || true)

metric n11_total "$tot"; metric n11_margin1_3ind "$m1"
metric n11_3ind_not_m1 "$r3"; metric n11_not_3ind "$n3"
metric n11_m1_5inducible "$sat"; metric n11_witnesses_verified "$ver"
metric n11_residual "$res"

eq() { [ "$1" = "$2" ] && echo aligned || echo divergent; }
banner "claims"
claim "sec6.n11-completeness"      "903753248 (= D_11)" "$tot" "$(eq "$tot" 903753248)"
claim "sec6.n11-margin1-3ind"      "362587120"          "$m1"  "$(eq "$m1"  362587120)"
claim "sec6.n11-3ind-not-margin1"  "20038128"           "$r3"  "$(eq "$r3"  20038128)"
claim "sec6.n11-not-3ind"          "521128000"          "$n3"  "$(eq "$n3"  521128000)"
claim "sec6.n11-m1-5inducible"     "521128000"          "$sat" "$(eq "$sat" 521128000)"
claim "sec6.n11-residual-zero"     "0 (ILP never invoked)" "$res" "$(eq "$res" 0)"
claim "sec6.N5-lower-bound"        "every 11-vertex tournament is 5-inducible => N(5) >= 12" \
      "$([ "$proven" = 1 ] && echo 'PROVEN, no ILP needed' || echo 'not confirmed')" \
      "$(eq "$proven" 1)"

banner "verdict"
ok=1
[ "$agg_rc" = 0 ] || ok=0
[ "$comp" = 1 ] || ok=0
for pair in "$tot 903753248" "$m1 362587120" "$r3 20038128" "$n3 521128000" "$sat 521128000" "$res 0" "$proven 1"; do
  set -- $pair; [ "$1" = "$2" ] || ok=0
done
echo "census $((census_s / 60))m on $N_WORKERS workers | aggregate rc=$agg_rc"
rm -rf "$RES" "$BIN"
[ "$ok" = 1 ] || { echo "S6-D1: the n=11 census did not reproduce the published aggregate" >&2; exit 1; }
echo "S6-D1 OK: all 903,753,248 tournaments on n=11 are 5-inducible => N(5) >= 12, reproduced at full scale"
