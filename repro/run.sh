#!/usr/bin/env bash
# =====================================================================================
# S6-D — triple-local CSP engine at n = 9 (full census).
#
# The N(5) >= 12 result is a solver-free C pipeline, not an ILP sweep. Its three stages
# are validated here over a COMPLETE catalogue (all 191,536 tournaments on n = 9) before
# the n = 11 census is attempted:
#
#   margin1_scan  decides margin-1 3-inducibility (3 labels) and full 3-inducibility
#                 (4 labels) as a per-vertex-triple arc labelling
#   cert_m1k5     margin-1 five-voter CSP over the 10 dissent pairs; SAT => 5-inducible
#                 with every arc backed exactly 3:2, emitting the arc labelling
#   verify_m1k5   independent verifier: rebuilds the five voters from each witness,
#                 checks every backward set is acyclic and re-counts every arc at 3:2
#
# Paper's n = 9 reference tally (sec6_bounds/README.md "What to expect"):
#   total 191,536 / margin-1 SAT 173,608 / realizable-not-margin-1 254 / non-3-real 17,674
#   and every non-3-inducible tournament margin-1 5-inducible, all witnesses verified.
# =====================================================================================
source "$(dirname "$0")/env.sh"
cd "$REPRO_ROOT"

sysinfo
[ -x "$GENTOURNG" ] || { echo "gentourng not found at $GENTOURNG" >&2; exit 1; }
watchdog_start
trap watchdog_stop EXIT

banner "build"
cc -O3 -o "$SCRATCH/margin1_scan" sec6_bounds/triple_local_csp/margin1_scan.c
cc -O3 -o "$SCRATCH/cert_m1k5"    sec6_bounds/triple_local_csp/cert_m1k5.c
cc -O3 -o "$SCRATCH/verify_m1k5"  sec6_bounds/triple_local_csp/verify_m1k5.c
echo "built margin1_scan, cert_m1k5, verify_m1k5"

# ---------------------------------------------------------------------------
banner "1. 3-inducibility scan over the complete n = 9 catalogue"
t0=$SECONDS
"$GENTOURNG" -q 9 | "$SCRATCH/margin1_scan" 9 > /dev/null 2> "$SCRATCH/scan.err"
scan_s=$((SECONDS - t0))
tail -1 "$SCRATCH/scan.err"
line=$(grep '^n=9:' "$SCRATCH/scan.err" | tail -1)
tot=$(sed -n 's/.*total \([0-9]*\).*/\1/p'                       <<<"$line")
msat=$(sed -n 's/.*margin1-SAT \([0-9]*\).*/\1/p'                <<<"$line")
rnm=$(sed -n 's/.*REALIZABLE-NOT-MARGIN1 \([0-9]*\).*/\1/p'      <<<"$line")
nre=$(sed -n 's/.*non-realizable \([0-9]*\).*/\1/p'              <<<"$line")

metric scan_wall_seconds "$scan_s"
metric scan_us_per_tournament "$(awk -v s="$scan_s" -v n="${tot:-1}" 'BEGIN{printf "%.1f", s*1e6/n}')"
metric n9_total "$tot"; metric n9_margin1_sat "$msat"
metric n9_real_not_margin1 "$rnm"; metric n9_non_3_real "$nre"

eq() { [ "$1" = "$2" ] && echo aligned || echo divergent; }
claim "sec6.n9-catalogue-size"      "191536" "$tot"  "$(eq "$tot"  191536)"
claim "sec6.n9-margin1-3-inducible" "173608" "$msat" "$(eq "$msat" 173608)"
claim "sec6.n9-3-inducible-not-m1"  "254"    "$rnm"  "$(eq "$rnm"  254)"
claim "sec6.n9-not-3-inducible"     "17674"  "$nre"  "$(eq "$nre"  17674)"

# ---------------------------------------------------------------------------
banner "2. full margin-1 five-voter pipeline (the census wiring, one process)"
# Every non-3-inducible n = 9 tournament must admit a margin-1 five-voter profile,
# and every witness must survive the independent verifier.
t0=$SECONDS
"$GENTOURNG" -q 9 \
  | "$SCRATCH/margin1_scan" 9 emitn 2> "$SCRATCH/scan2.err" \
  | grep '^N ' | cut -d' ' -f2 \
  | "$SCRATCH/cert_m1k5" 9 2> "$SCRATCH/cert.err" \
  | "$SCRATCH/verify_m1k5" 9 2> "$SCRATCH/verify.err" > /dev/null
pipe_s=$((SECONDS - t0))
tail -1 "$SCRATCH/cert.err"; tail -1 "$SCRATCH/verify.err"

cl=$(grep '^total ' "$SCRATCH/cert.err" | tail -1)
c_tot=$(sed -n 's/^total \([0-9]*\):.*/\1/p'                  <<<"$cl")
c_sat=$(sed -n 's/.*margin1-k5-SAT \([0-9]*\).*/\1/p'         <<<"$cl")
c_uns=$(sed -n 's/.*UNSAT \([0-9]*\).*/\1/p'                  <<<"$cl")
vl=$(grep '^verified ' "$SCRATCH/verify.err" | tail -1)
v_ok=$(sed -n 's/^verified \([0-9]*\).*/\1/p'                 <<<"$vl")
v_fail=$(grep -c 'VERIFY FAIL' "$SCRATCH/verify.err" || true)

metric pipeline_wall_seconds "$pipe_s"
metric cert_instances "$c_tot"; metric cert_m1k5_sat "$c_sat"; metric cert_unsat "$c_uns"
metric witnesses_verified "$v_ok"; metric verify_failures "$v_fail"

claim "sec6.n9-all-non3real-are-m1-5-inducible" "17674 of 17674 margin-1 5-inducible, 0 UNSAT" \
      "$c_sat of $c_tot SAT, $c_uns UNSAT" \
      "$([ "$c_sat" = 17674 ] && [ "$c_uns" = 0 ] && echo aligned || echo divergent)"
claim "sec6.n9-witnesses-independently-verified" "all witnesses: 5 acyclic voters, every arc exactly 3:2" \
      "$v_ok verified, $v_fail failures" \
      "$([ "$v_ok" = 17674 ] && [ "$v_fail" = 0 ] && echo aligned || echo divergent)"

# ---------------------------------------------------------------------------
banner "3. projection to n = 11"
# D_11 = 903,753,248 tournaments. Project the census cost from the measured rate.
us=$(awk -v s="$scan_s" -v n="${tot:-1}" 'BEGIN{printf "%.2f", s*1e6/n}')
awk -v us="$us" 'BEGIN{
  d11=903753248; core_h=d11*us/1e6/3600;
  printf "  measured scan rate      %.2f us/tournament (paper: ~20-34 us)\n", us;
  printf "  D_11                    903,753,248\n";
  printf "  projected scan cost     %.1f core-hours  => %.1f h wall on 8 cores\n", core_h, core_h/8;
  printf "METRIC\tn11_projected_core_hours\t%.1f\n", core_h;
  printf "METRIC\tn11_projected_wall_hours_8core\t%.1f\n", core_h/8; }'

banner "verdict"
allok=1
for pair in "$tot 191536" "$msat 173608" "$rnm 254" "$nre 17674" "$c_sat 17674" "$c_uns 0" "$v_ok 17674" "$v_fail 0"; do
  set -- $pair; [ "$1" = "$2" ] || allok=0
done
echo "scan ${scan_s}s | pipeline ${pipe_s}s"
[ "$allok" = 1 ] || { echo "S6-D: the n=9 tally did not reproduce" >&2; exit 1; }
echo "S6-D OK: full n=9 census matches the paper's reference tally exactly; engine validated for n=11"
