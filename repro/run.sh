#!/usr/bin/env bash
# =====================================================================================
# S7-A — MAS engine certification + Paley(43) premises.   [HEADLINE LINE, step 1]
#
# The §7 proof stands on two premises:
#   (i)  MAS(Paley43) = 543, so alpha* = 181/301 > 3/5 and the two top voters of any
#        5-realization are forced to level <= 1;
#   (ii) the engine that computes it is correct.
#
# This node establishes (ii) at full published scale — the Appendix A.4 MAS gauntlet,
# q = 19/23/31 against the known values 107/161/285, which check_all.sh does not run —
# and the >= 543 half of (i) independently, from the one committed input d0_reps.txt,
# with a verifier that shares no code with the package's engines.
#
# The <= 543 half needs the q=43 delta<=2 layer tables (~48 GB scratch) and is tracked
# on a separate node; it is not attempted here.
# =====================================================================================
source "$(dirname "$0")/env.sh"
cd "$REPRO_ROOT"

sysinfo
watchdog_start
trap watchdog_stop EXIT

banner "build"
cc -O3 -march=native -pthread -o "$SCRATCH/dp43" sec7_paley43/dp43.c
cc -O3 -march=native -pthread -o "$SCRATCH/verify_d0" repro/verify_d0.c
echo "built dp43, verify_d0"

# ---------------------------------------------------------------------------
banner "1. DP self-tests against brute force (q = 7, 11)"
# Each rebuilds canonicalization independently, checks fast==slow / idempotent /
# Aut-invariant, then verifies the DP order pool equals brute force at several tau.
for q in 7 11; do
  mkdir -p "$SCRATCH/st$q"
  "$SCRATCH/dp43" selftest $q "$SCRATCH/st$q" 2>&1 | tee "$SCRATCH/st$q.out"
done
s7=$(grep -c 'selftest q=7 PASSED'  "$SCRATCH/st7.out"  || true)
s11=$(grep -c 'selftest q=11 PASSED' "$SCRATCH/st11.out" || true)
claim "sec7.dp43-selftest-q7"  "pool == brute force, MAS(Paley7) = 14"  "$([ "$s7"  = 1 ] && echo 'PASSED' || echo 'not confirmed')" "$([ "$s7"  = 1 ] && echo aligned || echo divergent)"
claim "sec7.dp43-selftest-q11" "pool == brute force, MAS(Paley11) = 35" "$([ "$s11" = 1 ] && echo 'PASSED' || echo 'not confirmed')" "$([ "$s11" = 1 ] && echo aligned || echo divergent)"

# ---------------------------------------------------------------------------
banner "2. MAS gauntlet — certify the known values for q = 19, 23, 31"
# Appendix A.4: "the MAS gauntlet reproduces brute-force q=7,11 and the known
# MAS=107/161/285 for q=19/23/31". Runs the full layers->join->enum->close pipeline
# at tau = the published MAS; the join step certifies the maximum both ways.
declare -a GQ=(19 23 31) GMAS=(107 161 285)
gok=0
for i in 0 1 2; do
  q=${GQ[$i]}; want=${GMAS[$i]}
  d="$SCRATCH/g$q"; rm -rf "$d"; mkdir -p "$d"
  echo "--- q=$q  tau=$want ---"
  THREADS=$THREADS "$SCRATCH/dp43" all $q "$want" "$d" 2>&1 | tee "$SCRATCH/g$q.out"
  got=$(grep -o 'certified MAS = [0-9]*' "$SCRATCH/g$q.out" | tail -1 | awk '{print $NF}')
  got=${got:-none}
  metric "mas_q$q" "$got"
  claim "sec7.mas-gauntlet-q$q" "MAS(Paley$q) = $want" "MAS = $got" "$([ "$got" = "$want" ] && echo aligned || echo divergent)"
  [ "$got" = "$want" ] && gok=$((gok+1))
  du -sh "$d" | awk '{print "  layer tables on disk: " $1}'
  rm -rf "$d"
done
metric gauntlet_q_certified "$gok/3"

# ---------------------------------------------------------------------------
banner "3. Independent re-derivation of the level-0 facts from the committed seed"
"$SCRATCH/verify_d0" sec7_paley43/d0_reps.txt "$THREADS" 2>&1 | tee "$SCRATCH/vd0.out"
vd0=$(grep -c 'verify_d0: ALL CHECKS PASSED' "$SCRATCH/vd0.out" || true)

claim "sec7.paley43-structure"   "C = 903 arcs, T = 3311 cyclic triangles, out-deg 21, 11 tri/arc, |Aut| = 903" \
      "$([ "$vd0" = 1 ] && echo 'all structural constants match' || echo 'not confirmed')" \
      "$([ "$vd0" = 1 ] && echo aligned || echo divergent)"
claim "sec7.level0-census"       "19,651 orbits x 903 = 17,744,853 level-0 orders" \
      "$([ "$vd0" = 1 ] && echo '19,651 canonical reps, all stabiliser-free => 17,744,853' || echo 'not confirmed')" \
      "$([ "$vd0" = 1 ] && echo aligned || echo divergent)"
claim "sec7.mas-lower-bound"     "MAS(Paley43) = 543; alpha* = 181/301 > 3/5; slack 6; top-two level <= 1" \
      "$([ "$vd0" = 1 ] && echo 'MAS >= 543 confirmed independently (<= 543 needs the q=43 layer tables)' || echo 'not confirmed')" \
      "$([ "$vd0" = 1 ] && echo partial || echo divergent)"

banner "verdict"
ok=$(( s7 + s11 + gok + vd0 ))
echo "self-tests $((s7+s11))/2 | gauntlet $gok/3 | verify_d0 $vd0/1  => $ok/6"
[ "$ok" -eq 6 ] || { echo "S7-A: $((6-ok)) premise check(s) did not reproduce" >&2; exit 1; }
echo "S7-A OK: engine certified on q=7,11,19,23,31 and the level-0 premises re-derived independently"
