#!/usr/bin/env bash
# =====================================================================================
# S5-E — cA3: the k = 3 threshold is necessary but not sufficient.
#
# Conjecture A(k) predicted that a tournament is k-inducible exactly when its
# predictability alpha* reaches (k+1)/(2k). At k = 3 that threshold is 2/3. cA3 (the
# code's ce1068) is the Z_11 circulant with connection set {1,2,3,4,6}: it sits EXACTLY
# on the threshold, alpha* = 2/3, and yet is not 3-inducible — it needs five voters.
#
# This is the same shape of result as the paper's headline at k = 5, where Paley(43) has
# alpha* = 181/301 > 3/5 and still is not 5-inducible. cA3 is the small, fully certifiable
# instance of the phenomenon, so it is reproduced here by every independent engine the
# package ships:
#
#   alpha*             exact rational LP (rcdd + GMP), plus the structure analysis
#   not 3-inducible    (a) OR-Tools CP-SAT position-variable encoding
#                      (b) IBM CPLEX majority ILP
#                      (c) solver-free: enumerate all 11! = 39,916,800 backward masks and
#                          search for a 3-order partition of the 55 arcs
#   5-inducible        explicit 5-voter realization, verified arc by arc
#   vertex-critical    the n = 10 vertex deletion IS 3-inducible
#   minimal certificate  CPLEX min-cardinality (6 orders) + free orbit-minimality argument
# =====================================================================================
source "$(dirname "$0")/env.sh"
cd "$REPRO_ROOT/sec5_a3_boundary"

sysinfo
watchdog_start
trap watchdog_stop EXIT

hit() { grep -qF -- "$2" "$1" && echo 1 || echo 0; }
vd() { [ "$1" = 1 ] && echo aligned || echo divergent; }

# ---------------------------------------------------------------------------
banner "1. exact rational alpha* = 2/3 and the structure of cA3"
Rscript verify_ce1068.R  2>&1 | tee "$SCRATCH/verify.out"
Rscript analyze_ce1068.R 2>&1 | tee "$SCRATCH/analyze.out"

a_exact=$(hit "$SCRATCH/verify.out" 'alpha* == 2/3 exactly ? TRUE')
a_recheck=$(hit "$SCRATCH/verify.out" 'certificate re-check')
circ=$(hit "$SCRATCH/analyze.out" 'has an 11-cycle automorphism (=> circulant): TRUE')
dreg=$(hit "$SCRATCH/analyze.out" 'doubly-regular (all==3): TRUE')
cset=$(grep -o '{ *1, *2, *3, *4, *6 *}' "$SCRATCH/analyze.out" | head -1)
metric alpha_star_exact_2_3 "$a_exact"
claim "sec5.cA3-alpha-star-exact" "alpha* = 2/3 exactly (exact rational LP)" \
      "$([ "$a_exact" = 1 ] && echo 'alpha* == 2/3 exactly ? TRUE' || echo 'not confirmed')" "$(vd "$a_exact")"
claim "sec5.cA3-circulant" "Z_11 circulant, connection set {1,2,3,4,6}, doubly regular" \
      "circulant=$([ "$circ" = 1 ] && echo TRUE || echo no), S=${cset:-not found}, doubly-regular=$([ "$dreg" = 1 ] && echo TRUE || echo no)" \
      "$(vd "$([ "$circ" = 1 ] && [ "$dreg" = 1 ] && [ -n "$cset" ] && echo 1 || echo 0)")"

# ---------------------------------------------------------------------------
banner "2. not 3-inducible — engine (a): OR-Tools CP-SAT"
python3 independent_realize3_cpsat.py 2>&1 | tee "$SCRATCH/cpsat.out"
e_k3=$(hit "$SCRATCH/cpsat.out" 'k=3 (maj>=2): INFEASIBLE (proven)')
e_k5=$(hit "$SCRATCH/cpsat.out" 'k=5 (maj>=3): FEASIBLE')

banner "3. not 3-inducible — engine (b): solver-free 11! partition search"
cc -O3 -o "$SCRATCH/realize3_partition" realize3_partition.c
t0=$SECONDS
"$SCRATCH/realize3_partition" 2>&1 | tee "$SCRATCH/partition.out"
part_s=$((SECONDS - t0))
e_part=$(hit "$SCRATCH/partition.out" 'NO PARTITION EXISTS')
metric partition_seconds "$part_s"

banner "4. not 3-inducible — engine (c): IBM CPLEX majority ILP"
set +e
python3 reg11_realize3.py ce1068_inmask.txt "$SCRATCH/ce1068_realize3.csv" 2>&1 | tee "$SCRATCH/cplex.out"
cplex_rc=$?
set -e
e_cplex=$(hit "$SCRATCH/cplex.out" 'NOTREAL=1')
[ "$cplex_rc" = 0 ] || echo "  (CPLEX engine exited $cplex_rc — recorded as unavailable, the two free engines stand alone)"

engines=$((e_k3 + e_part + e_cplex))
metric engines_agreeing_not_3_inducible "$engines/3"
claim "sec5.cA3-not-3-inducible-3-engines" "not 3-inducible, unanimous across CP-SAT / CPLEX ILP / solver-free" \
      "CP-SAT=$([ "$e_k3" = 1 ] && echo INFEASIBLE || echo n/a), solver-free=$([ "$e_part" = 1 ] && echo 'NO PARTITION' || echo n/a), CPLEX=$([ "$e_cplex" = 1 ] && echo NOTREAL || echo unavailable) => $engines/3" \
      "$(vd "$([ "$engines" = 3 ] && echo 1 || echo 0)")"

# ---------------------------------------------------------------------------
banner "5. cA3 IS 5-inducible, and is vertex-critical"
python3 realize_and_delete_ce1068.py 2>&1 | tee "$SCRATCH/rd.out"
r5=$(hit "$SCRATCH/rd.out" '5-realizable = True')
rver=$(hit "$SCRATCH/rd.out" 'arcs with < 3 voters agreeing = 0')
rdel=$(hit "$SCRATCH/rd.out" '3-realizable = True')
rcrit=$(hit "$SCRATCH/rd.out" 'VERTEX-CRITICAL')
claim "sec5.cA3-5-inducible" "5-inducible: explicit 5-voter realization, McG(cA3) = 5" \
      "5-realizable=$([ "$r5" = 1 ] && echo True || echo no), arcs with <3 agreeing = $([ "$rver" = 1 ] && echo 0 || echo '>0')" \
      "$(vd "$([ "$r5" = 1 ] && [ "$rver" = 1 ] && echo 1 || echo 0)")"
claim "sec5.cA3-vertex-critical" "every 1-vertex deletion is 3-inducible => vertex-critical" \
      "$([ "$rdel" = 1 ] && [ "$rcrit" = 1 ] && echo 'deletion 3-realizable = True, VERTEX-CRITICAL' || echo 'not confirmed')" \
      "$(vd "$([ "$rdel" = 1 ] && [ "$rcrit" = 1 ] && echo 1 || echo 0)")"

# ---------------------------------------------------------------------------
banner "6. the minimum 2/3-certificate"
set +e
python3 cert_primal_1068.py 2>&1 | tee "$SCRATCH/certp.out"; cp_rc=$?
set -e
c6=$(grep -o 'min-cardinality = [0-9]* orders' "$SCRATCH/certp.out" | tail -1 | awk '{print $3}')
ctight=$(hit "$SCRATCH/certp.out" 'tight edges: 55/55')
metric min_certificate_orders "${c6:-none}"
claim "sec5.cA3-min-certificate" "minimum primal 2/3-certificate = 6 orders; 55/55 arcs tight at 2/3" \
      "min-cardinality = ${c6:-unavailable} orders, tight edges $([ "$ctight" = 1 ] && echo 55/55 || echo 'not confirmed')" \
      "$(vd "$([ "${c6:-0}" = 6 ] && [ "$ctight" = 1 ] && echo 1 || echo 0)")"

python3 cert_orbits_1068.py 2>&1 | tee "$SCRATCH/certo.out"
orb=$(hit "$SCRATCH/certo.out" 'arc-orbits under C_11: 5 classes, sizes [11, 11, 11, 11, 11]')
k1=$(hit "$SCRATCH/certo.out" 'k=1 feasible in pool? False')
claim "sec5.cA3-orbit-structure" "5 arc-orbits under C_11 of sizes [11,11,11,11,11]; no 1-orbit certificate" \
      "$([ "$orb" = 1 ] && [ "$k1" = 1 ] && echo 'both confirmed' || echo 'not confirmed')" \
      "$(vd "$([ "$orb" = 1 ] && [ "$k1" = 1 ] && echo 1 || echo 0)")"

rm -f ce1068_inmask.txt ce1068_analysis.rds

banner "verdict"
ok=1
for v in "$a_exact" "$circ" "$dreg" "$e_k3" "$e_k5" "$e_part" "$r5" "$rver" "$rdel" "$rcrit" "$orb" "$k1"; do
  [ "$v" = 1 ] || ok=0
done
echo "engines agreeing not-3-inducible: $engines/3 | solver-free 11! search: ${part_s}s"
[ "$ok" = 1 ] || { echo "S5-E: part of the cA3 battery did not reproduce" >&2; exit 1; }
echo "S5-E OK: cA3 sits on alpha* = 2/3 exactly and is not 3-inducible ($engines/3 independent engines), but is 5-inducible and vertex-critical"
