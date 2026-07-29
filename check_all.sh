#!/usr/bin/env bash
# =====================================================================================
# check_all.sh — fast, self-contained verification of this reproducibility package.
# Runs the quick "check the result" step for each section and reports PASS / FAIL / SKIP.
# It uses only shipped data + free tools (C compiler, OR-Tools, R with gmp/igraph/lpSolve,
# GLPK); the HPC censuses, nauty `gentourng` runs, McKay downloads, and CPLEX-only scripts
# are NOT part of this — each section's README documents those separately.
# A single CPLEX-gated check is skipped (not failed) when CPLEX is absent.
#
# Usage:  ./check_all.sh          (~1-2 minutes)
# =====================================================================================
cd "$(dirname "$0")"
G=$'\033[1;32m'; R=$'\033[1;31m'; Y=$'\033[1;33m'; C=$'\033[1;36m'; Z=$'\033[0m'
PASS=0; FAIL=0; SKIP=0
have_rcplex=$(Rscript -e 'cat(if (requireNamespace("Rcplex", quietly=TRUE)) 1 else 0)' 2>/dev/null)

# check  LABEL  MARKER(literal substring, or the token EXIT0)  NEEDS(-|rcplex)  CMD
check() {
  local label="$1" marker="$2" needs="$3" cmd="$4"
  if [ "$needs" = rcplex ] && [ "$have_rcplex" != 1 ]; then
    printf "  ${Y}SKIP${Z} %s  (needs CPLEX)\n" "$label"; SKIP=$((SKIP+1)); return
  fi
  local out rc ok=0
  out=$(eval "$cmd" 2>&1); rc=$?
  if [ "$marker" = EXIT0 ]; then [ $rc -eq 0 ] && ok=1
  else printf '%s' "$out" | grep -qF -- "$marker" && ok=1; fi
  if [ $ok -eq 1 ]; then printf "  ${G}PASS${Z} %s\n" "$label"; PASS=$((PASS+1))
  else printf "  ${R}FAIL${Z} %s\n" "$label"; FAIL=$((FAIL+1)); printf "       (wanted: %s)\n" "$marker"; fi
}

echo "${C}== sec3_mhp (median hitting problem; FAS counterexamples) ==${Z}"
check "sec3: min-weight FAS counterexamples" "unique min-weight FAS confirmed, value 5" - \
      "cd sec3_mhp && Rscript make_family_and_mhp_figs.R; rm -f *.pdf"

echo "${C}== sec4_fas_hs3 (FAS vs HS3; T* counterexample) ==${Z}"
check "sec4: T* has FAS 17 > HS3 16"        "minimum 3-cycle hitting set has 16 arcs" - \
      "cd sec4_fas_hs3 && Rscript make_tstar_figs.R; rm -f *.pdf"

echo "${C}== sec5_a3_boundary (A(3) fails on the boundary) ==${Z}"
check "sec5: cA3 exact alpha* = 2/3 (rational)" "alpha* == 2/3 exactly ? TRUE" - \
      "cd sec5_a3_boundary && Rscript verify_ce1068.R; rm -f ce1068_inmask.txt"
check "sec5: cA3 not-3-real / 5-real (CP-SAT)" "k=3 (maj>=2): INFEASIBLE (proven)" - \
      "cd sec5_a3_boundary && python3 independent_realize3_cpsat.py"
check "sec5: 47/47 obstacle certs (gmp-only)"  "STATIC (gmp-only) certification: 47/47 obstacles" - \
      "cd sec5_a3_boundary && Rscript verify_obstacle_certs.R n9_obstacle_certs.rds"
check "sec5: 72/72 non-margin-1 certs (gmp)"   "STATIC (gmp-only) certification: 72/72 non-margin-1 obstacles" - \
      "cd sec5_a3_boundary && Rscript verify_nm1_obstacle_certs.R n9_nm1_obstacle_certs.rds"

echo "${C}== sec6_bounds (bounds on N(k)) ==${Z}"
check "sec6: counting bounds table (asserts)"  EXIT0 - \
      "cd sec6_bounds && python3 counting_bounds/extended_table1_bounds.py"
check "sec6: near-regular bijection + bound"   EXIT0 - \
      "cd sec6_bounds && python3 counting_bounds/nearreg_table_bounds.py"

echo "${C}== sec7_paley43 (Paley(43) not 5-realizable => N(5) <= 43) ==${Z}"
( cd sec7_paley43 && cc -O3 -march=native -pthread -o /tmp/rc_dp43 dp43.c ) 2>/dev/null \
  && echo "  (built dp43)" || echo "  ${R}build failed${Z}"
check "sec7: certified MAS(7)=14 self-test"    "selftest q=7 PASSED"  - \
      "cd sec7_paley43 && mkdir -p /tmp/st7 && /tmp/rc_dp43 selftest 7 /tmp/st7"
check "sec7: certified MAS(11)=35 self-test"   "selftest q=11 PASSED" - \
      "cd sec7_paley43 && mkdir -p /tmp/st11 && /tmp/rc_dp43 selftest 11 /tmp/st11"
check "sec7: CP-SAT realizability gauntlet"    "GAUNTLET: PASS"       - \
      "cd sec7_paley43 && python3 realize5_cpsat.py --gauntlet"

echo "${C}== appendices (obstacle-dual / LP tools) ==${Z}"
check "appendices: min-set-cover ILP demo"     "Total elements covered: 5/5" rcplex \
      "cd appendices && Rscript minimum_set_cover.R"

rm -f /tmp/rc_dp43
echo
if [ "$FAIL" -eq 0 ]; then
  printf "${G}ALL CHECKS OK${Z}  —  PASS=%d  SKIP=%d (CPLEX not installed)  FAIL=0\n" "$PASS" "$SKIP"
else
  printf "${R}SOME CHECKS FAILED${Z}  —  PASS=%d  SKIP=%d  FAIL=%d\n" "$PASS" "$SKIP" "$FAIL"
  echo "Re-run the failing section's quick check from its README to see the full output."
fi
