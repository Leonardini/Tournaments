#!/usr/bin/env bash
# =====================================================================================
# check_all.sh — fast, self-contained verification of this reproducibility package.
# Runs the quick "check the result" step for each section and reports PASS / FAIL / SKIP.
# It uses only shipped data + free tools (C compiler, OR-Tools, R with gmp/igraph/lpSolve);
# the HPC censuses, nauty `gentourng` runs, McKay downloads, and CPLEX-only scripts are NOT
# part of this — each section's README documents those separately.
#
# A check whose tools are not installed is SKIPPED, not failed: run ./check_env.sh first to
# see what is missing and how to install it. Each check shows a live elapsed-time counter
# while it runs, so a slow step is visibly running rather than apparently hung.
#
# Usage:  ./check_all.sh            (~1-2 minutes)
#         ./check_all.sh -v         stream each check's own output as it runs
# =====================================================================================
cd "$(dirname "$0")" || exit 2
G=$'\033[1;32m'; R=$'\033[1;31m'; Y=$'\033[1;33m'; C=$'\033[1;36m'; D=$'\033[2m'; Z=$'\033[0m'
PASS=0; FAIL=0; SKIP=0; SKIP_DEPS=0
VERBOSE=0; [ "${1:-}" = "-v" ] || [ "${1:-}" = "--verbose" ] && VERBOSE=1
TTY=0; [ -t 1 ] && [ "$VERBOSE" = 0 ] && TTY=1
T_ALL=$SECONDS

# ---- what is installed (one probe, shared with ./check_env.sh) -----------------------
if [ -f ./check_env.sh ]; then
  eval "$(bash ./check_env.sh --export 2>/dev/null)"
else
  echo "${Y}warning:${Z} check_env.sh not found — dependency-aware SKIP is off"
fi

human() {   # human-readable name of a dependency key
  case "$1" in
    cc) echo "a C compiler" ;;
    python) echo "Python 3" ;;
    R) echo "R" ;;
    py_*) echo "Python package ${1#py_}" ;;
    r_*) echo "R package ${1#r_}" ;;
    cplex_r) echo "R package Rcplex (IBM CPLEX)" ;;
    glpk) echo "GLPK" ;;
    *) echo "$1" ;;
  esac
}

# ---- check  LABEL  MARKER(literal substring, or the token EXIT0)  NEEDS(keys, or -)  CMD
check() {
  local label="$1" marker="$2" needs="$3" cmd="$4"

  local missing="" k v
  if [ "$needs" != - ]; then
    for k in $needs; do
      eval "v=\${HAVE_$k:-1}"                      # unknown key => assume present
      [ "$v" = 1 ] || missing="$missing $(human "$k"),"
    done
  fi
  if [ -n "$missing" ]; then
    printf "  ${Y}SKIP${Z} %-46s ${D}needs%s${Z}\n" "$label" "${missing%,}"
    SKIP=$((SKIP+1)); SKIP_DEPS=$((SKIP_DEPS+1)); return
  fi

  local t0=$SECONDS out rc ok=0 tmp el pid
  tmp=$(mktemp "${TMPDIR:-/tmp}/rc_check.XXXXXX")
  if [ "$TTY" = 1 ]; then
    printf "  ${C}....${Z} %-46s" "$label"          # overwritten by the live counter
  else
    printf "  ${C}....${Z} %-46s ${D}running${Z}\n" "$label"
  fi

  if [ "$VERBOSE" = 1 ]; then
    ( eval "$cmd" ) 2>&1 | tee "$tmp"; rc=${PIPESTATUS[0]}
  else
    ( eval "$cmd" ) >"$tmp" 2>&1 &
    pid=$!
    if [ "$TTY" = 1 ]; then
      while kill -0 "$pid" 2>/dev/null; do
        el=$((SECONDS-t0))
        printf "\r  ${C}run ${Z} %-46s ${D}%3ds${Z}" "$label" "$el"
        sleep 1
      done
    fi
    wait "$pid"; rc=$?
  fi
  out=$(cat "$tmp"); rm -f "$tmp"
  el=$((SECONDS-t0))

  if [ "$marker" = EXIT0 ]; then [ "$rc" -eq 0 ] && ok=1
  else printf '%s' "$out" | grep -qF -- "$marker" && ok=1; fi

  [ "$TTY" = 1 ] && printf "\r"
  if [ "$ok" -eq 1 ]; then
    printf "  ${G}PASS${Z} %-46s ${D}%3ds${Z}\n" "$label" "$el"; PASS=$((PASS+1))
  else
    printf "  ${R}FAIL${Z} %-46s ${D}%3ds${Z}\n" "$label" "$el"; FAIL=$((FAIL+1))
    printf "       ${D}wanted: %s${Z}\n" "$marker"
    printf '%s\n' "$out" | tail -5 | sed 's/^/       | /'
  fi
}

printf "${C}Tournaments reproducibility package — quick verification${Z}  ${D}(~1-2 min)${Z}\n"

echo "${C}== sec3_mhp (median hitting problem; FAS counterexamples) ==${Z}"
check "sec3: min-weight FAS counterexamples" "unique min-weight FAS confirmed, value 5" "R r_igraph" \
      "cd sec3_mhp && Rscript make_family_and_mhp_figs.R; rm -f *.pdf"

echo "${C}== sec4_fas_hs3 (FAS vs HS3; T* counterexample) ==${Z}"
check "sec4: T* has FAS 17 > HS3 16"        "minimum 3-cycle hitting set has 16 arcs" "R r_igraph r_lpSolve" \
      "cd sec4_fas_hs3 && Rscript make_tstar_figs.R; rm -f *.pdf"
check "sec4: regular n = 11, HS3 < FAS only at T*" "CONFIRMED: of the 1223 regular tournaments on 11 vertices, 48 are 3-inducible" "cc R r_igraph python py_ortools" \
      "cd sec4_fas_hs3 && ./reg11_fas_hs3.sh"

echo "${C}== sec5_a3_boundary (A(3) fails on the boundary) ==${Z}"
check "sec5: cA3 exact alpha* = 2/3 (rational)" "alpha* == 2/3 exactly ? TRUE" "R r_lpSolve r_rcdd r_gmp" \
      "cd sec5_a3_boundary && Rscript verify_ce1068.R; rm -f ce1068_inmask.txt"
check "sec5: cA3 not-3-real / 5-real (CP-SAT)" "k=3 (maj>=2): INFEASIBLE (proven)" "python py_ortools" \
      "cd sec5_a3_boundary && python3 independent_realize3_cpsat.py"

echo "${C}== appendices (obstacle-dual / LP tools) ==${Z}"
check "n = 9 obstacles: 59 + 51 classes (exact)" "n9_signed_obstacles_254.tsv: 51/51 classes certified exactly" "python" \
      "cd appendices/obstacle_catalogue && python3 verify_catalogue.py"
check "appendices: min-set-cover ILP demo"     "Total elements covered: 5/5" "R cplex_r" \
      "cd appendices && Rscript minimum_set_cover.R"

rm -rf "$DP43" "${TMPDIR:-/tmp}/st7" "${TMPDIR:-/tmp}/st11"
echo
if [ "$FAIL" -gt 0 ]; then
  printf "${R}SOME CHECKS FAILED${Z}  —  PASS=%d  SKIP=%d  FAIL=%d  ${D}(%ds)${Z}\n" "$PASS" "$SKIP" "$FAIL" "$((SECONDS-T_ALL))"
  echo "Re-run the failing section's quick check from its README, or ./check_all.sh -v, to see the full output."
elif [ "$SKIP_DEPS" -gt 0 ]; then
  printf "${Y}NOTHING FAILED, BUT THE RUN IS INCOMPLETE${Z}  —  PASS=%d  SKIP=%d  FAIL=0  ${D}(%ds)${Z}\n" \
         "$PASS" "$SKIP" "$((SECONDS-T_ALL))"
else
  printf "${G}ALL CHECKS OK${Z}  —  PASS=%d  SKIP=%d  FAIL=0  ${D}(%ds)${Z}\n" "$PASS" "$SKIP" "$((SECONDS-T_ALL))"
fi
[ "$SKIP_DEPS" -gt 0 ] && printf "${Y}%d check(s) were skipped because a tool is missing${Z}, not because anything failed — run ${C}./check_env.sh${Z} to see what to install.\n" "$SKIP_DEPS"
exit $([ "$FAIL" -eq 0 ] && echo 0 || echo 1)
