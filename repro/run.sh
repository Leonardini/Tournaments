#!/usr/bin/env bash
# =====================================================================================
# BASELINE NODE — package-wide fast verification.
#
# Runs the repository's own quick verifier, check_all.sh: 11 self-checks spanning
# §3-§7 plus the CPLEX set-cover demo. Establishes that this machine's toolchain
# reproduces the package's shipped claims before any heavy node is launched.
#
# Metric: PASS / SKIP / FAIL counts (target PASS=11, FAIL=0 — CPLEX is installed
# here, so the normally-skipped Rcplex check should also run).
# =====================================================================================
source "$(dirname "$0")/env.sh"
cd "$REPRO_ROOT"

sysinfo

banner "check_all.sh — quick verification of every section"
t0=$SECONDS
set +e
./check_all.sh 2>&1 | tee "$SCRATCH/check_all.out"
set -e
elapsed=$((SECONDS - t0))

# strip the ANSI colouring check_all.sh emits before parsing
out=$(sed $'s/\033\\[[0-9;]*m//g' "$SCRATCH/check_all.out")
summary=$(printf '%s' "$out" | grep -E 'ALL CHECKS OK|SOME CHECKS FAILED' || true)
np=$(printf '%s' "$out" | grep -c '^  PASS ' || true)
ns=$(printf '%s' "$out" | grep -c '^  SKIP ' || true)
nf=$(printf '%s' "$out" | grep -c '^  FAIL ' || true)

banner "results"
metric wall_seconds "$elapsed"
metric checks_pass "$np"
metric checks_skip "$ns"
metric checks_fail "$nf"

# The individual claims each quick check settles, as paper-value vs observed-value.
verdict() { [ "$1" = 1 ] && echo aligned || echo divergent; }
g() { printf '%s' "$out" | grep -qF -- "$1" && echo 1 || echo 0; }

claim "sec3.mhp-min-weight-FAS"      "min-weight FAS = 5, unique"        "$(printf '%s' "$out" | grep -q '^  PASS sec3' && echo 'min-weight FAS = 5, unique' || echo 'not confirmed')" "$(verdict "$(g '  PASS sec3')")"
claim "sec4.Tstar-FAS-gt-HS3"        "FAS = 17 > 16 = HS3"              "$(printf '%s' "$out" | grep -q '^  PASS sec4' && echo 'FAS = 17 > 16 = HS3' || echo 'not confirmed')" "$(verdict "$(g '  PASS sec4')")"
claim "sec5.cA3-alpha-star"          "alpha* = 2/3 exactly (rational)"  "$(printf '%s' "$out" | grep -q 'PASS sec5: cA3 exact' && echo 'alpha* = 2/3 exactly' || echo 'not confirmed')" "$(verdict "$(g 'PASS sec5: cA3 exact')")"
claim "sec5.cA3-not-3-inducible"     "k=3 INFEASIBLE, k=5 FEASIBLE"     "$(printf '%s' "$out" | grep -q 'PASS sec5: cA3 not-3-real' && echo 'k=3 INFEASIBLE, k=5 FEASIBLE' || echo 'not confirmed')" "$(verdict "$(g 'PASS sec5: cA3 not-3-real')")"
claim "sec5.obstacle-certs-47"       "47/47 obstacles certified"        "$(printf '%s' "$out" | grep -q 'PASS sec5: 47/47' && echo '47/47 certified' || echo 'not confirmed')" "$(verdict "$(g 'PASS sec5: 47/47')")"
claim "sec5.nm1-certs-72"            "72/72 non-margin-1 certified"     "$(printf '%s' "$out" | grep -q 'PASS sec5: 72/72' && echo '72/72 certified' || echo 'not confirmed')" "$(verdict "$(g 'PASS sec5: 72/72')")"
claim "sec6.counting-bounds"         "N(5) <= 39 regular, <= 38 near-reg" "$(printf '%s' "$out" | grep -q 'PASS sec6: counting' && printf '%s' "$out" | grep -q 'PASS sec6: near-regular' && echo 'both tables assert clean' || echo 'not confirmed')" "$(verdict "$( [ "$(g 'PASS sec6: counting')" = 1 ] && [ "$(g 'PASS sec6: near-regular')" = 1 ] && echo 1 || echo 0)")"
claim "sec7.dp43-selftest-q7-q11"    "MAS(7)=14, MAS(11)=35 == brute force" "$(printf '%s' "$out" | grep -q 'PASS sec7: certified MAS(7)' && printf '%s' "$out" | grep -q 'PASS sec7: certified MAS(11)' && echo 'both self-tests PASSED' || echo 'not confirmed')" "$(verdict "$( [ "$(g 'PASS sec7: certified MAS(7)')" = 1 ] && [ "$(g 'PASS sec7: certified MAS(11)')" = 1 ] && echo 1 || echo 0)")"
claim "sec7.cpsat-gauntlet"          "GAUNTLET: PASS"                   "$(printf '%s' "$out" | grep -q 'PASS sec7: CP-SAT' && echo 'GAUNTLET: PASS' || echo 'not confirmed')" "$(verdict "$(g 'PASS sec7: CP-SAT')")"

banner "verdict"
echo "$summary"
echo "PASS=$np SKIP=$ns FAIL=$nf  in ${elapsed}s"
[ "$nf" -eq 0 ] || { echo "BASELINE FAILED: $nf quick check(s) did not reproduce" >&2; exit 1; }
echo "BASELINE OK: all $np quick checks reproduce on this machine ($ns skipped)"
