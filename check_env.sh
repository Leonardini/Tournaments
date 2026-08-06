#!/usr/bin/env bash
# =====================================================================================
# check_env.sh — does this machine have what the package needs?
#
# Run this BEFORE ./check_all.sh. It never runs a verification: it only reports which
# tools, libraries, packages and data files are present, what each one is needed for,
# and the exact command that installs the missing ones. This exists because a missing
# package otherwise shows up as a FAILED check, which looks like a failed reproduction.
#
# Usage:
#   ./check_env.sh              full report; exit 0 iff everything REQUIRED is present
#   ./check_env.sh --quiet      the verdict line only (same exit code)
#   ./check_env.sh --export     machine-readable HAVE_* assignments (used by check_all.sh)
# =====================================================================================
cd "$(dirname "$0")" || exit 2

MODE=report
case "${1:-}" in
  --export) MODE=export ;;
  --quiet)  MODE=quiet ;;
  --help|-h) sed -n '2,17p' "$0"; exit 0 ;;
  "") ;;
  *) echo "unknown option: $1  (try --help)" >&2; exit 2 ;;
esac

if [ -t 1 ] && [ "$MODE" = report ]; then
  G=$'\033[1;32m'; R=$'\033[1;31m'; Y=$'\033[1;33m'; C=$'\033[1;36m'; D=$'\033[2m'; Z=$'\033[0m'
else
  G=; R=; Y=; C=; D=; Z=
fi

EXPORTS=""; MISS_REQ=0; MISS_OPT=0

# record KEY PRESENT VERSION LABEL USED_FOR REQUIRED(1|0)
record() {
  local key="$1" present="$2" version="$3" label="$4" used="$5" req="$6"
  EXPORTS="${EXPORTS}HAVE_${key}=${present}
"
  if [ "$present" != 1 ]; then
    if [ "$req" = 1 ]; then MISS_REQ=$((MISS_REQ+1)); else MISS_OPT=$((MISS_OPT+1)); fi
  fi
  [ "$MODE" = report ] || return 0
  if [ "$present" = 1 ]; then
    printf "  ${G}ok  ${Z} %-20s %-16s ${D}%s${Z}\n" "$label" "$version" "$used"
  elif [ "$req" = 1 ]; then
    printf "  ${R}MISS${Z} %-20s %-16s ${D}%s${Z}\n" "$label" "-" "$used"
  else
    printf "  ${Y}--  ${Z} %-20s %-16s ${D}%s${Z}\n" "$label" "-" "$used"
  fi
}

section() { [ "$MODE" = report ] && printf "\n${C}%s${Z}\n" "$1"; return 0; }

# ---- base toolchain ------------------------------------------------------------------
CC_V=""; command -v cc >/dev/null 2>&1 && CC_V=$(cc --version 2>/dev/null | head -1 | sed -E 's/ *\(.*//' | cut -c1-30)
PY_V=""; command -v python3 >/dev/null 2>&1 && PY_V=$(python3 -c 'import sys;print("%d.%d.%d"%sys.version_info[:3])' 2>/dev/null)
R_V="";  command -v Rscript >/dev/null 2>&1 && R_V=$(Rscript --version 2>&1 | head -1 | sed -E 's/.*version ([0-9.]+).*/\1/')

section "Base toolchain"
record cc     "$([ -n "$CC_V" ] && echo 1 || echo 0)" "$CC_V"          "C compiler (cc)"  "every DP / CSP / screen engine" 1
record python "$([ -n "$PY_V" ] && echo 1 || echo 0)" "$PY_V"          "Python 3"         "CP-SAT checks, counting bounds" 1
record R      "$([ -n "$R_V"  ] && echo 1 || echo 0)" "$R_V"           "R"                "exact alpha*, certificates, figures" 1

# ---- Python packages -----------------------------------------------------------------
# name:import-path — one interpreter start for all of them.
PY_PROBE="ortools:ortools.sat.python.cp_model pulp:pulp matplotlib:matplotlib marimo:marimo cplex:cplex"
PY_OUT=""
if [ -n "$PY_V" ]; then
  PY_OUT=$(python3 - $PY_PROBE 2>/dev/null <<'PYEOF'
import importlib, sys
for spec in sys.argv[1:]:
    name, _, path = spec.partition(":")
    try:
        importlib.import_module(path)
    except Exception:
        print(name, "-"); continue
    try:
        from importlib.metadata import version
        v = version(name)
    except Exception:
        v = "present"
    print(name, v)
PYEOF
)
fi
pyver() { printf '%s\n' "$PY_OUT" | awk -v m="$1" '$1==m {print $2; found=1} END{if(!found) print "-"}'; }

section "Python packages          ${D}uv sync   (or: pip install -r requirements.txt)${Z}"
v=$(pyver ortools);    record py_ortools    "$([ "$v" != - ] && echo 1 || echo 0)" "$v" "ortools"    "CP-SAT: sec5, sec6, sec7 checks" 1
v=$(pyver pulp);       record py_pulp       "$([ "$v" != - ] && echo 1 || echo 0)" "$v" "pulp"       "CBC: sec5 orbit certificate" 1
v=$(pyver matplotlib); record py_matplotlib "$([ "$v" != - ] && echo 1 || echo 0)" "$v" "matplotlib" "optional: repro/figures/" 0
v=$(pyver marimo);     record py_marimo     "$([ "$v" != - ] && echo 1 || echo 0)" "$v" "marimo"     "optional: paley43_five_voters.py notebook" 0

# ---- R packages ----------------------------------------------------------------------
# Core four are really loaded (a package that will not load is worse than one absent);
# the rest are checked from their DESCRIPTION, which is much faster.
R_OUT=""
if [ -n "$R_V" ]; then
  R_OUT=$(Rscript --vanilla -e '
    load  <- c("igraph","lpSolve","rcdd","gmp")
    light <- c("combinat","Matrix","slam","pracma","magrittr","stringr","gtools",
               "matrixStats","tidyverse","testthat","Rcplex","cplexAPI")
    for (p in load)
      cat(p, if (suppressWarnings(requireNamespace(p, quietly=TRUE)))
                as.character(packageVersion(p)) else "-", "\n")
    for (p in light)
      cat(p, if (nzchar(system.file(package=p))) as.character(packageVersion(p)) else "-", "\n")
  ' 2>/dev/null)
fi
rver() { printf '%s\n' "$R_OUT" | awk -v m="$1" '$1==m {print $2; found=1} END{if(!found) print "-"}'; }

section "R packages               ${D}Rscript install_r_packages.R   (--all adds the appendices extras)${Z}"
v=$(rver igraph);  record r_igraph  "$([ "$v" != - ] && echo 1 || echo 0)" "$v" "igraph"  "graphs, canonical forms, all figures" 1
v=$(rver lpSolve); record r_lpSolve "$([ "$v" != - ] && echo 1 || echo 0)" "$v" "lpSolve" "float LP seed for the alpha* oracle" 1
v=$(rver rcdd);    record r_rcdd    "$([ "$v" != - ] && echo 1 || echo 0)" "$v" "rcdd"    "exact rational LP (alpha* = 2/3)" 1
v=$(rver gmp);     record r_gmp     "$([ "$v" != - ] && echo 1 || echo 0)" "$v" "gmp"     "exact certificate checks (solver-free)" 1
REXTRA_MISS=""
for p in combinat Matrix slam pracma magrittr stringr gtools matrixStats tidyverse testthat; do
  v=$(rver "$p"); [ "$v" = - ] && REXTRA_MISS="$REXTRA_MISS $p"
  EXPORTS="${EXPORTS}HAVE_r_${p}=$([ "$v" != - ] && echo 1 || echo 0)
"
done
if [ "$MODE" = report ]; then
  if [ -n "$REXTRA_MISS" ]; then
    printf "  ${Y}--  ${Z} %-20s %-16s ${D}%s${Z}\n" "appendices extras" "-" "missing:$REXTRA_MISS  (Rscript install_r_packages.R --all)"
  else
    printf "  ${G}ok  ${Z} %-20s %-16s ${D}%s${Z}\n" "appendices extras" "all present" "combinat, Matrix, slam, pracma, tidyverse, ..."
  fi
fi

# ---- optional external tools ---------------------------------------------------------
GLPK=0
if [ -n "$CC_V" ]; then
  t=$(mktemp -d 2>/dev/null || echo /tmp/rc_glpk.$$); mkdir -p "$t"
  printf '#include <glpk.h>\nint main(void){ glp_delete_prob(glp_create_prob()); return 0; }\n' > "$t/g.c"
  cc -O0 -o "$t/g" "$t/g.c" -I/opt/homebrew/include -L/opt/homebrew/lib \
       -I/usr/local/include -L/usr/local/lib -lglpk >/dev/null 2>&1 && GLPK=1
  rm -rf "$t"
fi
GENT=""; for g in gentourng nauty-gentourng; do command -v "$g" >/dev/null 2>&1 && GENT=$(command -v "$g") && break; done
[ -z "$GENT" ] && [ -n "${GENTOURNG:-}" ] && [ -x "${GENTOURNG}" ] && GENT="$GENTOURNG"
LRS=""; command -v lrs >/dev/null 2>&1 && LRS=$(command -v lrs)

section "Optional external tools  ${D}nothing below is needed for ./check_all.sh${Z}"
record glpk      "$GLPK" "$([ "$GLPK" = 1 ] && echo present)" "GLPK (-lglpk)" \
        "sec5 alpha_fast.c, the n=10 census pre-filter  [brew install glpk / apt-get install libglpk-dev]" 0
record gentourng "$([ -n "$GENT" ] && echo 1 || echo 0)" "$([ -n "$GENT" ] && echo present)" "nauty gentourng" \
        "n=11 census, whole-catalogue scans  [brew install nauty / apt-get install nauty]" 0
record lrs       "$([ -n "$LRS" ] && echo 1 || echo 0)" "$([ -n "$LRS" ] && echo present)" "lrs (lrslib)" \
        "sec5 non-margin-1 obstacle enumerator  [brew install lrslib / apt-get install lrslib]" 0

# ---- optional CPLEX ------------------------------------------------------------------
v=$(rver Rcplex);   RCPX=$([ "$v" != - ] && echo 1 || echo 0)
v2=$(rver cplexAPI); RAPI=$([ "$v2" != - ] && echo 1 || echo 0)
v3=$(pyver cplex);  PCPX=$([ "$v3" != - ] && echo 1 || echo 0)

section "IBM CPLEX (optional)     ${D}no headline result needs it; every reproducibility script has a free twin${Z}"
record cplex_r   "$RCPX" "$v"  "Rcplex"      "appendices set cover, sec5 nm1 cover" 0
record cplex_api "$RAPI" "$v2" "cplexAPI"    "sec6 ilp10 sweep" 0
record cplex_py  "$PCPX" "$v3" "cplex (py)"  "sec5 primal certificate, n10/reg11 ILPs" 0

# ---- shipped + downloaded data -------------------------------------------------------
DATA_OK=1
for f in data/regulartournaments11.RData data/n9_obstacle_keys.rds \
         data/n9_obstacle_catalog_exact.rds data/n9_nm1_obstacle_catalog.rds \
         data/n9_margin1only_tournaments.rds data/n9_nm1_obstacle_cover.rds \
         sec5_a3_boundary/n9_obstacle_certs.rds sec5_a3_boundary/n9_nm1_obstacle_certs.rds \
         sec7_paley43/d0_reps.txt; do
  [ -s "$f" ] || DATA_OK=0
done
MCKAY=$(ls data/mckay/*.txt 2>/dev/null | wc -l | tr -d ' ')

section "Data"
record data_shipped "$DATA_OK" "$([ "$DATA_OK" = 1 ] && echo "9 files")" "committed inputs" \
        "the certificates / catalogues the quick checks read" 1
record data_mckay "$([ "${MCKAY:-0}" -gt 0 ] && echo 1 || echo 0)" "$([ "${MCKAY:-0}" -gt 0 ] && echo "$MCKAY file(s)")" \
        "McKay catalogues" "only for the full censuses  [./get_data.sh]" 0

# ---- verdict -------------------------------------------------------------------------
if [ "$MODE" = export ]; then printf '%s' "$EXPORTS"; exit 0; fi

echo
if [ "$MISS_REQ" -eq 0 ]; then
  printf "${G}READY${Z} — everything required is installed"
  [ "$MISS_OPT" -gt 0 ] && printf " (%d optional item(s) absent; ./check_all.sh skips those)" "$MISS_OPT"
  printf ".\nNext: ${C}./check_all.sh${Z}\n"
  exit 0
else
  printf "${R}NOT READY${Z} — %d required item(s) missing. ./check_all.sh would SKIP the checks that need them.\n" "$MISS_REQ"
  echo "Install with:"
  echo "    uv sync                          # Python (or: pip install -r requirements.txt)"
  echo "    Rscript install_r_packages.R     # R"
  echo "  macOS system libraries:  brew install gmp mpfr glpk"
  echo "  Debian/Ubuntu:           apt-get install libgmp-dev libmpfr-dev libglpk-dev libxml2-dev"
  exit 1
fi
