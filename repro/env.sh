# =====================================================================================
# repro/env.sh — the FIXED environment contract for the arXiv 2607.26690 reproduction.
#
# Sourced by repro/run.sh on every experiment branch. This file is identical on every
# node: the run command (`bash repro/run.sh`) and this environment never vary, so all
# nodes' results stay comparable. Per-node work lives in repro/run.sh alone.
#
# Machine: the author's Mac (orx --backend local). 14 cores / 24 GB RAM, so the local
# safety rule is at most 10 cores and a combined RSS well inside physical RAM; THREADS
# is capped at 8 here and a watchdog samples swap so nothing runs the laptop into swap.
# =====================================================================================
set -euo pipefail

REPRO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
export REPRO_ROOT
export THREADS="${THREADS:-8}"            # laptop rule: never more than 10 cores
export SCRATCH="${SCRATCH:-${TMPDIR:-/tmp}/orx-repro}"
mkdir -p "$SCRATCH"

# External inputs that are not committed (see the package's "Data policy"):
#   - nauty 2.8.6 gentourng, for whole-catalogue tournament generation
#   - McKay's order-9 / order-10 tournament catalogues
export GENTOURNG="${GENTOURNG:-$HOME/Downloads/DownloadedSoftware/nauty2_8_6/gentourng}"
export MCKAY_DIR="${MCKAY_DIR:-$HOME/Downloads/NonPriority/Conjectures/KemenyMedian/Tournaments/SourceFiles}"

banner() { printf '\n======== %s ========\n' "$*"; }

# claim <id> <paper-value> <observed-value> <verdict>
# One machine-greppable line per paper claim. In local mode the run log is the only
# evidence channel, so every number the report will quote has to appear here.
claim() { printf 'CLAIM\t%s\tpaper=%s\tobserved=%s\t%s\n' "$1" "$2" "$3" "$4"; }

# metric <name> <value>  — a scalar worth plotting (timings, counts, memory)
metric() { printf 'METRIC\t%s\t%s\n' "$1" "$2"; }

sysinfo() {
  banner "environment"
  printf 'date          %s\n' "$(date -u '+%Y-%m-%dT%H:%M:%SZ')"
  printf 'host          %s\n' "$(hostname -s)"
  printf 'uname         %s\n' "$(uname -mrs)"
  printf 'cores(total)  %s\n' "$(sysctl -n hw.ncpu)"
  printf 'THREADS       %s\n' "$THREADS"
  printf 'memory(GB)    %.1f\n' "$(echo "$(sysctl -n hw.memsize) / 1073741824" | bc -l)"
  printf 'disk avail    %s\n' "$(df -h "$SCRATCH" | tail -1 | awk '{print $4}')"
  printf 'commit        %s\n' "$(git rev-parse --short HEAD 2>/dev/null || echo n/a)"
  printf 'cc            %s\n' "$(cc --version | head -1)"
  printf 'R             %s\n' "$(Rscript --version 2>&1 | head -1)"
  printf 'python        %s\n' "$(python3 --version)"
  printf 'ortools       %s\n' "$(python3 -c 'import ortools;print(ortools.__version__)' 2>/dev/null || echo MISSING)"
  printf 'cplex         %s\n' "$(python3 -c 'import cplex;print(cplex.__version__)' 2>/dev/null || echo MISSING)"
  printf 'gentourng     %s\n' "$([ -x "$GENTOURNG" ] && echo "$GENTOURNG" || echo MISSING)"
  printf 'mckay dir     %s\n' "$([ -d "$MCKAY_DIR" ] && echo "$MCKAY_DIR" || echo MISSING)"
}

# ---- memory / disk watchdog ---------------------------------------------------------
# Samples swap and this run's process-tree RSS every 30 s into the log, and kills the
# run if swap grows past SWAP_LIMIT_GB (default 3 GB). Peak RSS is reported as a METRIC
# so the report can quote a real memory cost per node instead of an estimate.
WD_PID=""
watchdog_start() {
  local limit="${SWAP_LIMIT_GB:-3}" root=$$
  ( peak=0
    while :; do
      sleep 30
      local swap rss
      swap=$(sysctl -n vm.swapusage | sed -n 's/.*used = \([0-9.]*\)M.*/\1/p')
      swap=${swap:-0}
      rss=$(ps -Ao rss=,ppid=,pid= | awk -v r="$root" '
        { rssv[$3]=$1; par[$3]=$2 }
        END { for (p in par) { q=p; d=0
                while (q!="" && q!=1 && d<40) { if (q==r) { s+=rssv[p]; break } q=par[q]; d++ } }
              print s+0 }')
      rss=$(echo "$rss / 1048576" | bc -l)
      awk -v s="$swap" -v m="$rss" 'BEGIN{printf "WATCHDOG  swap=%.2fGB  rss=%.2fGB\n", s/1024, m}'
      peak=$(awk -v a="$peak" -v b="$rss" 'BEGIN{print (b>a)?b:a}')
      printf 'METRIC\tpeak_rss_gb\t%.2f\n' "$peak"
      if awk -v s="$swap" -v l="$limit" 'BEGIN{exit !(s/1024 > l)}'; then
        echo "WATCHDOG: swap exceeded ${limit}GB — killing run to protect the laptop" >&2
        kill -TERM -"$root" 2>/dev/null || kill -TERM "$root"
        exit 1
      fi
    done ) &
  WD_PID=$!
}
watchdog_stop() { [ -n "$WD_PID" ] && kill "$WD_PID" 2>/dev/null || true; }
