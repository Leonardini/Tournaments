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
# Samples this run's process-tree RSS and the machine's swap every 30 s into the log, and
# kills the run if it is the cause of memory pressure. Peak RSS is reported as a METRIC so
# the report can quote a real memory cost per node instead of an estimate.
#
# Two things have to be true for a kill to be correct: memory pressure exists, AND this run
# is the cause of it. Both halves matter, and getting either wrong kills healthy runs:
#
#   * NOT absolute swap. This laptop routinely sits at 7-18 GB of swap in use from unrelated
#     applications, so an absolute threshold fires immediately on a run using 10 MB.
#   * NOT swap growth alone either. Other processes on this machine (the user's own long
#     compute) can drive swap up several GB while this run holds 100 MB. Blaming the run for
#     that killed an 8-hour census at the 71-minute mark.
#
# So: kill outright if the run's OWN resident set passes RSS_LIMIT_GB — then it is
# unambiguously the problem. Kill on swap growth past SWAP_GROWTH_GB only when the run's RSS is
# at least SWAP_BLAME_RSS_GB (default 2), i.e. large enough to plausibly be the cause. Otherwise
# warn and keep going: the machine is under pressure from elsewhere and killing this run would
# not relieve it.
#
# The two budgets are sized against the heaviest thing this reproduction runs, the q=43 layer
# build: documented at ~5 GB resident, with a Burnside ceiling of 9.32 GB, observed peaking at
# 5.94 GB. A 3 GB swap-growth budget is SMALLER than that legitimate footprint — allocating 6-9 GB
# on a 24 GB machine that already has other tenants pushes a few GB to swap as a matter of course,
# so the trigger fired on normal operation and killed a healthy build. The resident-set cap is the
# guard that actually encodes the laptop rule (keep this job's RSS well inside physical RAM), so
# it is tightened to just above the workload's own ceiling, where a genuine runaway shows up
# immediately; the swap-growth kill is widened to a backstop for a true runaway rather than a
# first line of defence.
#   RSS_LIMIT_GB    11   applied to phys_footprint (anonymous), not RSS
#   SWAP_GROWTH_GB   6   (accommodates the documented ~5 GB build; was 3)
WD_PID=""
swap_used_gb() { sysctl -n vm.swapusage | awk '{for(i=1;i<=NF;i++) if($i=="used"){gsub(/M/,"",$(i+2)); print $(i+2)/1024; exit}}'; }

# Kill a run and everything it spawned, deepest first, skipping the caller.
#
# `kill -TERM -$pid` needs $pid to be a process-GROUP leader, which run.sh is not under the orx
# local runner: the negative-pid form fails and the usual fallback `kill -TERM $pid` reaps only
# the shell. Its children keep running, unsupervised and invisible to orx. That actually happened
# — two orphaned `dp43` processes survived two killed runs, kept allocating (one reached 4.74 GB
# over 11 minutes), and the memory they held is what starved the next attempt into being killed
# too. So walk the tree explicitly, then SIGKILL whatever ignores SIGTERM.
kill_tree() {
  local p="$1" self="${2:-0}" c
  for c in $(pgrep -P "$p" 2>/dev/null); do
    [ "$c" = "$self" ] || kill_tree "$c" "$self"
  done
  [ "$p" = "$self" ] || kill -TERM "$p" 2>/dev/null || true
}
kill_run_tree() {                     # $1 = root pid, $2 = pid to spare (the caller)
  kill_tree "$1" "${2:-0}"
  sleep 5
  local c
  for c in $(pgrep -P "$1" 2>/dev/null); do
    [ "$c" = "${2:-0}" ] || kill -KILL "$c" 2>/dev/null || true
  done
  [ "$1" = "${2:-0}" ] || kill -KILL "$1" 2>/dev/null || true
}
watchdog_start() {
  local grow="${SWAP_GROWTH_GB:-6}" rmax="${RSS_LIMIT_GB:-11}" blame="${SWAP_BLAME_RSS_GB:-2}" root=$$ base
  base=$(swap_used_gb); base=${base:-0}
  printf 'WATCHDOG baseline: swap already in use by the machine = %.2f GB (growth budget %s GB chargeable only above %s GB run RSS, RSS cap %s GB)\n' "$base" "$grow" "$blame" "$rmax"
  ( peak=0
    while :; do
      sleep 30
      local swap rss
      swap=$(swap_used_gb); swap=${swap:-0}
      # RSS is the WRONG metric here. dp43 mmaps each parent layer file read-only
      # (MAP_SHARED/PROT_READ), so up to 9.3 GB of clean, instantly reclaimable page cache
      # counts toward RSS while creating no memory pressure whatever. Judging on RSS killed a
      # healthy build at "11.03 GB" while swap sat BELOW its baseline. Measured directly: a
      # 2 GB read-only mmap fully touched reads 2.01 GB of RSS but 8.7 MB of phys_footprint.
      # So decide on phys_footprint (macOS's anonymous+compressed measure, what Activity
      # Monitor calls Memory) summed over the tree, and log RSS alongside for context.
      pids=$(ps -Ao ppid=,pid= | awk -v r="$root" '
        { par[$2]=$1 } END { for (p in par) { q=p; d=0
            while (q!="" && q!=1 && d<40) { if (q==r) { print p; break } q=par[q]; d++ } } }')
      rss=$(ps -Ao rss=,pid= | awk -v L="$pids" 'BEGIN{split(L,a," "); for(i in a) want[a[i]]=1}
              want[$2]{s+=$1} END{printf "%.2f", s/1048576}')
      mem=$(for pp in $pids; do footprint -p "$pp" 2>/dev/null | awk '/phys_footprint:/{
                v=$2; u=$3;
                if (u=="GB") v*=1048576; else if (u=="MB") v*=1024;
                print v; exit}'; done | awk '{s+=$1} END{printf "%.2f", s/1048576}')
      rss=${rss:-0}; mem=${mem:-0}
      awk -v s="$swap" -v b="$base" -v m="$mem" -v r="$rss" 'BEGIN{printf "WATCHDOG  swap=%.2fGB (+%.2f vs baseline)  run_mem=%.2fGB (rss %.2fGB, incl. mmapped layer files)\n", s, s-b, m, r}'
      peak=$(awk -v a="$peak" -v b="$mem" 'BEGIN{print (b>a)?b:a}')
      printf 'METRIC\tpeak_rss_gb\t%.2f\n' "$peak"
      if awk -v m="$mem" -v l="$rmax" 'BEGIN{exit !(m > l)}'; then
        echo "WATCHDOG: run anonymous memory passed ${rmax}GB — killing it to protect the laptop" >&2
        kill_run_tree "$root" "$BASHPID"; exit 1
      fi
      if awk -v s="$swap" -v b="$base" -v g="$grow" 'BEGIN{exit !(s-b > g)}'; then
        if awk -v m="$mem" -v c="$blame" 'BEGIN{exit !(m >= c)}'; then
          echo "WATCHDOG: swap grew past ${grow}GB while this run holds ${mem}GB anonymous — this run is the likely cause, killing it" >&2
          kill_run_tree "$root" "$BASHPID"; exit 1
        fi
        awk -v s="$swap" -v b="$base" -v m="$rss" 'BEGIN{
          printf "WATCHDOG WARNING: machine swap is up %.2fGB since this run started, but the run holds only %.2fGB — other processes are the cause, not this run. Continuing.\n", s-b, m }' >&2
      fi
    done ) &
  WD_PID=$!
}
watchdog_stop() { [ -n "$WD_PID" ] && kill "$WD_PID" 2>/dev/null || true; }
