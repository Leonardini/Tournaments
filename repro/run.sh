#!/usr/bin/env bash
# =====================================================================================
# S7-D — the full level-<=1 shell: the complete Paley(43) proof.  [HEADLINE LINE, step 4]
#
# S7-A certified the MAS engine and established MAS >= 543 independently. S7-B ran the
# screen exhaustively but only on the level-0 shell (17.7 M orders). S7-C showed the
# screen's safeguards hold. Two gaps remain, and both need the q = 43 layer tables:
#
#   MAS <= 543          only the dp43 join over the full delta <= 2 shell certifies it
#   the level-1 layer   1,821,652 further orbits — 93x more orders than level 0
#
# This node runs the package's own driver `sec7_paley43/reproduce_paley43.sh` unchanged,
# stages 0-4, which does both and ends in the proof banner. Reference figures it must hit:
#   certified MAS = 543 · delta<=1 orbit count = 1,841,303 (x 903 = 1,662,696,609 orders)
#   level-<=1 screen: TRUE_DISJOINT = 0 over 4,376,325,129 (rep, pool) pairs   [App. A.3]
#
# DISK IS THE BINDING CONSTRAINT, not CPU or RAM (~8 threads, ~5 GB resident).
# The layer tables are ~48 GB — the engine's own Burnside ceiling says 48.28 GB and the
# build approaches it. Two guards, because filling this boot volume is the hazard:
#   * a pre-flight check that refuses to start below MIN_FREE_GB;
#   * a disk watchdog that aborts the build if free space falls under ABORT_FREE_GB,
#     leaving the partial tables in place so a later run resumes rather than restarts.
# The tables live in $SCRATCH (via a symlink at the path the driver expects) so that a
# resumed run reuses them: `dp43 layers` records each finished layer in its manifest and
# skips it on the next pass, and stage 2 skips entirely once layer 22 is recorded.
# =====================================================================================
source "$(dirname "$0")/env.sh"
cd "$REPRO_ROOT"

MIN_FREE_GB="${MIN_FREE_GB:-60}"      # refuse to start below this
ABORT_FREE_GB="${ABORT_FREE_GB:-8}"   # abort mid-build below this

free_gb() { df -g "$1" | tail -1 | awk '{print $4}'; }

sysinfo

banner "pre-flight: disk"
FREE=$(free_gb "$SCRATCH")
echo "  scratch            $SCRATCH"
echo "  free on its volume ${FREE} GB"
echo "  required to start  ${MIN_FREE_GB} GB   (48 GB of layer tables + join/enum + margin)"
metric free_gb_at_start "$FREE"
if [ "${FREE:-0}" -lt "$MIN_FREE_GB" ]; then
  cat >&2 <<EOF

S7-D not started: only ${FREE} GB free, needs ${MIN_FREE_GB} GB.

The q=43 delta<=2 layer tables are ~48 GB (\`dp43 burnside 43\` puts the ceiling at
48.28 GB). Free about $(( MIN_FREE_GB - FREE )) GB more and re-launch this same node —
nothing else about it changes, and any layers already built are reused.
EOF
  exit 1
fi

# keep the expensive tables outside the per-run clone so a partial build resumes
PERSIST="$SCRATCH/dp43run43"
mkdir -p "$PERSIST"
rm -rf sec7_paley43/dp43run43
ln -s "$PERSIST" sec7_paley43/dp43run43
echo "  layer tables       $PERSIST  (symlinked as sec7_paley43/dp43run43)"
if [ -f "$PERSIST/manifest.txt" ]; then
  echo "  resuming: manifest already records $(grep -c '^L ' "$PERSIST/manifest.txt") layer entries"
  du -sh "$PERSIST" | awk '{print "  tables on disk so far: " $1}'
fi
# reuse a previously canonicalised shell if one survived
[ -f "$PERSIST/delta1_reps.txt" ] && cp "$PERSIST/delta1_reps.txt" sec7_paley43/delta1_reps.txt

watchdog_start
# disk watchdog: abort before the volume is endangered, keeping the partial build
( set +e +o pipefail
  root=$$
  while :; do
    sleep 60
    f=$(free_gb "$SCRATCH"); f=${f:-0}
    printf 'DISK  %s GB free  (tables %s)\n' "$f" "$(du -sh "$PERSIST" 2>/dev/null | awk '{print $1}')"
    if [ "$f" -lt "$ABORT_FREE_GB" ]; then
      echo "DISKWATCH: only ${f} GB free — aborting the build to protect the volume (partial tables kept for resume)" >&2
      kill -TERM -"$root" 2>/dev/null || kill -TERM "$root"
      exit 1
    fi
  done ) &
DW_PID=$!
trap 'watchdog_stop; kill "$DW_PID" 2>/dev/null || true' EXIT

# ---------------------------------------------------------------------------
# ---------------------------------------------------------------------------
# MEMORY: dp43's chunk buffers, not its layer array, are what overflow this machine.
# With the default CHUNKMB=16 the CHUNK-scaled allocations are
#   runbuf   KMAX*CHUNK*8                    = 2.00 GB
#   freelist (KMAX+QCAP+NTH+2)*CHUNK*8       = 2.38 GB   (nbuf = 142 buffers)
#   master slack  KMAX*CHUNK*8               = 2.00 GB
# ~6.4 GB of pure batching overhead. Measured on this 24 GB machine, L20 peaked at
# 26 GB phys_footprint and was killed; L21/L22 have larger arrays still. CHUNK only
# controls how records are grouped through the sort/merge, so the layer CONTENTS are
# identical at any setting — this trades merge passes (slower) for memory, and the
# 20 layers already banked at CHUNKMB=16 remain valid and resumable.
export CHUNKMB="${CHUNKMB:-2}"
echo "CHUNKMB=$CHUNKMB (default 16) — trims ~5.6 GB of chunk buffers off the peak"

banner "reproduce_paley43.sh — stages 0-4 (the package's own driver, unchanged)"
t0=$SECONDS
set +e
( cd sec7_paley43 && THREADS="$THREADS" ./reproduce_paley43.sh ) 2>&1 | tee "$SCRATCH/paley43.out"
rc=${PIPESTATUS[0]}
set -e
el=$((SECONDS - t0))
kill "$DW_PID" 2>/dev/null || true
echo
echo "driver exited $rc after $((el / 60))m $((el % 60))s"
metric wall_seconds "$el"
metric driver_exit "$rc"
[ -d "$PERSIST" ] && du -sh "$PERSIST" | awk '{print "peak layer tables on disk: " $1}'

out="$SCRATCH/paley43.out"
clean=$(sed $'s/\033\\[[0-9;]*m//g' "$out")

# ---------------------------------------------------------------------------
banner "claims"
eq() { [ "$1" = "$2" ] && echo aligned || echo divergent; }

# (1) MAS = 543 certified in both directions by the join over the delta<=2 shell
mas=$(grep -o 'certified MAS = [0-9]*' <<<"$clean" | tail -1 | awk '{print $NF}')
metric certified_mas "${mas:-none}"
claim "sec7.mas-exact" "MAS(Paley43) = 543 (certified both ways)" \
      "certified MAS = ${mas:-not reached}" "$(eq "${mas:-none}" 543)"

# (2) the census identity on the level-<=1 shell
orb=$(grep -o 'distinct_orbits=[0-9]*' <<<"$clean" | tail -1 | cut -d= -f2)
cens=$(grep -c 'delta<=1 reps complete + census-verified' <<<"$clean" || true)
metric delta1_orbits "${orb:-none}"
claim "sec7.level1-census" "1,841,303 delta<=1 orbits (x 903 = 1,662,696,609 orders)" \
      "${orb:-not reached} orbits$([ "$cens" = 1 ] && echo ', census identity enforced')" \
      "$(eq "${orb:-none}" 1841303)"

# (3) the delta=0 sanity pass and (4) the real level-<=1 screen
d0=$(grep '^RESULT ' <<<"$clean" | head -1)
d1=$(grep '^RESULT ' <<<"$clean" | tail -1)
f() { sed -n "s/.*[ ]$2=\([0-9-]*\).*/\1/p" <<<"$1"; }
d0_td=$(f "$d0" TRUE_DISJOINT)
d1_td=$(f "$d1" TRUE_DISJOINT); d1_mo=$(f "$d1" min_overlap)
d1_pairs=$(f "$d1" pairs_checked); d1_M=$(f "$d1" M); d1_K=$(f "$d1" K)
d1_dang=$(f "$d1" dangerous); d1_cand=$(f "$d1" rmask_cand_pairs)
metric delta0_true_disjoint "${d0_td:-none}"
metric delta1_true_disjoint "${d1_td:-none}"
metric delta1_min_overlap "${d1_mo:-none}"
metric delta1_pairs_checked "${d1_pairs:-none}"
metric delta1_distinct_rmasks "${d1_M:-none}"
metric delta1_dangerous_rmasks "${d1_dang:-none}"
metric delta1_dangerous_pool_orders "${d1_K:-none}"
metric delta1_candidate_rmask_pairs "${d1_cand:-none}"

claim "sec7.delta0-sanity" "TRUE_DISJOINT = 0 on the delta=0 pass" \
      "TRUE_DISJOINT = ${d0_td:-not reached}" "$(eq "${d0_td:-none}" 0)"
claim "sec7.level1-true-disjoint" "TRUE_DISJOINT = 0 on the full level-<=1 shell" \
      "TRUE_DISJOINT = ${d1_td:-not reached} over ${d1_pairs:-?} (rep, pool) pairs" \
      "$(eq "${d1_td:-none}" 0)"
claim "sec7.level1-screen-counts" "M = 4,709,640 rmasks, 5,092,111 candidate pairs, 678,686 dangerous, K = 347,694,990, 4,376,325,129 pairs checked" \
      "M = ${d1_M:-?}, ${d1_cand:-?} candidate pairs, ${d1_dang:-?} dangerous, K = ${d1_K:-?}, ${d1_pairs:-?} pairs checked" \
      "$(eq "${d1_pairs:-none}" 4376325129)"

proved=$(grep -c 'Paley(43) is NOT 5-realizable' <<<"$clean" || true)
claim "sec7.N5-upper-bound" "Paley(43) is not 5-realizable => N(5) <= 43" \
      "$([ "$proved" -ge 1 ] && echo 'PROVED banner reached' || echo 'not reached')" \
      "$(eq "$([ "$proved" -ge 1 ] && echo 1 || echo 0)" 1)"

# bank the canonicalised shell so a re-run need not redo canon_reps
[ -f sec7_paley43/delta1_reps.txt ] && cp sec7_paley43/delta1_reps.txt "$PERSIST/delta1_reps.txt"

banner "verdict"
ok=1
[ "$rc" = 0 ] || ok=0
for pair in "${mas:-none} 543" "${orb:-none} 1841303" "${d0_td:-none} 0" "${d1_td:-none} 0"; do
  set -- $pair; [ "$1" = "$2" ] || ok=0
done
[ "$proved" -ge 1 ] || ok=0
if [ "$ok" = 1 ]; then
  echo "S7-D OK: MAS = 543 certified, level-<=1 shell complete and census-verified,"
  echo "         TRUE_DISJOINT = 0 over the whole shell => Paley(43) is not 5-realizable => N(5) <= 43"
else
  echo "S7-D: the full-shell proof did not complete (driver exit $rc)" >&2
  grep -E 'FAIL|DISKWATCH|WATCHDOG:' <<<"$clean" | tail -5 >&2
  exit 1
fi
