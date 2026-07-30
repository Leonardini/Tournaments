#!/usr/bin/env bash
# =====================================================================================
# S7-C — the screen's soundness controls, and the min_overlap divergence.
#                                                            [HEADLINE LINE, step 3]
#
# S7-B reproduced TRUE_DISJOINT = 0 over the complete level-0 shell but read
# min_overlap = 71 where Appendix A.4 reports 68. Three controls run here; the second
# is a direct test of why.
#
#  1. POSITIVE-DETECTION CONTROL (DBTEST=1). Replaces the full 3311-bit DB by the razor
#     triangles only. Then every razor-disjoint candidate is disjoint by construction, so
#     seedcount MUST equal checked. This is the negative control for the whole screen: it
#     proves the detection path fires and coverage is complete, so TRUE_DISJOINT = 0 means
#     "looked at every candidate and found none", not "never looked".
#     Appendix A.4 at level 0: 333,809 = 333,809.
#
#  2. AUT-REDUCTION-FREE CROSS-CHECK (POOLVSPOOL=1). Both sides range over the full
#     G-closed pool, dropping the factor-903 one-side reduction of §6.2 entirely, so
#     TRUE_DISJOINT = 0 is re-established without that lemma.
#     It also tests the min_overlap hypothesis. A zero overlap survives the reduction
#     (DB-overlap 0 => rmask-overlap 0, and §6.2 carries a zero through sigma), which is
#     why the CLAIM is unaffected. But razor-disjointness itself is NOT G-invariant —
#     sigma permutes triangles, not W-internal triangles — so the pool-vs-pool candidate
#     set is strictly different, and a pair with overlap 68 can be a candidate here while
#     its Aut-reduced counterpart shares a razor triangle and is never scored.
#
#  3. G-INVARIANCE OF DB-OVERLAP (repro/verify_ginv.c, written for this reproduction).
#     The sole property the reduction rests on, re-derived from scratch and checked
#     exhaustively over all 903 sigma, plus the triangle orbit structure of Appendix A.4.
# =====================================================================================
source "$(dirname "$0")/env.sh"
cd "$REPRO_ROOT"

sysinfo
watchdog_start
trap watchdog_stop EXIT

banner "build"
cc -O3 -march=native -pthread -o "$SCRATCH/razor_screen" sec7_paley43/razor_screen.c
cc -O3 -march=native          -o "$SCRATCH/verify_ginv"  repro/verify_ginv.c
echo "built razor_screen, verify_ginv"

f() { sed -n "s/.*[ ]$2=\([0-9-]*\).*/\1/p" <<<"$1"; }
eq() { [ "$1" = "$2" ] && echo aligned || echo divergent; }

# ---------------------------------------------------------------------------
banner "1. positive-detection control (DBTEST=1) — must give seedcount == checked"
cd sec7_paley43
t0=$SECONDS
MCAP=300000 DBTEST=1 SEEDCAP=1 "$SCRATCH/razor_screen" d0_reps.txt 1 24 0 "$THREADS" 2>&1 | tee "$SCRATCH/dbtest.out"
dbt_s=$((SECONDS - t0))
cd "$REPRO_ROOT"
r1=$(grep '^RESULT ' "$SCRATCH/dbtest.out" | tail -1)
d_checked=$(f "$r1" pairs_checked)
d_seeds=$(grep -o 'TRUE-DISJOINT=[0-9]*' "$SCRATCH/dbtest.out" | tail -1 | cut -d= -f2)
metric dbtest_checked "$d_checked"; metric dbtest_seeds "$d_seeds"; metric dbtest_seconds "$dbt_s"
echo "  checked=$d_checked  seeds=$d_seeds"
claim "sec7.coverage-control" "seedcount == checked == 333809 at level 0" \
      "seeds=$d_seeds, checked=$d_checked" \
      "$([ "$d_seeds" = "$d_checked" ] && [ "$d_checked" = 333809 ] && echo aligned || echo divergent)"

# ---------------------------------------------------------------------------
banner "2. Aut-reduction-free cross-check (POOLVSPOOL=1)"
cd sec7_paley43
t0=$SECONDS
MCAP=300000 POOLVSPOOL=1 "$SCRATCH/razor_screen" d0_reps.txt 1 24 0 "$THREADS" 2>&1 | tee "$SCRATCH/pvp.out"
pvp_s=$((SECONDS - t0))
cd "$REPRO_ROOT"
r2=$(grep '^RESULT ' "$SCRATCH/pvp.out" | tail -1)
p_checked=$(f "$r2" pairs_checked); p_td=$(f "$r2" TRUE_DISJOINT); p_mo=$(f "$r2" min_overlap)
metric poolvspool_pairs_checked "$p_checked"
metric poolvspool_true_disjoint "$p_td"
metric poolvspool_min_overlap "$p_mo"
metric poolvspool_seconds "$pvp_s"
echo "  pairs_checked=$p_checked  TRUE_DISJOINT=$p_td  min_overlap=$p_mo"
claim "sec7.autfree-true-disjoint" "TRUE_DISJOINT = 0 without the Aut reduction" \
      "TRUE_DISJOINT = $p_td over $p_checked full-pool pairs" "$(eq "$p_td" 0)"
claim "sec7.min-overlap-source" "min overlap = 68 (Appendix A.4)" \
      "Aut-reduced 71 (S7-B) vs pool-vs-pool $p_mo" "$(eq "$p_mo" 68)"

banner "min_overlap by mode"
printf '  %-28s %s\n' "Aut-reduced (S7-B)" "71"
printf '  %-28s %s\n' "pool-vs-pool (this node)" "$p_mo"
printf '  %-28s %s\n' "paper, Appendix A.4" "68"
if [ "$p_mo" = 68 ]; then
  echo "  => the published 68 is the pool-vs-pool figure. The two modes screen different"
  echo "     candidate sets because razor-disjointness is not G-invariant; both give"
  echo "     TRUE_DISJOINT = 0, so the claim is unaffected either way."
else
  echo "  => pool-vs-pool does not explain the 68 either; min_overlap remains unresolved."
  echo "     TRUE_DISJOINT = 0 reproduces in both modes, so the claim is unaffected."
fi

# ---------------------------------------------------------------------------
banner "3. G-invariance of DB-overlap + triangle orbit structure"
"$SCRATCH/verify_ginv" sec7_paley43/d0_reps.txt 60 2>&1 | tee "$SCRATCH/ginv.out"
gi=$(grep -c 'verify_ginv: ALL CHECKS PASSED' "$SCRATCH/ginv.out" || true)
viol=$(sed -n 's/.*violations: \([0-9]*\).*/\1/p' "$SCRATCH/ginv.out" | tail -1)
comb=$(sed -n 's/.*combinations tested: \([0-9]*\).*/\1/p' "$SCRATCH/ginv.out" | tail -1)
metric ginv_combinations_tested "$comb"; metric ginv_violations "$viol"
claim "sec7.triangle-orbits" "5 orbits of sizes 903,903,903,301,301; 602 triangles with nontrivial stabiliser" \
      "$([ "$gi" = 1 ] && echo 'exact match' || echo 'not confirmed')" \
      "$([ "$gi" = 1 ] && echo aligned || echo divergent)"
claim "sec7.g-invariance" "DB-overlap size is G-invariant (checked over all 903 sigma)" \
      "$viol violations over $comb (sigma, pair) combinations" "$(eq "$viol" 0)"

banner "verdict"
ok=1
[ "$d_seeds" = "$d_checked" ] && [ "$d_checked" = 333809 ] || ok=0
[ "$p_td" = 0 ] || ok=0
[ "$gi" = 1 ] || ok=0
echo "coverage control ${dbt_s}s | pool-vs-pool ${pvp_s}s | G-invariance OK=$gi"
[ "$ok" = 1 ] || { echo "S7-C: a soundness control did not reproduce" >&2; exit 1; }
echo "S7-C OK: coverage complete, TRUE_DISJOINT=0 holds without the Aut reduction, G-invariance exact"
