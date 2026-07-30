#!/usr/bin/env bash
# =====================================================================================
# S4 — Theorem 4.1: FAS = HS3 for every tournament on n <= 10.
#
# The paper's §4 result: on every tournament with at most 10 vertices, the minimum
# feedback arc set equals the minimum hitting set of directed 3-cycles. (Theorem 2.1
# gives one inequality analytically; the census establishes equality exhaustively, and
# §4 then exhibits the first counterexamples at n = 11.)
#
# hs3fas.c computes both sides EXACTLY per tournament — FAS via a Held-Karp maximum-
# acyclic-subgraph DP over all 2^n vertex subsets, HS3 via branch-and-bound with a
# 20,000,000-node limit. A tournament with HS3 < FAS prints MISMATCH; a B&B blow-up
# prints HARD. Theorem 4.1 requires both counts to be 0 at every n.
#
# Full published scale, no downscaling: complete catalogues for every n from 3 to 10,
# 9,733,056 tournaments at n = 10 alone. Small n come from nauty gentourng; n = 9 and
# n = 10 use McKay's catalogues already on this machine. The two sources use opposite
# bit conventions for the arc triangle, which enumerate the same isomorphism classes up
# to converse — and FAS and HS3 are both converse-invariant, so the verdict is the same.
# =====================================================================================
source "$(dirname "$0")/env.sh"
cd "$REPRO_ROOT"

sysinfo
[ -x "$GENTOURNG" ] || { echo "gentourng not found at $GENTOURNG" >&2; exit 1; }
watchdog_start
trap watchdog_stop EXIT

banner "build"
cc -O3 -o "$SCRATCH/hs3fas" sec4_fas_hs3/hs3fas.c
echo "built hs3fas (exact Held-Karp MAS + exact minimum 3-cycle hitting set)"

# number of tournaments on n vertices up to isomorphism (OEIS A000568)
declare -a EXPECT=([3]=2 [4]=4 [5]=12 [6]=56 [7]=456 [8]=6880 [9]=191536 [10]=9733056)

banner "exhaustive FAS == HS3 census, n = 3..10"
tot_all=0; mism_all=0; hard_all=0; allok=1
for n in 3 4 5 6 7 8 9 10; do
  case $n in
    9)  cat="$MCKAY_DIR/tournaments9.txt";  src="McKay catalogue" ;;
    10) cat="$MCKAY_DIR/tournaments10.txt"; src="McKay catalogue" ;;
    *)  cat="$SCRATCH/t$n.txt"; src="gentourng"; "$GENTOURNG" -q $n 2>/dev/null > "$cat" ;;
  esac
  [ -s "$cat" ] || { echo "missing catalogue for n=$n ($cat)" >&2; exit 1; }
  t0=$SECONDS
  out=$("$SCRATCH/hs3fas" "$cat" $n)
  el=$((SECONDS - t0))
  echo "  [$src] $out   (${el}s)"

  cnt=$(sed -n "s/^n=$n: \([0-9]*\) tournaments.*/\1/p"        <<<"$out")
  mis=$(sed -n 's/.*; \([0-9]*\) with HS3<FAS.*/\1/p'          <<<"$out")
  hrd=$(sed -n 's/.*; \([0-9]*\) HARD .*/\1/p'                 <<<"$out")
  verd=$(grep -o 'minFAS == for ALL minHS3' <<<"$out" || true)

  metric "n${n}_tournaments" "$cnt"
  metric "n${n}_hs3_lt_fas"  "$mis"
  metric "n${n}_hard"        "$hrd"
  metric "n${n}_seconds"     "$el"

  ok=1
  [ "$cnt" = "${EXPECT[$n]}" ] || ok=0
  [ "$mis" = 0 ] || ok=0
  [ "$hrd" = 0 ] || ok=0
  [ -n "$verd" ] || ok=0
  [ "$ok" = 1 ] || allok=0
  claim "sec4.thm41-n$n" "${EXPECT[$n]} tournaments, 0 with HS3<FAS, 0 HARD" \
        "$cnt tournaments, $mis with HS3<FAS, $hrd HARD" \
        "$([ "$ok" = 1 ] && echo aligned || echo divergent)"
  tot_all=$((tot_all + cnt)); mism_all=$((mism_all + mis)); hard_all=$((hard_all + hrd))
  [ "$n" -le 8 ] && rm -f "$SCRATCH/t$n.txt"
done

banner "aggregate"
metric total_tournaments_n3_to_n10 "$tot_all"
metric total_hs3_lt_fas "$mism_all"
metric total_hard "$hard_all"
printf '  tournaments swept (n = 3..10): %d\n' "$tot_all"
printf '  with HS3 < FAS:                %d\n' "$mism_all"
printf '  unresolved (HARD):             %d\n' "$hard_all"
claim "sec4.theorem-4.1" "FAS = HS3 for every tournament on n <= 10 (exhaustive)" \
      "$tot_all tournaments checked, $mism_all with HS3 < FAS, $hard_all unresolved" \
      "$([ "$allok" = 1 ] && echo aligned || echo divergent)"

banner "verdict"
[ "$allok" = 1 ] || { echo "S4: Theorem 4.1 did not reproduce at some n" >&2; exit 1; }
echo "S4 OK: FAS == HS3 for all $tot_all tournaments on 3 <= n <= 10 — Theorem 4.1 reproduced at full scale"
