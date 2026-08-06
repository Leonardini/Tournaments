#!/usr/bin/env bash
# =====================================================================================
# get_data.sh — download the external tournament catalogues this package reads.
#
# Source: Brendan McKay's digraph archive, https://users.cecs.anu.edu.au/~bdm/data/digraphs.html
# Files land in data/mckay/ under the names the scripts and READMEs use (McKay's own
# names are shorter: tourn9.txt -> tournaments9.txt, rt11.txt -> regulartournaments11.txt).
# Every download is verified against its exact expected byte size AND line count, so a
# truncated or mirrored-wrong file is caught here rather than halfway through a census.
#
# Usage:
#   ./get_data.sh                 default set: the n <= 9 catalogues + regular n = 11  (~7 MB)
#   ./get_data.sh n10             McKay's order-10 catalogue (37 MB download -> 447 MB on disk)
#   ./get_data.sh selfconverse11  the 279,968 self-converse 11-vertex tournaments (15 MB)
#   ./get_data.sh all             everything (~470 MB on disk)
#   ./get_data.sh --list          show the table and what reads each file; download nothing
#   ./get_data.sh --force <set>   re-download even if a verified copy is already there
#
# Destination override:  DATA_DIR=/somewhere ./get_data.sh
# =====================================================================================
cd "$(dirname "$0")" || exit 2
BASE="https://users.cecs.anu.edu.au/~bdm/data"
DEST="${DATA_DIR:-$PWD/data/mckay}"

if [ -t 1 ]; then G=$'\033[1;32m'; R=$'\033[1;31m'; Y=$'\033[1;33m'; C=$'\033[1;36m'; D=$'\033[2m'; Z=$'\033[0m'
else G=; R=; Y=; C=; D=; Z=; fi

# remote-file | local-name | bytes | lines | group | what reads it
CATALOGUES="
tourn3.txt|tournaments3.txt|8|2|quick|sec4 hs3fas (FAS = HS3 census, n = 3)
tourn4.txt|tournaments4.txt|28|4|quick|sec4 hs3fas (n = 4)
tourn5.txt|tournaments5.txt|132|12|quick|sec4 hs3fas (n = 5)
tourn6.txt|tournaments6.txt|896|56|quick|sec4 hs3fas (n = 6)
tourn7.txt|tournaments7.txt|10032|456|quick|sec4 hs3fas (n = 7)
tourn8.txt|tournaments8.txt|199520|6880|quick|sec4 hs3fas (n = 8)
tourn9.txt|tournaments9.txt|7086832|191536|quick|sec4 hs3fas (n = 9); sec6 triple-local CSP demo
rt11.txt|regulartournaments11.txt|68488|1223|quick|sec5 regular n = 11 census (the .RData twin is committed)
tourn10.txt.gz|tournaments10.txt|447720576|9733056|n10|sec4 Theorem 4.1 (n = 10); sec5 n = 10 census; sec6 ilp10
selfcontourn11.txt|selfconversetournaments11.txt|15678208|279968|selfconverse11|sec4 the six self-converse violators (Figure 4)
"

want_group() {   # want_group <group-of-row>
  case "$SET" in
    all) return 0 ;;
    quick) [ "$1" = quick ] ;;
    *) [ "$1" = "$SET" ] ;;
  esac
}

FORCE=0; SET=quick; LIST=0
while [ $# -gt 0 ]; do
  case "$1" in
    --force) FORCE=1 ;;
    --list) LIST=1 ;;
    --help|-h) sed -n '2,22p' "$0"; exit 0 ;;
    quick|n10|selfconverse11|all) SET="$1" ;;
    *) echo "unknown argument: $1  (try --help)" >&2; exit 2 ;;
  esac
  shift
done

if [ "$LIST" = 1 ]; then
  printf "${C}McKay catalogues${Z}  ${D}source: %s${Z}\n\n" "$BASE/digraphs.html"
  printf "  %-32s %12s %10s  %-15s %s\n" "local name (data/mckay/)" "bytes" "lines" "set" "read by"
  printf '%s\n' "$CATALOGUES" | while IFS='|' read -r rf lf b l g u; do
    [ -z "$rf" ] && continue
    here=""; [ -s "$DEST/$lf" ] && here="${G} [present]${Z}"
    printf "  %-32s %12s %10s  %-15s %s%s\n" "$lf" "$b" "$l" "$g" "$u" "$here"
  done
  printf "\n${D}sets: quick (default, ~7 MB) | n10 (447 MB) | selfconverse11 (15 MB) | all${Z}\n"
  exit 0
fi

fetch() {   # fetch <url> <outfile>
  local meter=-sS                      # piped/redirected: no progress bar, just errors
  [ -t 1 ] && meter=-#                 # a real terminal: curl's one-line progress bar
  if command -v curl >/dev/null 2>&1; then
    curl -fL --retry 3 --connect-timeout 30 "$meter" -o "$2" "$1"
  elif command -v wget >/dev/null 2>&1; then
    wget -q --show-progress -O "$2" "$1"
  else
    echo "need curl or wget" >&2; return 1
  fi
}

filesize() { [ -f "$1" ] && (stat -f%z "$1" 2>/dev/null || stat -c%s "$1" 2>/dev/null) || echo 0; }

mkdir -p "$DEST" || exit 2
printf "${C}Downloading into${Z} %s\n" "$DEST"

# Disk-space guard for the big one.
if [ "$SET" = n10 ] || [ "$SET" = all ]; then
  avail=$(df -k "$DEST" | tail -1 | awk '{print $4}')
  if [ -n "$avail" ] && [ "$avail" -lt 550000 ]; then
    printf "${R}not enough free disk${Z}: %s MB available, the order-10 catalogue needs ~490 MB (download + decompressed)\n" \
           "$((avail/1024))"; exit 1
  fi
fi

OK=0; FAIL=0; SKIP=0
while IFS='|' read -r rf lf bytes lines group used; do
  [ -z "$rf" ] && continue
  want_group "$group" || continue
  out="$DEST/$lf"

  if [ "$FORCE" = 0 ] && [ "$(filesize "$out")" = "$bytes" ]; then
    printf "  ${G}ok  ${Z} %-32s ${D}already present and the right size${Z}\n" "$lf"
    OK=$((OK+1)); continue
  fi

  case "$rf" in
    *.gz) printf "  ${C}get ${Z} %-32s ${D}%s (compressed; expands to %s bytes)${Z}\n" "$lf" "$rf" "$bytes" ;;
    *)    printf "  ${C}get ${Z} %-32s ${D}%s (%s bytes)${Z}\n" "$lf" "$rf" "$bytes" ;;
  esac

  tmp="$out.part"
  if ! fetch "$BASE/$rf" "$tmp"; then
    printf "  ${R}FAIL${Z} %-32s download failed (%s)\n" "$lf" "$BASE/$rf"; rm -f "$tmp"; FAIL=$((FAIL+1)); continue
  fi
  case "$rf" in
    *.gz) printf "       decompressing (this takes a moment for the big ones)...\n"
          mv "$tmp" "$tmp.gz"
          if ! gunzip -f "$tmp.gz"; then
            printf "  ${R}FAIL${Z} %-32s gunzip failed\n" "$lf"; rm -f "$tmp.gz" "$tmp"; FAIL=$((FAIL+1)); continue
          fi ;;
  esac

  # --- verification: exact size, exact line count, structural sanity -----------------
  got=$(filesize "$tmp")
  if [ "$got" != "$bytes" ]; then
    printf "  ${R}FAIL${Z} %-32s size %s, expected %s — left at %s\n" "$lf" "$got" "$bytes" "$tmp"
    FAIL=$((FAIL+1)); continue
  fi
  printf "       verifying %s lines...\n" "$lines"
  gotl=$(wc -l < "$tmp" | tr -d ' ')
  if [ "$gotl" != "$lines" ]; then
    printf "  ${R}FAIL${Z} %-32s %s lines, expected %s — left at %s\n" "$lf" "$gotl" "$lines" "$tmp"
    FAIL=$((FAIL+1)); continue
  fi
  bad=$(head -1 "$tmp" | tr -d '01\n' | wc -c | tr -d ' ')
  if [ "$bad" != 0 ]; then
    printf "  ${R}FAIL${Z} %-32s first line is not a 0/1 bit string — left at %s\n" "$lf" "$tmp"
    FAIL=$((FAIL+1)); continue
  fi
  mv "$tmp" "$out"
  printf "  ${G}ok  ${Z} %-32s ${D}verified: %s bytes, %s tournaments${Z}\n" "$lf" "$bytes" "$lines"
  OK=$((OK+1))
done <<EOF
$CATALOGUES
EOF

echo
if [ "$FAIL" -eq 0 ]; then
  printf "${G}DATA OK${Z} — %d file(s) in %s\n" "$OK" "$DEST"
  cat <<'USAGE'

How the scripts read them (paths are relative to each section folder):

  sec4:  cc -O3 -o hs3fas hs3fas.c && ./hs3fas ../data/mckay/tournaments10.txt 10
  sec5:  Rscript n10_prefilter.R ../data/mckay/tournaments10.txt cand.idx 0
  sec6:  Rscript ilp10/make_chunks10.R ../data/mckay/tournaments10.txt 10 <outdir> 200

Not downloaded here: nauty's `gentourng` (generates catalogues on the fly for the n = 11
census) — install it with `brew install nauty` or `apt-get install nauty`.
USAGE
  [ "$SET" = quick ] && printf "\n${D}The order-10 catalogue is a separate, larger download: ./get_data.sh n10${Z}\n"
  exit 0
else
  printf "${R}%d download(s) failed${Z}, %d ok. Re-run to retry (verified files are not re-fetched).\n" "$FAIL" "$OK"
  exit 1
fi
