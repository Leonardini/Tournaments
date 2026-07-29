#!/usr/bin/env python3
# extract_gidx_inm.py TOURN45 GIDX_SORTED OUT_PREFIX
#   Emits, aligned line-for-line: OUT_PREFIX.inm  (10 space-separated n=10 in-neighbour bitmasks per line,
#   the format alpha_fast reads) and OUT_PREFIX.gidx (the global catalogue index per line). Two-pointer
#   merge over ascending GIDX_SORTED, single streaming pass of TOURN45.
import sys
TOURN, GIDX, PRE = sys.argv[1], sys.argv[2], sys.argv[3]
n = 10
UP = [(i, j) for i in range(n) for j in range(i + 1, n)]
finm = open(PRE + ".inm", "w"); fg = open(PRE + ".gidx", "w")
with open(GIDX) as gf:
    line = gf.readline(); ptr = int(line) if line else None
    written = 0
    with open(TOURN) as tf:
        for li, row in enumerate(tf):
            if ptr is None: break
            if li < ptr: continue
            b = [ord(ch) - 48 for ch in row.rstrip("\n")]
            A = [[0] * n for _ in range(n)]
            for kk, (i, j) in enumerate(UP):
                A[i][j] = b[kk]; A[j][i] = 1 - b[kk]
            inm = [sum((1 << u) for u in range(n) if A[u][v] == 1) for v in range(n)]
            finm.write(" ".join(map(str, inm)) + "\n"); fg.write(f"{li}\n"); written += 1
            line = gf.readline(); ptr = int(line) if line else None
finm.close(); fg.close()
print(f"extracted {written} tournaments -> {PRE}.inm / {PRE}.gidx")
