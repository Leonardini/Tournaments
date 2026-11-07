# Section 4 — Conjecture 2: FAS = HS₃ on 3-inducible tournaments  (`sec4_fas_hs3/`)

**What it does.** Backs the Section 4 claims about when the minimum feedback arc set (FAS)
equals the minimum 3-cycle hitting set (HS₃). `hs3fas.c` establishes **Theorem 4.1**
by exhaustively checking, over a McKay tournament catalogue, that FAS = HS₃ for every
tournament on n ≤ 10 vertices (FAS via an exact Held–Karp maximum-acyclic-subgraph DP,
HS₃ via exact branch-and-bound). The two R scripts regenerate the paper's figures for
the n = 11 counterexamples where the equality first fails: `make_tstar_figs.R` for the
regular tournament T\* (Counterexample 4.2 / Figure 3, FAS = 17 > 16 = HS₃), and
`make_conj2_cex_figs.R` for the six 3-inducible self-converse violators (Figure 4). Both
R scripts re-verify every numeric claim before drawing and halt on any mismatch.
`reg11_fas_hs3.sh` backs the sentence after Counterexample 4.2: FAS = HS₃ holds for every
regular tournament on 11 vertices except T\*, which happens to be 3-inducible; among the
1,223 regular tournaments on 11 vertices, 48 of them 3-inducible, T\* is the only one with
HS₃ < FAS.

**Files.**
- `hs3fas.c` — exhaustive FAS == HS₃ census over a McKay catalogue (Theorem 4.1).
- `make_tstar_figs.R` — rebuilds the T\* figures (Counterexample 4.2 / Figure 3), re-checking FAS = 17 and HS₃ = 16.
- `make_conj2_cex_figs.R` — rebuilds the six self-converse violator figures (Figure 4), re-checking self-converse and HS₃ < FAS.
- `tstar_voters.R` — the three voters of T\* and the majority-tournament function; `source`d by `make_tstar_figs.R` and `reg11_catalogue.R`, so both use the same T\*.
- `reg11_fas_hs3.sh` — FAS versus HS₃ on all 1,223 regular tournaments on 11 vertices, split by 3-inducibility. It runs the three files below.
- `reg11_catalogue.R` — reads `../data/regulartournaments11.RData`, checks that every entry is a regular tournament and that no two are isomorphic, finds the one entry isomorphic to T\*, and writes the catalogue as bit strings for the C engines.
- `reg11_fas_hs3.py` — computes, for every entry, FAS (Held–Karp), HS₃ (the 0/1 integer program min Σ x_a subject to x_a + x_b + x_c ≥ 1 for every directed 3-cycle, solved to proven optimality by OR-Tools CP-SAT) and 3-inducibility (CP-SAT over three linear orders); requires them to agree with `hs3fas.c` and `../appendices/margin1_scan.c` on every entry; and checks the paper's counts.

**Dependencies.** C compiled with `cc -O3`; R with `igraph` and `lpSolve`; Python 3 with
`ortools` for `reg11_fas_hs3.py`. Versions and
installation are in the [top-level README](../README.md#environment). **None require
CPLEX** (the FAS = HS₃ census runs with only a C compiler and free solvers). `hs3fas.c`
reads an external **McKay tournament catalogue** — a plain-text file with one tournament
per line, each line a bit string of length C = n(n−1)/2 (the tournament's triangle of
arc directions). Get them with `./get_data.sh all` from the repo root; they land in
`data/mckay/`, verified against their expected size and tournament count. The R figure scripts
need no external data (the tournaments are hard-coded from their Appendix C inducing
profiles), and `reg11_fas_hs3.sh` reads only the committed `../data/regulartournaments11.RData`.

**How to run.**
```sh
# 0. once, from the repo root: fetch the catalogues (n <= 9 are ~7 MB; n = 10 is a 37 MB download)
#    ./get_data.sh && ./get_data.sh n10

# 1. hs3fas.c — exhaustive FAS == HS3 census (Theorem 4.1)
cc -O3 -o hs3fas hs3fas.c
# usage: ./hs3fas <catalogue.txt> <n>   (catalogue lines must have length n(n-1)/2)
./hs3fas ../data/mckay/tournaments10.txt 10        # the n = 10 McKay catalogue
#   repeat once per catalogue, e.g. ./hs3fas ../data/mckay/tournaments8.txt 8, ... up to n = 10

# 2. make_tstar_figs.R — Counterexample 4.2 / Figure 3 (takes no arguments)
Rscript make_tstar_figs.R           # writes PDFs to the current directory; run from this folder

# 3. make_conj2_cex_figs.R — the six self-converse violators / Figure 4 (takes no arguments)
Rscript make_conj2_cex_figs.R       # writes PDFs to the current directory; run from this folder

# 4. reg11_fas_hs3.sh — FAS vs HS3 on the 1,223 regular 11-vertex tournaments (takes no arguments)
./reg11_fas_hs3.sh                  # WORKERS=1..4 sets the number of processes (default 4)
```

**What to expect.**

- **`hs3fas.c`** — runtime depends on the catalogue size (number of tournaments, which
  grows sharply with n): small catalogues (n ≤ 8) finish in seconds; the full n = 10
  catalogue (≈ 9.7 million tournaments) is the longest, about **2 minutes** on one core
  of a laptop (measured: 113 s, Apple clang, `-O3`). It reports progress on stderr while
  it runs — a live counter on a terminal, a line every 15 s when redirected to a file
  (`PROGRESS=0` silences it) — so a long catalogue is visibly progressing:
  `hs3fas n=10: 5185111/9733056 tournaments (53.3%), 0 with HS3<FAS, 0 hard  60s`.
  Prints a final summary line on stdout, e.g.
  `n=10: 9733056 tournaments; 0 with HS3<FAS; 0 HARD (unresolved) => minFAS == for ALL minHS3`.
  For Theorem 4.1 the mismatch and HARD counts are both 0, giving the `== for ALL`
  verdict. Any refutation prints up to 20 lines like
  `MISMATCH idx <k>: FAS=<f> HS3=<h>  bits=<line>`; any branch-and-bound blow-up prints
  up to 20 `HARD idx <k> (B&B node limit, FAS=<f>): bits=<line>` lines (the node limit is
  20,000,000). Writes no files (all output to stdout).

- **`make_tstar_figs.R`** — a few seconds. Prints
  `FAS check: witness order leaves 17 arcs backward`, `cyclic triangles: <count>`, and
  `HS check: minimum 3-cycle hitting set has 16 arcs`, then `Tstar_HS.pdf written` and
  `Tstar_FAS.pdf written`. Writes `Tstar_HS.pdf` and `Tstar_FAS.pdf` to the working
  directory. Guarded by `stopifnot`: it aborts if T\* is not regular (out-degree 5), if
  the witness order does not leave exactly 17 backward arcs, or if the exact minimum
  3-cycle hitting set is not 16.

- **`make_conj2_cex_figs.R`** — a few seconds (six exact Held–Karp DPs over 2¹¹
  subsets). For each of A–F prints, e.g.,
  `Counterexample A: self-converse OK, HS3 = <h> < <f> = FAS` followed by
  `CounterexampleA.pdf written`. Writes `CounterexampleA.pdf` … `CounterexampleF.pdf` to
  the working directory. Guarded by `stopifnot`: it aborts if any tournament is not
  self-converse (`vf2` isomorphism to its converse) or fails HS₃ < FAS.

- **`reg11_fas_hs3.sh`** — about 25 s on 4 cores of a laptop (measured: 24 s), about 0.5 GB
  in all. It writes nothing to this folder: the binaries and intermediate files go to a
  temporary directory that is removed on exit. It prints
  `1223 regular tournaments on 11 vertices, pairwise non-isomorphic`,
  `T* = catalogue entry 902`, the summary lines of `margin1_scan.c` and `hs3fas.c`
  (`MISMATCH idx 902: FAS=17 HS3=16 …`), progress on stderr, and then the outcome for each
  class:

  ```
  3-inducible: 48 tournaments; (FAS, HS3) -> count {(15, 15): 1, (16, 16): 1, (17, 16): 1, (17, 17): 22, (18, 18): 23}; HS3 < FAS at entries [902]
  not 3-inducible: 1175 tournaments; (FAS, HS3) -> count {(16, 16): 14, (17, 17): 278, (18, 18): 827, (19, 19): 55, (20, 20): 1}; HS3 < FAS at entries []
  CONFIRMED: of the 1223 regular tournaments on 11 vertices, 48 are 3-inducible, and HS3 < FAS only for T* (entry 902, FAS = 17, HS3 = 16), which is 3-inducible
  ```

  Entries are numbered from 1 in catalogue order. The script stops with an error, and
  prints no `CONFIRMED` line, if the catalogue is not 1,223 pairwise non-isomorphic regular
  tournaments, if T\* is not in it exactly once, if a solver fails to prove optimality, if
  the two engines disagree on FAS, HS₃ or 3-inducibility of any entry, or if the counts
  differ from the paper's (1,223 regular, 48 of them 3-inducible, exactly one with HS₃ < FAS,
  and that one T\*).
