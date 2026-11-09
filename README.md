# Tournaments not inducible by three voters — reproducibility package

Code for the paper *Tournaments not inducible by three voters*
(L. Chindelevitch and A. Harutyunyan). Every computational claim in the paper has a verifier here,
organized by section, with a claim → tool manifest further down.

On 2026-11-07 the two papers were re-split: this one now treats three voters, and the five-voter
results it used to contain (the counting bounds on N(k), the proof that Paley(43) is not 5-inducible,
the census of the 11-vertex tournaments and the unit-margin five-voter profiles) moved to the companion
paper, with their code, to its package
[TournamentsBeyond5Voters](https://github.com/Leonardini/TournamentsBeyond5Voters). So did the
independent reproduction of the Paley(43) proof (its `REPRODUCTION.md`, report and notebook); the
reproduction's experiment branches (`orx/*`) remain in this repository.

## Getting started

```sh
git clone https://github.com/Leonardini/Tournaments.git && cd Tournaments
uv sync                        # Python env, exact versions, from uv.lock  (or: pip install -r requirements.txt)
Rscript install_r_packages.R   # the four R packages the checks need
./check_env.sh                 # what is installed, what is missing, and the command that fixes it
./check_all.sh                 # ~1-2 min: PASS / FAIL for every section
```

Run `./check_env.sh` before `./check_all.sh`: a check whose tools are absent is reported as
**SKIP**, never as FAIL, and `check_env.sh` is where you see *why*. Long steps print progress on
stderr as they go (`PROGRESS=0` silences it), so a slow stage is visibly running rather than hung.
[`uv`](https://docs.astral.sh/uv/) is optional but recommended — one command, no manual venv.

Two ways in:

- **Check the results fast** — from the repo root, `./check_all.sh` (~1–2 min) runs a quick
  "check the result" step for every section and reports PASS / FAIL. Free tools only: no HPC, no
  downloads, no CPLEX.
- **Rerun a census** — each section's README gives the full computation behind its claims, with the
  catalogues it reads (see *Data policy*).

The package is source code plus a few small data files.
Large data — McKay's tournament catalogues — is not checked in; the scripts regenerate it or download it (see *Data policy*).
Most claims are cross-checked by two independent engines (e.g. CPLEX *and* OR-Tools CP-SAT, or an ILP
*and* a solver-free check), and every reported optimum is re-verified in exact rational arithmetic.

## Environment

You need a **C compiler**, **R**, and **Python 3**. No script needs all of it — each says what it
uses, and `./check_env.sh` reports exactly what is present on your machine.

| | needed for | install |
|---|---|---|
| **C** (`cc -O3`) | the census and constraint-search engines | preinstalled (`clang` on macOS, `gcc` on Linux) |
| **Python 3** — `ortools` | the CP-SAT checks | `uv sync`, or `pip install -r requirements.txt` |
| **R** — `igraph`, `lpSolve`, `rcdd`, `gmp` | exact α\*, the certificates, every figure | `Rscript install_r_packages.R` |
| system libraries — GMP, MPFR | `gmp` and `rcdd` build against them | `brew install gmp mpfr` / `apt-get install libgmp-dev libmpfr-dev` |

Optional, and only for specific extras — `./check_all.sh` needs none of them:

- [GLPK](https://www.gnu.org/software/glpk/) — `sec5_a3_boundary/alpha_fast.c`, the n = 10 census
  pre-filter (`brew install glpk` / `apt-get install libglpk-dev`).
- [nauty](https://pallini.di.uniroma1.it/) `gentourng` — whole-catalogue scans
  (`brew install nauty` / `apt-get install nauty`; the upstream tarball is also fine).
- [cddlib](https://github.com/cddlib/cddlib) and GMP, under the Python package `pycddlib` — regenerating
  the obstacle catalogue at n = 9 (`brew install cddlib gmp`, then `uv sync --extra obstacles`).
- The R extras `combinat`, `slam`, `Matrix`, `pracma`, `tidyverse` … cover incidental helpers in
  `appendices/`: `Rscript install_r_packages.R --all`.

Two notes on how little is really required: the obstacle checker
`appendices/obstacle_catalogue/verify_catalogue.py` needs **only the Python standard library**, and
`appendices/hk_oracle.c` is an `#include`d oracle rather than a standalone program.

**Data** — McKay's digraph catalogues, fetched and verified by `./get_data.sh` (see *Data policy*).

**CPLEX is optional** (see below); `cplexAPI` / `Rcplex` and `docplex` / `cplex` are used only by the
handful of CPLEX scripts.

### CPLEX (optional)

**No headline result needs it.** FAS = HS₃ and cA3's non-3-inducibility run with just a C compiler
and/or free solvers (OR-Tools CP-SAT, `lpSolve`, GLPK). Only these scripts use IBM CPLEX
22.1 — and the reproducibility ones each have a free twin:

| CPLEX script | free twin |
|---|---|
| `sec5_a3_boundary/reg11_realize3.py` | `independent_realize3_cpsat.py` |
| `sec5_a3_boundary/n10_realize3.py` | `cpsat_realize3_n10.py` |
| `appendices/{k_realizability_lp.R, minimum_set_cover.R}` | — (appendix computations only) |

To run the CPLEX scripts, install **IBM ILOG CPLEX Optimization Studio 22.1** (free for academics via
the [IBM Academic Initiative](https://www.ibm.com/academic)), then add the bindings:

- **Python:** `python <cplex-studio>/python/setup.py install` — the full library; the
  `pip install cplex` community edition caps models at 1000 variables.
- **R:** `install.packages("Rcplex", configure.args="--with-cplex-dir=<cplex-studio>/cplex")`;
  `cplexAPI` (CRAN archive) builds the same way.

## Manifest — claim → verifier

The theorem that every minimum FAS is a minimal 3-cycle hitting set and the symmetrization lemma are
analytic and need no computation. Everything below does.

### Refuting Conjecture 1 of Milosz–Hamel–Pierrot (`sec3_mhp/`)

| claim | tool |
|---|---|
| Counterexamples 3.1 (m = 7, 9) and 3.2 (m = 5, n = 6): FAS > HS₃, with the minimum-weight FAS found by brute force and the margins verified | `make_family_and_mhp_figs.R` — self-checking; **stops on any mismatch** before plotting |

### Refuting Conjecture 2: FAS = HS₃ on 3-inducible tournaments (`sec4_fas_hs3/`)

| claim | tool |
|---|---|
| Theorem 4.1: FAS = HS₃ for **every** tournament on n ≤ 10 (exhaustive) | `hs3fas.c` — Held–Karp MAS + exact minimum 3-cycle hitting set over a McKay catalogue |
| Counterexample 4.2: regular T\* on 11 vertices with FAS = 17 > 16 = HS₃ | `make_tstar_figs.R` — self-checks FAS = 17 and HS₃ = 16 (lpSolve) |
| FAS = HS₃ for every regular tournament on 11 vertices except T\*: among the 1,223 regular tournaments on 11 vertices, 48 of them 3-inducible, T\* is the only one with HS₃ < FAS | `reg11_fas_hs3.sh` — FAS, HS₃ and 3-inducibility of every entry, each by two exact engines; stops unless the counts are 1,223 / 48 / 1 and the one is T\* |
| The six 3-inducible self-converse violators (Figure 4) | `make_conj2_cex_figs.R` — re-checks self-converse and HS₃ < FAS |

### The A(3) threshold fails on the boundary (`sec5_a3_boundary/`)

cA3 is the code's **ce1068**: the Z₁₁ circulant with connection set {1, 2, 3, 4, 6}.

| claim | tool |
|---|---|
| cA3 structure and exact α\* = 2/3 (rational, `rcdd`/GMP) | `verify_ce1068.R`, `analyze_ce1068.R`, `inmask_alpha.R` |
| cA3 not 3-inducible — three independent methods | `reg11_realize3.py` (CPLEX), `independent_realize3_cpsat.py` (CP-SAT), `realize3_partition.c` (solver-free) |
| 6-order 2/3-certificate (its minimality is proved by hand in the paper) | `make_cA3_fig.R` (re-checks the certificate before drawing) |
| cA3 is 5-inducible; vertex-criticality | `realize_and_delete_ce1068.py` |
| regular n = 11 census (1,223) isolating cA3 | `reg11_alphastar.R`, `reg11_realize3.py` |
| n = 10 census (9,733,056 → 1,013 counterexamples) | `n10_prefilter.R`, `extract_gidx_inm.py`, `alpha_fast.c`, `n10_realize3.py`, `cpsat_realize3_n10.py`, `batch_verify_alpha_n10.R`, `characterize_n10_ce.R` |
| cA6 (needs **9** voters); the 6-vs-9-voter dichotomy | `cert9.c` |
| forced-arc reversal counterexamples at n = 10 (Figure D.2) | `make_reversal_cex_figs.R` |

### Obstacles at every order (`obstacle_family/`)

| claim | tool |
|---|---|
| The value (2n − 3)/(3n − 4) for the completions of the paper's previous version (Theorem 7.2 now uses other completions; see `obstacle_family/README.md`) | `lean/` — a Lean 4 proof (Mathlib), for every n; build and axiom check in its README |
| The figure of G₁₀ and H₁₁ with their arc classes | `make_family_section_figs.R` (checks arc counts, the Eulerian property and that no arc is drawn through a vertex before drawing) |

### Appendices — shared engines and appendix-specific tools (`appendices/`)

| appendix | tool |
|---|---|
| the predictability LP α\* (column generation, exact MAS oracle as separator); obstacle duals | `k_realizability_lp.R` |
| minimum set cover of obstacle classes | `minimum_set_cover.R` |
| The catalogue of minimal obstacles at n = 9 (all minimal supports, exactly; α\* of all 17,674), its minimum covers, and drawings of the two containment covers | `obstacle_catalogue/` (its own README) |
| The figure of G₈ and H₉ (H₉ is class `O02` of the catalogue; each checked to be Eulerian with 3n − 4 arcs before drawing) | `../sec3_mhp/make_family_and_mhp_figs.R` |
| exact weighted MAS: Held–Karp oracle (n ≤ 16) | `hk_oracle.c` |
| 3-inducibility as a labelling of the vertex triples, the engine of the census table (~20 µs/tournament) | `margin1_scan.c` |
| forced-arc reversal dichotomy | `reversal_check.c` |

## Data policy

No large data is committed — the scripts read McKay catalogues you download. One small input is the
exception, kept in the repo: `data/regulartournaments11.RData` (40 KB, the 1,223 regular 11-vertex
tournaments that `sec4_fas_hs3/reg11_fas_hs3.sh` and the cA3 scripts read).

`appendices/obstacle_catalogue/n9_minimal_obstacles.tsv` (15 KB) is the catalogue of minimal obstacles
at n = 9: the 59 isomorphism classes of inclusion-minimal supports of optimal duals of the predictability
LP, over all 17,674 non-3-inducible 9-tournaments. The scripts in that folder recompute it exactly, with
the signed classes of the 254 tournaments that are 3-inducible but not with unit margin
(`n9_signed_obstacles_254.tsv`); their inputs, the three tournament lists (1.6 MB), are kept there too. `O01`–`O40` come from the 1,054 tournaments that do not contain
`G8`; `G8` is the only minimal obstacle of the 16,263 that contain it and have α\* = 13/20; `O41`–`O58`
come from the other 357, whose α\* is 64/99, 11/17 or 24/37 (`O41` is the 64/99 dual of Shepardson and
Tovey 2009). One row per class. `arclist` gives the obstacle as a multidigraph, `u>v:m` meaning arc
u → v with multiplicity m; the dual weight of an arc is its multiplicity divided by `total_mult`.
`converse` names the class of the reversed obstacle, `n_supports` and `n_tournaments` count its minimal
supports and the tournaments that carry one (`n_supports` of `G8` counts its copies), `degseq` lists
out/in degrees, and `source` says which collection the class comes from (`1054` or `16620`).

**`./get_data.sh` downloads the catalogues for you**, into `data/mckay/` under the names the scripts
expect, checking each one against its exact expected byte count *and* line count — so a truncated
download is caught here rather than halfway through a census.

```sh
./get_data.sh --list       # the table: file, size, tournament count, and what reads it
./get_data.sh              # default set: the n <= 9 catalogues + regular n = 11   (~7 MB)
./get_data.sh n10          # McKay's order-10 catalogue: 37 MB download -> 447 MB on disk
./get_data.sh all          # everything (~470 MB on disk)
```

Nothing in `./check_all.sh` needs any of it; the downloads are for the full censuses
(`hs3fas` at n = 10 and the sec5 n = 10 census). Source and provenance:
Brendan McKay's digraph archive, <https://users.cecs.anu.edu.au/~bdm/data/digraphs.html>.

## Layout

```
sec3_mhp/          MHP Conjecture 1 counterexamples
sec4_fas_hs3/      MHP Conjecture 2 (FAS = HS₃): n ≤ 10 census, T*, regular n = 11
sec5_a3_boundary/  A(3) threshold on the boundary: cA3, censuses, cA6
obstacle_family/   obstacles at every order: the Lean proof of the family's value, its figure
appendices/        shared engines + appendix-specific tools
common/  data/     shared α* oracle and progress helper; the few committed data inputs

check_env.sh          is this machine ready? (never runs a check — only reports)
check_all.sh          the quick PASS/FAIL verification of every section  (-v to stream output)
get_data.sh           download + verify McKay's catalogues into data/mckay/
pyproject.toml        Python environment: uv.lock pins exact versions   (uv sync)
requirements.txt      the same dependencies for plain pip
install_r_packages.R  the R side of the environment
```
