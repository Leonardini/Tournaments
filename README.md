> **Independent reproduction (2026-07-30).** Every computational claim in this package was
> re-run on a single laptop, including the Section 7 keystone end to end: the q=43 layer tables rebuilt
> from scratch, `MAS(Paley43) = 543` certified both ways, the level-≤1 shell enumerated and
> census-verified at 1,841,303 orbits, and `TRUE_DISJOINT = 0` over all 4,376,325,129 pairs —
> every published count exact. See **[REPRODUCTION.md](REPRODUCTION.md)** for the claim-by-claim
> table and experiment log, **[reports/paley43-five-voters/report.md](reports/paley43-five-voters/report.md)**
> for the illustrated write-up, and **[paley43_five_voters.py](paley43_five_voters.py)** for a
> tutorial notebook.
>
> *Note for anyone rebuilding Section 7 on a machine with under ~32 GB of RAM:* run
> `CHUNKMB=2 ./reproduce_paley43.sh`. The default chunk size puts ~6.4 GB into buffers and peaks
> near 26 GB at layer 20; `CHUNKMB=2` completed the same layers at ~9 GB.

# Tournaments determined by three and five voters — reproducibility package

Code for the paper *Tournaments determined by three and five voters*
(L. Chindelevitch and A. Harutyunyan). Every computational claim in the paper has a verifier here,
organized by section, with a claim → tool manifest further down. Section 9 of the paper describes
this package. Section and appendix numbers here follow the version submitted to *Mathematical Social
Sciences*. The independent reproduction ([REPRODUCTION.md](REPRODUCTION.md) and the report) audited the
earlier arXiv version, 2607.26690, whose Appendix A (the Paley(43) counts) is Appendix F of this one.

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
- **Reproduce the keystone end-to-end** — the headline result (Paley(43) is not the majority of five
  voters, Section 7 ⇒ **N(5) ≤ 43**) rebuilds from one script:
  `cd sec7_paley43 && ./reproduce_paley43.sh` (details under *Quick start* below).

The package is source code plus a few small data files (≈ 3 MB).
Large data — McKay's tournament catalogues, the Paley(43)
DP layer tables — is not checked in; the scripts regenerate it or download it (see *Data policy*).
Most claims are cross-checked by two independent engines (e.g. CPLEX *and* OR-Tools CP-SAT, or an ILP
*and* a solver-free check), and every reported optimum is re-verified in exact rational arithmetic.

## Environment

You need a **C compiler**, **R**, and **Python 3**. No script needs all of it — each says what it
uses, and `./check_env.sh` reports exactly what is present on your machine.

| | needed for | install |
|---|---|---|
| **C** (`cc -O3`) | the DP / CSP engines and screens | preinstalled (`clang` on macOS, `gcc` on Linux) |
| **Python 3** — `ortools`, `pulp` | the CP-SAT checks and the orbit certificate | `uv sync`, or `pip install -r requirements.txt` |
| **R** — `igraph`, `lpSolve`, `rcdd`, `gmp` | exact α\*, the certificates, every figure | `Rscript install_r_packages.R` |
| system libraries — GMP, MPFR | `gmp` and `rcdd` build against them | `brew install gmp mpfr` / `apt-get install libgmp-dev libmpfr-dev` |

Optional, and only for specific extras — `./check_all.sh` needs none of them:

- [GLPK](https://www.gnu.org/software/glpk/) — `sec5_a3_boundary/alpha_fast.c`, the n = 10 census
  pre-filter (`brew install glpk` / `apt-get install libglpk-dev`).
- [nauty](https://pallini.di.uniroma1.it/) `gentourng` — the n = 11 census and whole-catalogue scans
  (`brew install nauty` / `apt-get install nauty`; the upstream tarball is also fine).
- [lrs](http://cgm.cs.mcgill.ca/~avis/C/lrs.html) — the non-unit-margin obstacle enumerator
  (`brew install lrslib` / `apt-get install lrslib`).
- The R extras `combinat`, `slam`, `Matrix`, `pracma`, `tidyverse` … cover incidental helpers in
  `appendices/`: `Rscript install_r_packages.R --all`.
- `matplotlib` (the report's figures) and `marimo` (the tutorial notebook):
  `uv sync --extra figures --extra notebook`.

Two notes on how little is really required: the solver-free obstacle checker
`sec5_a3_boundary/verify_obstacle_certs.R` needs **only `gmp`**, and `appendices/hk_oracle.c` is an
`#include`d oracle rather than a standalone program.

**Data** — McKay's digraph catalogues, fetched and verified by `./get_data.sh` (see *Data policy*).

**CPLEX is optional** (see below); `cplexAPI` / `Rcplex` and `docplex` / `cplex` are used only by the
handful of CPLEX scripts.

### CPLEX (optional)

**No headline result needs it.** Paley(43) (Section 7), the N(5) ≥ 12 census (Section 6), FAS = HS₃ (Section 4), and cA3's
non-3-inducibility (Section 5) all run with just a C compiler and/or free solvers (OR-Tools CP-SAT, PuLP-CBC,
`lpSolve`, GLPK). Only these eight scripts use IBM CPLEX 22.1 — and the reproducibility ones each have
a free twin:

| CPLEX script | free twin |
|---|---|
| `sec5_a3_boundary/reg11_realize3.py` | `independent_realize3_cpsat.py` |
| `sec5_a3_boundary/n10_realize3.py` | `cpsat_realize3_n10.py` |
| `sec5_a3_boundary/cert_primal_1068.py` | `cert_orbits_1068.py` |
| `sec6_bounds/ilp10/solve_ilp10.R`, `ilp10_aggregate.R` | `sec6_bounds/ilp10/verify_5inducible.py` |
| `appendices/{gen_duals.R, k_realizability_lp.R, minimum_set_cover.R}` | — (appendix computations only) |

To run the CPLEX scripts, install **IBM ILOG CPLEX Optimization Studio 22.1** (free for academics via
the [IBM Academic Initiative](https://www.ibm.com/academic)), then add the bindings:

- **Python:** `python <cplex-studio>/python/setup.py install` — the full library; the
  `pip install cplex` community edition caps models at 1000 variables.
- **R:** `install.packages("Rcplex", configure.args="--with-cplex-dir=<cplex-studio>/cplex")`;
  `cplexAPI` (CRAN archive) builds the same way.

## Quick start — the Paley(43) result (Section 7)

```sh
cd sec7_paley43 && ./reproduce_paley43.sh
```

This builds `dp43.c`, `canon_reps.c`, `razor_screen.c`, then runs, in order:

1. **self-tests** — the MAS gauntlet on q = 7, 11 (brute force) and q = 19, 23, 31 (against known values);
2. the **δ ≤ 2 layer tables**;
3. the **level-≤ 1 shell** with a census identity check (orbit count must equal 1,841,303);
4. the **co-backing screen** ⇒ **N(5) ≤ 43**.

Needs ≤ 8 threads, ~5 GB RAM, and ~50 GB scratch disk. `d0_reps.txt` (the δ = 0 orbit representatives)
is the one committed input; every other table is regenerated.

## Manifest — claim → verifier

Theorem 2.1 (Section 2, *every minimum FAS is a minimal 3-cycle hitting set*) and Lemma 2.2 (proved in the paper's
Appendix A) are analytic and need no computation. Everything below does.

### Section 3 — Refuting Conjecture 1 of Milosz–Hamel–Pierrot (`sec3_mhp/`)

| claim | tool |
|---|---|
| Counterexamples 3.1 (m = 7, 9) and 3.2 (m = 5, n = 6): FAS > HS₃, with the minimum-weight FAS found by brute force and the margins verified | `make_family_and_mhp_figs.R` — self-checking; **stops on any mismatch** before plotting |

### Section 4 — Conjecture 2: FAS = HS₃ on 3-inducible tournaments (`sec4_fas_hs3/`)

| claim | tool |
|---|---|
| Theorem 4.1: FAS = HS₃ for **every** tournament on n ≤ 10 (exhaustive) | `hs3fas.c` — Held–Karp MAS + exact minimum 3-cycle hitting set over a McKay catalogue |
| Counterexample 4.2: regular T\* on 11 vertices with FAS = 17 > 16 = HS₃ | `make_tstar_figs.R` — self-checks FAS = 17 and HS₃ = 16 (lpSolve) |
| The six 3-inducible self-converse violators (Figure 4) | `make_conj2_cex_figs.R` — re-checks self-converse and HS₃ < FAS |

### Section 5 — The A(3) threshold fails on the boundary (`sec5_a3_boundary/`)

cA3 is the code's **ce1068**: the Z₁₁ circulant with connection set {1, 2, 3, 4, 6}.

| claim | tool |
|---|---|
| cA3 structure and exact α\* = 2/3 (rational, `rcdd`/GMP) | `verify_ce1068.R`, `analyze_ce1068.R`, `inmask_alpha.R` |
| cA3 not 3-inducible — three independent methods | `reg11_realize3.py` (CPLEX), `independent_realize3_cpsat.py` (CP-SAT), `realize3_partition.c` (solver-free) |
| 6-order 2/3-certificate; minimality; orbit-minimality | `cert_primal_1068.py`, `cert_orbits_1068.py`, `enum_profiles.c`, `make_cA3_fig.R` |
| cA3 is 5-inducible; vertex-criticality | `realize_and_delete_ce1068.py` |
| regular n = 11 census (1,223) isolating cA3 | `reg11_alphastar.R`, `reg11_realize3.py` |
| n = 10 census (9,733,056 → 1,013 counterexamples) | `n10_prefilter.R`, `extract_gidx_inm.py`, `alpha_fast.c`, `n10_realize3.py`, `cpsat_realize3_n10.py`, `batch_verify_alpha_n10.R`, `characterize_n10_ce.R` |
| cA6 (needs **9** voters); the 6-vs-9-voter dichotomy | `cert9.c` |
| forced-arc reversal counterexamples at n = 10 (Figure 8) | `make_reversal_cex_figs.R` |

### Section 6 — Improved bounds on N(k) (`sec6_bounds/`)

| claim | tool |
|---|---|
| N(5) ≥ 12: every tournament on n ≤ 11 is 5-inducible (n = 11 census over D₁₁ = 903,753,248) | `n11_census/` pipeline (`n11_worker.sh`, `n11_aggregate.sh`) driving `triple_local_csp/{margin1_scan.c, cert_m1k5.c}`; independent re-verifier `triple_local_csp/verify_m1k5.c` |
| every non-3-inducible tournament on n = 8, 9, 10 (96, 17,674, 2,830,464) has a unit-margin five-voter profile, i.e. lies in I₅,₁ | `unit_margin_witnesses/n{8,9}_unit_margin_profiles.txt.xz` (the profiles; n = 10 is regenerated), checked by `unit_margin_witnesses/verify_unit_margin.py`; regenerated by `make_witnesses.sh` |
| the n ≤ 10 ILP layer (CPLEX; free twin `verify_5inducible.py`) | `ilp10/solve_ilp10.R`, `ilp10/ilp10_aggregate.R`, `ilp10/make_chunks10.R` |
| triple-local CSP — 3-inducibility as a vertex-triple labelling (~20 µs/tournament; Appendix G.3) | `triple_local_csp/margin1_scan.c` |
| Proposition 6.1 completion-uniqueness ⇒ N(5) ≤ 39 (regular), ≤ 38 (near-regular) | `counting_bounds/extended_table1_bounds.py`, `counting_bounds/nearreg_table_bounds.py` |

### Section 7 — Paley(43) is not the majority of five voters (`sec7_paley43/`)

Run it via *Quick start* above. The pieces:

- `dp43.c` — certifies MAS(Paley(43)) = 543 (the Appendix E engine);
- `canon_reps.c` — enumerates the level-≤ 1 shell;
- `razor_screen.c` — runs the co-backing screen;
- `realize5_cpsat.py --gauntlet` — validates the CP-SAT 5-inducibility encoder used for auxiliary checks.

Proof write-up: [`PALEY43_NONREALIZABLE.md`](sec7_paley43/PALEY43_NONREALIZABLE.md).

### Appendices — shared engines and appendix-specific tools (`appendices/`)

| appendix | tool |
|---|---|
| B.6 — predictability LP α\* (column generation, exact MAS oracle as separator); obstacle duals (Appendix G.1) | `k_realizability_lp.R` |
| B.4 — minimum set cover of obstacle classes | `minimum_set_cover.R` |
| B.7 — triangle-packing dual certificates on Paley(43) | `gen_duals.R` |
| The catalogue of minimal obstacles at n = 9 (all minimal supports, exactly; α\* of all 17,674) | `obstacle_catalogue/` (its own README) |
| E — MAS engine: weighted Held–Karp oracle (n ≤ 16) | `hk_oracle.c` |
| G.4 — forced-arc reversal dichotomy | `reversal_check.c` |
| G — obstacle figures (G₈, G₉ role-labelled) | `make_AB_obstacle_figures.R` |

The infinite obstacle family (a forthcoming companion paper) is **not** included here.

## Data policy

No large data is committed — scripts regenerate it (`reproduce_paley43.sh` rebuilds every DP table) or
read McKay catalogues you download. Two small inputs are the exceptions, kept in the repo:
`sec7_paley43/d0_reps.txt` (2.2 MB, the δ = 0 orbit-representative seed) and
`data/regulartournaments11.RData` (40 KB, the 1,223 regular 11-vertex tournaments the cA3 scripts read).
The unit-margin witnesses for n = 8 and 9 in `sec6_bounds/unit_margin_witnesses/` (about 260 KB) are
also kept, so that they can be checked without being searched for again; the n = 10 file (40 MB) is
regenerated by `make_witnesses.sh` in about 6 minutes.

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
(`hs3fas` at n = 10, the sec5 n = 10 census, `ilp10`). Source and provenance:
Brendan McKay's digraph archive, <https://users.cecs.anu.edu.au/~bdm/data/digraphs.html>.

## Layout

```
sec3_mhp/          Section 3  MHP Conjecture 1 counterexamples
sec4_fas_hs3/      Section 4  Conjecture 2 (FAS = HS₃): n ≤ 10 census + T*
sec5_a3_boundary/  Section 5  A(3) threshold on the boundary: cA3, censuses, cA6
sec6_bounds/       Section 6  bounds on N(k): n = 11 census, ILP, counting, unit-margin witnesses
sec7_paley43/      Section 7  Paley(43), end-to-end from one script
appendices/        shared engines + appendix-specific tools (B, E, G)
common/  data/     shared α* oracle and progress helper; the few committed data inputs

check_env.sh          is this machine ready? (never runs a check — only reports)
check_all.sh          the quick PASS/FAIL verification of every section  (-v to stream output)
get_data.sh           download + verify McKay's catalogues into data/mckay/
pyproject.toml        Python environment: uv.lock pins exact versions   (uv sync)
requirements.txt      the same dependencies for plain pip
install_r_packages.R  the R side of the environment
```
