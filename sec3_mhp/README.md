# Section 3 — Refuting Conjecture 1 of Milosz–Hamel–Pierrot  (`sec3_mhp/`)

**What it does.** Reproduces the paper's Counterexamples 3.1 (m = 7 and m = 9 voters) and
3.2 (m = 5 voters, n = 6 candidates), which refute Conjecture 1 of Milosz–Hamel–Pierrot by
exhibiting weighted majority tournaments whose minimum-weight feedback arc set (FAS) exceeds
the minimum 3-cycle hitting set. The single script builds each tournament from explicit voter
lists and multiplicities, finds the minimum-weight FAS **by brute force over all vertex orders**,
self-checks the tournament structure and the optimal FAS (value / number of tied optimal sets /
the specific arcs) against the paper's claimed values — stopping on any mismatch — and only then
renders the figures. As a side product it also draws the Section-9 obstacle-family members
(`ObstacleG8/H9/G10/H11`), each Eulerian-checked with `3n − 4` arcs before plotting.

**Files.**
- `make_family_and_mhp_figs.R` — self-checking brute-force verifier + figure generator for
  Counterexamples 3.1/3.2 (and the obstacle-family figures).

**Dependencies.** R with the `igraph` package (the only library loaded here). Versions and
installation are in the [top-level README](../README.md#environment). None require CPLEX.

**How to run.** Takes no CLI arguments; writes all output PDFs to the current directory, so run
it from its own folder:

```sh
cd sec3_mhp
Rscript make_family_and_mhp_figs.R
```

**What to expect.**

- `make_family_and_mhp_figs.R` — approximately a few seconds (brute force is at most 24 vertex
  orders for the n = 4 tournaments and 720 for the n = 6 tournament; the rest is `igraph`
  rendering of four small PDFs). It writes four
  PDFs to the working directory: `ObstacleG8.pdf`, `ObstacleH9.pdf` (the two smallest members of the obstacle families;
  `../obstacle_family/make_family_section_figs.R` draws the next two), and `MHP_Fig1.pdf`, `MHP_Fig2.pdf`, the two
  panels of the figure of the counterexamples to Conjecture 1 of Milosz et al. Each figure prints a confirmation line, e.g. `ObstacleG8.pdf written`.
  Panel (a) shows the four-vertex counterexample for both seven and nine voters, which differ only in the
  margin of the arc 3 → 4 (labelled "3 (5)"); its self-check prints
  `MHP_Fig1: seven voters, min-weight FAS value <v> | optimal sets: 2 ; nine voters, value <v> | optimal sets: 1`,
  and panel (b) prints
  `MHP_Fig2: unique min-weight FAS confirmed, value <v>`. Because every FAS/margin claim is
  guarded by `stopifnot` before plotting (the majority tournament must match the paper's, and the
  brute-force optimum must have the expected value, count of tied optimal sets, and specific
  arcs), the script **errors out and produces no figures if any claim fails to reproduce**.
