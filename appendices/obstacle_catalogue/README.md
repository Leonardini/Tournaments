# The minimal obstacles at n = 9 (`appendices/obstacle_catalogue/`)

**What it does.** Computes, for every non-3-inducible 9-vertex tournament, all of its minimal obstacles:
the inclusion-minimal supports of optimal duals of the predictability LP, each with its dual weights.
It does the same for the 254 tournaments that are 3-inducible but not with unit margin, using the
exact-coverage LP, whose duals may be negative.
The result is the catalogue of the paper's obstacle appendix: 59 classes over the 17,674
non-3-inducible tournaments, and the signed classes of the 254. It also gives α\* exactly for all 17,674,
so 64/99 is the minimum predictability at n = 9.

**Why the enumeration is complete.** For a tournament T with predictability α, the optimal duals form a
polytope F = {y ≥ 0 : Σ y = 1, fwd_π(y) ≤ α for every order π}. For any set S of arcs, the optimal duals
supported inside S form a face of F. So every minimal support is the support of a vertex of F, the minimal
supports are exactly the inclusion-minimal vertex supports, and the dual on a minimal support is unique
exactly when one vertex carries it. `face_vertices.py` lists the vertices of F exactly:
1. It computes α exactly.
2. It finds the arcs that some optimal dual uses, with one exact LP.
3. It enumerates the vertices of the polytope cut out by the orders collected so far. This uses cddlib in
   rational arithmetic, after the implicit equalities have been recognised.
4. It checks every vertex against all 9! orders with an integer Held–Karp computation, adds any order a
   vertex violates, and enumerates again. When every vertex passes, the polytope is F.

No bound on the size of the dual weights is assumed anywhere.

With duals of either sign, {y_e = 0} is no longer a face, so `face_signed.py` splits y = u − w (u, w ≥ 0)
on the arcs whose weight changes sign over F and works with the vertices at which no arc has both parts
positive (the module docstring has the argument).

**Files.**
- `obstacle_lp.py` — shared tools: tournaments, the Held–Karp maximum-weight order (vectorised),
  exact LPs (cddlib) and floating-point LPs (OR-Tools GLOP, used only to propose which orders to collect),
  and α\*(T) or α⁼(T) computed exactly.
- `face_vertices.py` — the minimal obstacles of one collection of tournaments (predictability LP, y ≥ 0).
- `face_signed.py` — the same for the exact-coverage LP (y of any sign), used for the 254.
- `build_catalogue.py` — groups the minimal supports into isomorphism classes of weighted multidigraphs
  (bliss canonical forms, via igraph), numbers them as in the paper, and writes
  `n9_minimal_obstacles.tsv` and `n9_signed_obstacles_254.tsv`. One row per class; `arclist` gives the
  obstacle as a multidigraph, `u>v:m` meaning arc u → v with multiplicity m, and an arc's dual weight is its
  multiplicity divided by the sum of all multiplicities (`total_mult`; in the signed file, where a negative
  multiplicity marks a negative weight, `sum_mult`).
  The checks below are part of the script, and any failure stops it:
  - every tournament appears exactly once;
  - every minimal support carries a unique dual;
  - every tournament with G8 and α\* = 13/20 has only copies of G8 as minimal obstacles;
  - every class is Eulerian.
- `verify_catalogue.py` — checks the two catalogue files exactly, with the Python standard library only.
  For every class, the best order of its vertices (Held–Karp over vertex subsets, in integers) must
  collect exactly the listed share α\* (or α⁼) of its weight, and that share must be below 2/3. A
  tournament containing the class's arcs then has α\* (or α⁼) at most that value, so the class certifies
  that the tournament is not 3-inducible (or not with unit margin). It also checks that every class is
  Eulerian. `../../check_all.sh` runs it.
- `covers.py` — minimum covers of the 17,674, and of the 254, by obstacle classes, under containment and
  under the tournaments' own obstacles, solved exactly by CP-SAT (fewest classes, then least total
  multiplicity). It writes the four covers to `covers.tsv`.
- `draw_covers.R` — draws the classes of the two containment covers: `figures/A_prime.pdf`, the 25 classes
  that cover the 17,674 together with G8 (which every cover contains, and which the paper draws separately), and `figures/B_prime.pdf`, the 25 signed classes that cover
  the 254, with one page per class in `figures/A_prime/` and `figures/B_prime/`. An arc is labelled with
  its multiplicity when that is not 1; a red dashed arc has negative weight.
- Inputs (kept in the repository, 1.6 MB): `the1054.txt`, the 1,054 non-3-inducible 9-tournaments that do
  not contain G8; `g8set_16620.txt`, the 16,620 that do; `margin1_254.txt`, the 254 tournaments that are
  3-inducible but not with unit margin. One tournament per line, as nine 0/1 rows of its adjacency matrix.

**Dependencies.** Python 3 with `numpy`, `ortools`, `pycddlib` (3.x, which needs the cddlib and GMP C
libraries, e.g. `brew install cddlib gmp`), `python-igraph` and `networkx`. The drawings need R with the `igraph` package.

**How to run.** Each script takes `<k> <K>` and processes every K-th tournament starting at k, so the
work splits over K cores.

```sh
for k in 0 1 2 3 4 5 6 7; do python3 face_vertices.py the1054.txt face1054_$k.jsonl $k 8 & done; wait
for k in 0 1 2 3 4 5 6 7; do python3 face_vertices.py g8set_16620.txt face16620_$k.jsonl $k 8 & done; wait
for k in 0 1 2 3 4 5 6 7; do python3 face_signed.py margin1_254.txt face254_$k.jsonl $k 8 & done; wait
python3 build_catalogue.py
python3 verify_catalogue.py
python3 covers.py
Rscript draw_covers.R
```

**What to expect.** On 8 cores, the 17,674 take about 20 minutes, at about 0.5 s per tournament
(at most a few seconds each). The 254 take about 6 minutes, at about 12 s each. Each worker prints its
progress with an estimated time remaining. `build_catalogue.py` prints:

```
1,054: 1748 minimal supports, 40 classes; 384 tournaments with more than one
16,620: alpha* [('64/99', 12), ('11/17', 200), ('24/37', 145), ('13/20', 16263)]; 19 classes (G8 + 18)
minimum alpha* over the 17,674: 64/99
n9_minimal_obstacles.tsv: 59 classes; self-converse 13; shared between the two collections 0
254: 359 minimal signed supports, 51 classes; alpha^= [('21/32', 32), ('23/35', 7), ('25/38', 44), ('27/41', 50), ('29/44', 31), ('31/47', 54), ('35/53', 4), ('37/56', 16), ('39/59', 4), ('41/62', 4), ('45/68', 8)]
```

`verify_catalogue.py` takes under a second and prints:

```
n9_minimal_obstacles.tsv: 59/59 classes certified exactly (best order = listed value < 2/3; Eulerian)
n9_signed_obstacles_254.tsv: 51/51 classes certified exactly (best order = listed value < 2/3; Eulerian)
```

`covers.py` takes about 4 minutes on one core and prints (several minimum covers can tie; the counts and
the least total multiplicity are what is determined):

```
(M) containment: the 1,054 need 25 classes (total multiplicity 836): O01 O02 O03 O04 O05 O06 O07 O08 O09 O11 O12 O13 O14 O18 O19 O20 O21 O30 O32 O33 O34 O35 O36 O39 O40
    all 16,620 contain G8, and tournament 0 of g8set_16620.txt contains none of the other classes,
    so G8 is in every cover and covers all 16,620.  Minimum cover of the 17,674: 26 classes
    (G8 + the above; total multiplicity 856).
(S) own obstacles: the 1,054 need 37 classes (total multiplicity 1283): O01 O02 O03 O04 O05 O06 O07 O08 O09 O10 O11 O12 O13 O14 O17 O18 O19 O20 O21 O22 O23 O24 O25 O26 O27 O28 O29 O31 O32 O33 O34 O35 O36 O37 O38 O39 O40
    the 357 of the 16,620 with alpha* < 13/20 need 14 (total 633): O41 O42 O43 O44 O45 O46 O47 O48 O49 O50 O51 O52 O55 O56;
    the others have only G8.  Minimum cover of the 17,674: 52 classes.
254, (M) containment: 25 classes (total multiplicity 1312): U03 U07 U08 U11 U12 U13 U24 U25 U26 U27 U30 U31 U32 U37 U38 U39 U40 U41 U42 U43 U45 U46 U47 U50 U51
254, (S) own obstacles: 35 classes (total multiplicity 1742): U01 U02 U03 U04 U07 U08 U09 U11 U12 U13 U14 U15 U21 U24 U25 U26 U28 U29 U30 U31 U32 U35 U36 U37 U38 U39 U40 U41 U42 U43 U45 U46 U47 U50 U51
```
