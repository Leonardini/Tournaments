# Obstacles at every order (Section "Obstacles at every order" and Appendix F)

The paper shows that every fraction (2t − 1)/(3t − 1) with t ≥ 7 is the predictability of a
tournament. With n = t + 1, it builds two families of obstacles, G_n for even n ≥ 8 and H_n for
odd n ≥ 9, and their completions Ĝ_n and Ĥ_n, which are tournaments. Theorem 7.2 states that all
four have predictability exactly (2n − 3)/(3n − 4), and that G_n (H_n) is the only minimal obstacle of
its completion. This folder holds:

| file | content |
|---|---|
| `make_family_section_figs.R` | the figure of G₁₀ and H₁₁ with their arc classes (path, hub, defect, other); checks the arc counts, the Eulerian property and that no arc is drawn through a vertex before drawing, and writes `ObstacleG10.pdf` and `ObstacleH11.pdf` to the folder it is run from |
| `family_appendix.md` | the detailed proof of Theorem 7.2, which Appendix F of the paper summarizes: the weighted orders, their loads, the moves and the relations, as tables, with the arguments that use them |
| `check_family_appendix.py` | checks every table of `family_appendix.md` against the definitions of Section 7.1, for k ≤ 25 (see below) |
| `lean/` | a Lean 4 proof (Mathlib) of Theorem 7.2 for every n ≥ 8: the value (2n − 3)/(3n − 4), and the uniform distribution on G_n (H_n) as the only optimal Alice strategy of the completion |

## Checking the tables

```sh
python3 check_family_appendix.py      # a few seconds, standard library only
```

The script rebuilds G_n, H_n and their completions from the definitions of Section 7.1 and, for every
k ≤ 25 (an optional argument changes this bound), checks each table of `family_appendix.md` against them: the double
cover, the loads of the weighted orders in the strict certificates, the optimal Bob
strategy for G_n and its moves, the relations between the arcs of H_n, and the orders for n = 8 and 9.
`family_appendix.md` explains why the entries hold for every k, and the Lean proof below proves them for
every k. Any failure stops it with an error naming the table, the row
and k; it ends with `ALL CHECKS PASS`.

## The Lean proof

```sh
cd lean && ./install.sh     # elan, the pinned Lean 4.35.0, Mathlib's cache (~5 GB), build, axioms
```

or, with elan already installed:

```sh
cd lean/TsigmaProof
lake exe cache get          # Mathlib's prebuilt files
lake build                  # about 7.5 minutes; up to 7 Lean processes and 13 GB of memory at once
lake env lean AxiomReport.lean
```

The build uses no `sorry`, `admit` or `native_decide`. The main theorems rest only on Lean's
standard axioms `propext`, `Classical.choice` and `Quot.sound`; `axioms.txt` is the output of
`AxiomReport.lean`. A reader checking the proof should confirm two things: `lake build` reports
no error, and `AxiomReport.lean` shows no `sorryAx`. (Lean turns a failed tactic inside a nested
`by`, such as a `simp` discharger, into `sorry` and logs an error while the surrounding proof goes
through, so a build that ends "completed" with an error in its log is not a proof.)

### What it proves

Predictability is the value of the game in which Alice picks an arc and Bob a linear order, Bob
winning if the arc is forward. Write n = 2k + 6 (even) or n = 2k + 9 (odd).

- **Bob's side (`bob`, `bob_strict`).** The weighted orders of the strict certificates of
  `family_appendix.md` (for odd n, the six sets together) have total weight c(3n − 4), with c = 2 for even
  n ≥ 10, c = 6 for odd n ≥ 11 and c = 1 for n = 8, 9. Every arc of the completion is forward in
  orders of total weight at least c(2n − 3), and every arc outside the obstacle in orders of total
  weight at least c(2n − 3) + 1.
- **Alice's side (`alice`).** Alice puts weight 1 on each of the 3n − 4 arcs of the obstacle;
  every ranking makes at most 2n − 3 of them forward (Proposition 7.1, through the double cover of
  Appendix F as a sum of triangle inequalities).
- **The value (`value`, `value_exact`).** By weak duality, the completion and the obstacle both
  have predictability exactly (2n − 3)/(3n − 4).
- **The unique obstacle (`unique`).** An Alice strategy is a nonnegative weighting of the arcs of
  the completion, of total 1 (`AliceOpt` in `Duality.lean`); it is optimal when every linear order
  makes its arcs forward with total weight at most (2n − 3)/(3n − 4). `Tsigma.Even.unique` and
  `Tsigma.Odd.unique` state that the uniform distribution on the arcs of G_n (H_n) is optimal, and
  that every optimal one equals it. The proof follows Appendix F: the strict certificates confine
  an optimal Alice strategy to the obstacle (Lemma "loads"); the orders of an optimal Bob strategy
  are tight, and the moves of one vertex in them relate the weights of two arcs (Lemma "moves");
  the moves and relations of `family_appendix.md` force all the weights to be equal (for n = 8, 9, the
  equations of the tight orders do).

`Tournament.lean` proves that each completion is a tournament: exactly one arc joins any two
distinct vertices.

| file | content |
|---|---|
| `Common.lean` | indicators, the contribution of a group of orders as the length of an interval, `BobFwd`, `AliceFwd`, weak duality |
| `EvenDefs.lean`, `OddDefs.lean` | G_n and H_n, the completion orders, the completions, the rankings of the strict certificates, injectivity |
| `EvenLoads*.lean`, `OddLoads*.lean`, `Even.lean`, `Odd.lean` | the load of every class of arcs; Bob's side |
| `UpperEven.lean`, `UpperOdd.lean` | Alice's side: the double cover |
| `Small.lean` | n = 8 and n = 9: the orders X_n and Y_n, checked by `decide` |
| `Main.lean` | the value |
| `Tournament.lean` | the completions are tournaments |
| `Duality.lean`, `Support.lean`, `Bridge.lean` | optimal Alice strategies: Lemmas "loads" and "moves", sums over the arcs of the obstacle, the uniform distribution |
| `EvenDual*.lean`, `EvenMoves*.lean`, `OddTight.lean`, `OddMoves*.lean` | the optimal Bob strategies, their tight orders, and the moves and relations of `family_appendix.md` |
| `UniqueEven.lean`, `UniqueOdd.lean`, `SmallUnique.lean` | the uniform distribution is the only optimal Alice strategy of the obstacle |
| `Unique.lean` | the final theorems `unique` |

The files other than `Common`, `Upper*`, `Main`, `Tournament`, `Duality`, `Support`, `Bridge`,
`UniqueEven`, `UniqueOdd` and `Unique` were generated mechanically from the tables of `family_appendix.md`;
every claim in them is proved by `omega`, `decide` or `linarith`, so an error in a table makes the
build fail rather than prove a wrong theorem.

### What the formal proof does not cover

The Lean statements are about the Lean definitions `garc` (the arcs of G_n or H_n), `sigma` (the
completion order) and `tarc` (the arcs of the completion). They follow the definitions of Section
7.1 line by line, and their correspondence with the paper rests on reading them side by side.
