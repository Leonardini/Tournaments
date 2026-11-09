# Obstacles at every order (Section "Obstacles at every order" and Appendix F)

The paper shows that every fraction (2t − 1)/(3t − 1) with t ≥ 7 is the predictability of a
tournament. With n = t + 1, it builds two families of obstacles, G_n for even n ≥ 8 and H_n for
odd n ≥ 9, and their completions Ĝ_n and Ĥ_n, which are tournaments. Theorem 7.2 states that all
four have predictability exactly (2n − 3)/(3n − 4). This folder holds:

| file | content |
|---|---|
| `make_family_section_figs.R` | the figure of G₁₀ and H₁₁ with their arc classes (path, hub, defect, other); checks the arc counts, the Eulerian property and that no arc is drawn through a vertex before drawing, and writes `ObstacleG10.pdf` and `ObstacleH11.pdf` to the folder it is run from |
| `lean/` | a Lean 4 proof (Mathlib), for every n ≥ 8, of the value (2n − 3)/(3n − 4) for the completions of the paper's previous version (see the status note below) |

## The Lean proof

> **Status (2026-11-09).** Theorem 7.2 of the current manuscript uses other completions, in which the family
> member is the only minimal obstacle: along T₂, W₁…W_k, U₁, T₁, T₀, P₁, T₃, P₂, U₂…U_k (even) and
> N₂, W₁…W_k, N₃, F, H, P₁, P₂, N₁, G, N₀, U₁…U_k (odd). The proof below covers the completions of the
> previous version, along T₂, W₁…W_k, T₁, T₀, P₁, U₂…U_k, U₁, T₃, P₂ and N₂, W₁…W_k, N₃, F, H, G, N₀, P₁,
> P₂, N₁, U₁…U_k, and has not yet been regenerated for the new ones.

```sh
cd lean && ./install.sh     # elan, the pinned Lean 4.35.0, Mathlib's cache (~5 GB), build, axioms
```

or, with elan already installed:

```sh
cd lean/TsigmaProof
lake exe cache get          # Mathlib's prebuilt files
lake build                  # about 1 minute and 3 GB of memory
lake env lean AxiomReport.lean
```

The build uses no `sorry`, `admit` or `native_decide`. The main theorems rest only on Lean's
standard axioms `propext`, `Classical.choice` and `Quot.sound`; `axioms.txt` is the output of
`AxiomReport.lean`. A reader checking the proof should confirm two things: `lake build` reports
no error, and `AxiomReport.lean` shows no `sorryAx`. (Lean turns a failed tactic inside a nested
`by`, such as a `simp` discharger, into `sorry` and logs an error while the surrounding proof goes
through, so a build that ends "completed" with an error in its log is not a proof.)

### How the statement is encoded

Predictability is the value of the game in which Alice picks an arc and Bob a linear order, Bob
winning if the arc is forward. Lean states both sides with integer weights, which is the rational
statement multiplied by the total weight (`TsigmaProof/Common.lean`). Write n = 2k + 6 (even) or
n = 2k + 9 (odd).

- **Bob's side, `BobFwd`.** The weighted orders of Appendix F have total weight 3n − 4. Each is
  given as a ranking that is injective on the vertices, so a linear order, and every arc of the
  completion is forward with weight at least 2n − 3.
- **Alice's side, `AliceFwd`.** Alice puts weight 1 on each of the 3n − 4 arcs of the obstacle.
  Every ranking, injective or not, makes at most 2n − 3 of them forward. This is Proposition 7.1,
  proved through the double cover of Appendix F.1 as a sum of triangle inequalities.
- **Exact value, `value_exact`.** By weak duality (`weak_duality`), no weighted orders do better
  than the fraction (2n − 3)/(3n − 4), and no weighted arcs do better against them, for the
  completion and for the obstacle alike.

The results are `Tsigma.Even.value`, `Tsigma.Even.value_exact`, `Tsigma.Odd.value` and
`Tsigma.Odd.value_exact` (`TsigmaProof/Main.lean`). `Tournament.lean` proves that each completion
is a tournament: exactly one arc joins any two distinct vertices.

| file | content |
|---|---|
| `Common.lean` | indicators, the contribution of a family of orders as the length of an interval, `BobFwd`, `AliceFwd`, weak duality |
| `Even.lean`, `Odd.lean` | G_n and H_n, the completion orders, the rankings of the order tables of Appendix F, one lemma per class of arcs (load at most n − 1), injectivity, Bob's strategy |
| `UpperEven.lean`, `UpperOdd.lean` | Alice's side: the double cover |
| `Small.lean` | n = 8 and n = 9: the orders of the small-order table, checked by `decide` |
| `Main.lean` | the final theorems |
| `Tournament.lean` | the completions are tournaments |

`Even.lean`, `Odd.lean` and `Small.lean` were generated mechanically from the order tables of
Appendix F; every claim in them is proved by `omega` or `decide`, so an error in a table makes
the build fail rather than prove a wrong theorem.

### What the formal proof does not cover

The Lean statements are about the Lean definitions `garc` (the arcs of G_n or H_n), `sigma` (the
completion order) and `tarc` (the arcs of the completion). They follow the definitions of Section
7.1 line by line, and their correspondence with the paper rests on reading them side by side.
