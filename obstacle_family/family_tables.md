<!-- Extracted mechanically from paper 1 (Section 7.2 up to Theorem 7.2, and the tables of Appendix F) by extract_family_tables.py; check_family_appendix.py reads it. Do not edit. -->

### Tournaments that attain the bound {#sec:family-tournaments}

A tournament that contains $G_n$ or $H_n$ thus has predictability at most $\rho_n$, and it can have
less, because the pairs that the obstacle leaves unjoined may complete a smaller obstacle. For
example, if these pairs of $G_{10}$ are oriented as in the order
$T_0, T_1, T_2, T_3, P_1, P_2, U_1, U_2, W_1, W_2$, the arc $T_3 \to W_1$ completes a copy of $G_8$
on $T_0, T_1, T_2, T_3, P_1, P_2, U_1, W_1$, and the predictability drops to at most
$13/20 < 17/26 = \rho_{10}$. Even when the predictability stays at $\rho_n$, the unjoined pairs can
complete further obstacles with the same predictability, so that $G_n$ is not the only one. For a
digraph $O$ and a linear order $\lambda$ of its vertices, the *completion* of $O$ along $\lambda$ is
the tournament that contains every arc of $O$ and orients every other pair as in $\lambda$. We let
$\widehat G_n$ be the completion of $G_n$ along
$$T_2,\ W_1, \dots, W_k,\ U_1,\ T_1,\ T_0,\ P_1,\ T_3,\ P_2,\ U_2, \dots, U_k,$$
where $U_2, \dots, U_k$ is empty when $k = 1$, and $\widehat H_n$ the completion of $H_n$ along
$$N_2,\ W_1, \dots, W_k,\ N_3,\ F,\ H,\ P_1,\ P_2,\ N_1,\ G,\ N_0,\ U_1, \dots, U_k.$$
Both orders list every $W_i$ before every $U_j$, so that no unjoined pair becomes an arc from some
$U_j$ to some $W_i$, like the arcs of the zigzag path.

**Theorem []{#thm:family-value}

| obstacle | cyclic triangles $x \to y \to z \to x$, written $xyz$ |
|---|---|
| $G_n$ | $T_0T_3P_1$, $T_0T_3P_2$, $T_2P_1T_0$, $T_1P_2T_0$, $T_3P_1T_1$, $T_3P_2T_2$ |
| $H_n$ | $N_2FN_0$, $N_2FN_1$, $N_3FN_0$, $N_3FN_1$, $N_3GN_0$, $N_3GN_2$ |
| | $N_0P_2G$, $N_2P_2G$, $N_3HN_1$, $N_3HN_2$, $N_2P_1N_0$, $N_2P_2N_1$ |

Table: The cyclic triangles of $G_n$ and $H_n$ that contain no arc of the zigzag path. {#tbl:fixed-triangles .natural}

| order | vertices from first to last | weight |
|---|---|--:|
| $R_{1}$ | $W_{1:k}\ T_2\ T_1\ U_1\ T_3\ P_2\ P_1\ T_0\ U_{2:k}$ | 1 |
| $R_{2}$ | $W_{1:k}\ T_0\ T_2\ T_1\ U_1\ T_3\ P_1\ P_2\ U_{2:k}$ | 2k+1 |
| $R_{3}$ | $W_{1:k}\ T_0\ T_2\ P_1\ T_1\ U_1\ T_3\ P_2\ U_{2:k}$ | 1 |
| $R_{4}$ | $W_{1:k}\ P_1\ P_2\ T_0\ T_2\ T_1\ U_1\ T_3\ U_{2:k}$ | 2k |
| $R_{5}$ | $W_{2:k}\ T_0\ T_2\ T_1\ U_1\ T_3\ P_1\ P_2\ U_{2:k}\ W_1$ | 1 |
| $R_{6}$ | $W_{2:k}\ P_1\ T_1\ P_2\ T_2\ U_1\ T_0\ T_3\ U_{2:k}\ W_1$ | 1 |
| $R_{7}$ | $W_{2:k}\ P_2\ T_0\ T_2\ T_1\ U_1\ T_3\ P_1\ U_{2:k}\ W_1$ | 1 |
| $R_{8}$ | $W_{1:k-1}\ T_3\ W_k\ P_2\ T_2\ P_1\ T_1\ U_1\ T_0\ U_{2:k}$ | 2 |
| $R_{9}$ | $W_{1:k-1}\ T_3\ W_k\ P_1\ P_2\ T_0\ T_2\ T_1\ U_1\ U_{2:k}$ | 1 |
| $R_{10}$ | $T_2\ U_1\ T_0\ U_{2:k}\ W_{1:k-1}\ T_3\ W_k\ P_1\ T_1\ P_2$ | 1 |
| $R_{11}$ | $T_3\ S\ P_1\ T_0\ T_1\ P_2\ T_2$ | 2 |
| $R_{12}$ | $T_3\ S\ P_1\ P_2\ T_0\ T_2\ T_1$ | 1 |
| $R_{13}$ | $P_1\ T_1\ P_2\ T_0\ T_2\ T_3\ S$ | 1 |
| $R_{14}$ | $U_1\ W_1\ P_1\ P_2\ T_0\ T_1\ T_2\ T_3\ S_2$ | 1 |
| $R_{15}$ | $U_1\ W_1\ P_1\ P_2\ T_0\ T_2\ T_1\ T_3\ S_2$ | 1 |
| $R_{16}$ | $U_1\ W_1\ P_2\ T_2\ P_1\ T_0\ T_1\ T_3\ S_2$ | 1 |
| $R_{17}$ | $T_1\ U_1\ P_2\ T_0\ M\ T_3\ W_k\ T_2\ P_1$ | 2 |
| $R_{18}$ | $P_2\ T_2\ U_1\ P_1\ T_0\ M\ T_3\ W_k\ T_1$ | 2 |
| $R_{19}$ | $T_2\ T_1\ U_1\ T_3\ P_1\ P_2\ M\ W_k\ T_0$ | 1 |
| $R_{20}$ | $T_2\ P_1\ T_1\ U_1\ M\ T_3\ W_k\ P_2\ T_0$ | 1 |
| $R_{21}$ | $M\ W_k\ T_0\ T_2\ T_1\ U_1\ T_3\ P_1\ P_2$ | 3 |
| $A_j$, $0 \le j \le k$ | $T_3\ P_1\ S_{\le j}\ T_1\ S_{>j}\ P_2\ T_0\ T_2$ | 1 each |
| $A'_j$, $0 \le j \le k$ | $S_{>j}\ P_1\ T_0\ T_1\ T_3\ P_2\ S_{\le j}\ T_2$ | 1 each |
| $B_j$, $0 \le j \le k-1$ | $T_3\ P_2\ S'_{\le j}\ T_2\ S'_{>j}\ W_1\ P_1\ T_0\ T_1$ | 1 each |
| $B'_j$, $0 \le j \le k-1$ | $T_2\ T_3\ P_1\ S'_{\le j}\ T_1\ S'_{>j}\ W_1\ P_2\ T_0$ | 1 each |
| $C_j$, $0 \le j \le k-1$ | $M_{>j}\ T_3\ W_k\ P_2\ T_2\ U_1\ P_1\ T_0\ M_{\le j}\ T_1$ | 1 each |
| $C'_j$, $0 \le j \le k-1$ | $T_1\ U_1\ P_2\ T_0\ M_{\le j}\ T_2\ M_{>j}\ T_3\ W_k\ P_1$ | 2 each |
| $C''_j$, $0 \le j \le k-1$ | $T_2\ U_1\ P_1\ T_0\ M_{\le j}\ T_1\ M_{>j}\ T_3\ W_k\ P_2$ | 1 each |

Table: The strict certificate for $\widehat G_n$, $n = 2k + 6$, $k \ge 2$; a group weight is per member. {#tbl:even-orders .natural}

| arcs of $\widehat G_n$ | $R$ | $A, A'$ | $B, B'$ | $C, C', C''$ | load |
|---|--:|--:|--:|--:|--:|
| $P_1 \to P_2$ | $9$ | $0$ | $k$ | $3k$ | $4k+9$ |
| $P_1 \to T_0$, $P_1 \to T_1$, $T_3 \to P_2$ | $2k+10$ | $0$ | $0$ | $2k$ | $4k+10$ |
| $P_2 \to T_0$, $T_3 \to P_1$ | $2k+9$ | $k+1$ | $0$ | $k$ | $4k+10$ |
| $P_2 \to T_2$, $T_1 \to P_2$ | $2k+10$ | $0$ | $k$ | $k$ | $4k+10$ |
| $T_0 \to T_1$, $T_1 \to U_1$ | $9$ | $k+1$ | $k$ | $2k$ | $4k+10$ |
| $T_0 \to T_2$ | $10$ | $0$ | $2k$ | $2k$ | $4k+10$ |
| $T_0 \to T_3$, $T_1 \to T_3$ | $9$ | $k+1$ | $2k$ | $k$ | $4k+10$ |
| $T_2 \to P_1$ | $2k+8$ | $2k+2$ | $0$ | $0$ | $4k+10$ |
| $T_2 \to T_1$ | $7$ | $2k+2$ | $0$ | $2k$ | $4k+9$ |
| $T_2 \to T_3$ | $8$ | $2k+2$ | $k$ | $k$ | $4k+10$ |
| $T_2 \to U_1$ | $8$ | $2k+2$ | $0$ | $2k$ | $4k+10$ |
| $U_1 \to P_1$ | $2k+7$ | $k+2$ | $k$ | $0$ | $4k+9$ |
| $U_1 \to P_2$ | $2k+8$ | $1$ | $k$ | $k$ | $4k+9$ |
| $U_1 \to T_0$, $T_3 \to W_{k}$, $U_{k} \to W_{k-1}$ | $4k+9$ | $1$ | $0$ | $0$ | $4k+10$ |
| $U_{2} \to W_{1}$, $U_i \to W_{i-1}$ | $4k+9$ | $1$ | $0$ | $0$ | $4k+10$ |
| $U_1 \to T_3$ | $7$ | $k+2$ | $2k$ | $k$ | $4k+9$ |
| $P_1 \to U_{k}$, $W_1 \to P_2$ | $9$ | $1$ | $k$ | $3k-1$ | $4k+9$ |
| $P_2 \to U_{k}$, $W_1 \to P_1$ | $8$ | $k+2$ | $k$ | $2k-1$ | $4k+9$ |
| $T_0 \to U_{k}$, $W_1 \to T_3$ | $8$ | $k+2$ | $2k$ | $k-1$ | $4k+9$ |
| $T_1 \to U_{k}$ | $9$ | $k+1$ | $2k-1$ | $k+1$ | $4k+10$ |
| $T_2 \to U_{k}$ | $8$ | $2k+2$ | $k-1$ | $k+1$ | $4k+10$ |
| $T_3 \to U_{k}$, $W_1 \to T_0$ | $9$ | $1$ | $0$ | $4k-1$ | $4k+9$ |
| $P_1 \to U_{i}$ | $9$ | $k-i+1$ | $k$ | $2k+i-1$ | $4k+9$ |
| $P_2 \to U_{i}$ | $8$ | $2k-i+2$ | $k$ | $k+i-1$ | $4k+9$ |
| $T_0 \to U_{i}$ | $8$ | $2k-i+2$ | $2k$ | $i-1$ | $4k+9$ |
| $T_1 \to U_{i}$ | $9$ | $k+1$ | $k+i-1$ | $2k-i+1$ | $4k+10$ |
| $T_2 \to U_{i}$ | $8$ | $2k+2$ | $i-1$ | $2k-i+1$ | $4k+10$ |
| $T_3 \to U_{i}$ | $9$ | $k-i+1$ | $0$ | $3k+i-1$ | $4k+9$ |
| $W_1 \to T_1$ | $8$ | $k+1$ | $k$ | $2k+1$ | $4k+10$ |
| $W_1 \to T_2$ | $9$ | $0$ | $2k$ | $2k+1$ | $4k+10$ |
| $W_{k} \to P_1$ | $8$ | $2k+1$ | $k$ | $k$ | $4k+9$ |
| $W_{k} \to P_2$ | $9$ | $k$ | $k$ | $2k$ | $4k+9$ |
| $W_{k} \to T_0$ | $9$ | $k$ | $0$ | $3k$ | $4k+9$ |
| $W_{k} \to T_1$ | $8$ | $k+1$ | $1$ | $3k$ | $4k+10$ |
| $W_{k} \to T_2$ | $9$ | $0$ | $k+1$ | $3k$ | $4k+10$ |
| $W_{i} \to P_1$ | $8$ | $k+i+1$ | $k$ | $2k-i$ | $4k+9$ |
| $W_{i} \to P_2$ | $9$ | $i$ | $k$ | $3k-i$ | $4k+9$ |
| $W_{i} \to T_0$ | $9$ | $i$ | $0$ | $4k-i$ | $4k+9$ |
| $W_{i} \to T_1$ | $8$ | $k+1$ | $k-i+1$ | $2k+i$ | $4k+10$ |
| $W_{i} \to T_2$ | $9$ | $0$ | $2k-i+1$ | $2k+i$ | $4k+10$ |
| $W_{i} \to T_3$ | $8$ | $k+i+1$ | $2k$ | $k-i$ | $4k+9$ |
| $U_{1} \to U_{k}$, $W_{1} \to W_{k}$ | $7$ | $k+3$ | $2k$ | $k-1$ | $4k+9$ |
| $U_{1} \to U_{j}$, $j \ge 4$, $W_{1} \to W_{j}$, $j \ge 4$ | $7$ | $2k-j+3$ | $2k$ | $j-1$ | $4k+9$ |
| $U_{1} \to U_{2}$, $U_{k-1} \to U_{k}$, $U_i \to U_{i+1}$ | $7$ | $2k+1$ | $2k$ | $1$ | $4k+9$ |
| $W_{1} \to W_{2}$, $W_{k-1} \to W_{k}$, $W_i \to W_{i+1}$ | $7$ | $2k+1$ | $2k$ | $1$ | $4k+9$ |
| $U_{1} \to U_{3}$, $U_{k-2} \to U_{k}$, $U_i \to U_{i+2}$ | $7$ | $2k$ | $2k$ | $2$ | $4k+9$ |
| $W_{1} \to W_{3}$, $W_{k-2} \to W_{k}$, $W_i \to W_{i+2}$ | $7$ | $2k$ | $2k$ | $2$ | $4k+9$ |
| $U_{1} \to W_{1}$, $U_{k} \to W_{k}$, $U_i \to W_{i}$ | $4k+9$ | $0$ | $0$ | $1$ | $4k+10$ |
| $U_{i} \to U_{k}$, $i \le k-3$, $W_{i} \to W_{k}$, $i \le k-3$ | $7$ | $k+i+2$ | $2k$ | $k-i$ | $4k+9$ |
| $U_{i} \to U_{j}$, $j \ge i+3$, $W_{i} \to W_{j}$, $j \ge i+3$ | $7$ | $2k+i-j+2$ | $2k$ | $-i+j$ | $4k+9$ |
| $W_{1} \to U_{k}$ | $8$ | $k+3$ | $2k$ | $k-2$ | $4k+9$ |
| $W_{1} \to U_{j}$, $j \ge 4$ | $8$ | $2k-j+3$ | $2k$ | $j-2$ | $4k+9$ |
| $W_{1} \to U_{3}$, $W_{k-2} \to U_{k}$, $W_i \to U_{i+2}$ | $8$ | $2k$ | $2k$ | $1$ | $4k+9$ |
| $W_{k} \to U_{1}$ | $10$ | $k-1$ | $0$ | $3k$ | $4k+9$ |
| $W_{k} \to U_{j}$, $j \le k-3$ | $10$ | $k-j$ | $0$ | $3k+j-1$ | $4k+9$ |
| $W_{k} \to U_{k-1}$, $W_{2} \to U_{1}$, $W_i \to U_{i-1}$ | $10$ | $1$ | $0$ | $4k-2$ | $4k+9$ |
| $W_{k} \to U_{k-2}$, $W_{3} \to U_{1}$, $W_i \to U_{i-2}$ | $10$ | $2$ | $0$ | $4k-3$ | $4k+9$ |
| $W_{i} \to U_{1}$, $i \ge 4$ | $10$ | $i-1$ | $0$ | $4k-i$ | $4k+9$ |
| $W_{i} \to U_{k}$, $i \le k-3$ | $8$ | $k+i+2$ | $2k$ | $k-i-1$ | $4k+9$ |
| $W_{i} \to U_{j}$, $j \ge i+3$ | $8$ | $2k+i-j+2$ | $2k$ | $-i+j-1$ | $4k+9$ |
| $W_{i} \to U_{j}$, $j \le i-3$ | $10$ | $i-j$ | $0$ | $4k-i+j-1$ | $4k+9$ |

Table: The loads of the arcs of $\widehat G_n$, $n = 2k + 6$, $k \ge 3$, by class of arcs and group of orders of Table @tbl:even-orders: the orders $R_1, \dots, R_{21}$ with their weights, and the members of the families with each letter. The arcs of $G_n$ are those of load $4k + 10$. Indices $i$ and $j$ range over $2, \dots, k - 1$. {#tbl:even-loads .natural}

| order | vertices from first to last | weight |
|---|---|--:|
| $A_{1}$ | $W_{1:k}\ F\ H\ P_2\ G\ N_1\ N_0\ N_2\ N_3\ P_1\ U_{1:k}$ | k |
| $A_{2}$ | $W_{1:k}\ H\ N_1\ N_0\ N_2\ N_3\ F\ P_1\ P_2\ G\ U_{1:k}$ | k |
| $A_{3}$ | $W_{1:k}\ N_3\ F\ H\ P_2\ N_1\ G\ N_2\ P_1\ N_0\ U_{1:k}$ | 1 |
| $A_{4}$ | $W_{1:k}\ F\ N_0\ N_3\ P_2\ G\ H\ N_1\ N_2\ P_1\ U_{1:k}$ | 1 |
| $A_{5}$ | $W_{1:k}\ H\ N_0\ N_2\ P_2\ N_1\ N_3\ F\ P_1\ G\ U_{1:k}$ | 1 |
| $A_{6}$ | $W_{1:k}\ H\ N_1\ N_0\ N_2\ N_3\ F\ P_1\ P_2\ G\ U_{1:k}$ | 2 |
| $A_{7}$ | $W_{1:k}\ H\ N_1\ N_3\ G\ N_2\ F\ P_1\ N_0\ P_2\ U_{1:k}$ | 1 |
| $A_{8}$ | $N_3\ W_{1:k}\ H\ P_2\ G\ N_2\ F\ N_1\ P_1\ N_0\ U_{1:k}$ | 1 |
| $A_{9}$ | $P_1\ W_{1:k}\ N_3\ F\ H\ P_2\ N_1\ G\ N_0\ N_2\ U_{1:k}$ | 1 |
| $A_{10}$ | $E\ F\ H\ N_1\ N_0\ N_2\ N_3\ P_1\ P_2\ G$ | 1 |
| $A_{11}$ | $P_1\ P_2\ E\ F\ H\ G\ N_1\ N_0\ N_2\ N_3$ | 1 |
| $A_{12}$ | $N_1\ G\ N_0\ N_2\ N_3\ P_1\ P_2\ E\ F\ H$ | 1 |
| $A_{13}$ | $N_2\ F\ P_2\ N_1\ P_1\ G\ N_0\ E\ N_3\ H$ | 1 |
| $A_{14}$ | $G\ N_2\ F\ P_2\ N_1\ P_1\ N_0\ E\ N_3\ H$ | 1 |
| $A_{15}$ | $P_1\ F\ P_2\ G\ U_k\ H\ D\ W_1\ N_1\ N_0\ N_2\ N_3$ | 1 |
| $A_{16}$ | $N_3\ U_k\ H\ D\ P_1\ W_1\ F\ P_2\ N_1\ G\ N_0\ N_2$ | 1 |
| $A_{17}$ | $N_1\ N_3\ U_k\ H\ D\ P_1\ W_1\ G\ N_0\ N_2\ P_2\ F$ | 1 |
| $A_{18}$ | $F\ N_1\ U_k\ H\ D\ P_1\ W_1\ G\ N_0\ N_2\ N_3\ P_2$ | 1 |
| $A_{19}$ | $N_0\ N_2\ N_3\ U_k\ F\ H\ P_2\ D\ P_1\ W_1\ N_1\ G$ | 1 |
| $A_{20}$ | $N_0\ P_2\ N_1\ N_3\ U_k\ H\ D\ P_1\ W_1\ G\ N_2\ F$ | 1 |
| $A_{21}$ | $G\ N_2\ N_3\ F\ U_k\ H\ D\ P_1\ W_1\ N_0\ P_2\ N_1$ | 1 |
| $A_{22}$ | $N_1\ N_2\ N_3\ F\ G\ U_k\ H\ D\ P_1\ W_1\ N_0\ P_2$ | 1 |
| $A^{E1}_j$, $0 \le j \le k$ | $P_1\ G\ N_0\ E_{\le j}\ N_2\ E_{>j}\ N_3\ F\ H\ P_2\ N_1$ | 1 each |
| $A^{E2}_j$, $0 \le j \le k$ | $N_2\ F\ P_1\ N_0\ P_2\ E_{\le j}\ N_1\ E_{>j}\ N_3\ H\ G$ | 1 each |
| $A^{D1}_j$, $0 \le j \le k-1$ | $N_1\ N_3\ G\ U_k\ H\ D_{\le j}\ N_2\ D_{>j}\ P_1\ W_1\ F\ N_0\ P_2$ | 1 each |
| $A^{D2}_j$, $0 \le j \le k-1$ | $N_3\ F\ P_2\ U_k\ H\ D_{\le j}\ N_1\ D_{>j}\ P_1\ W_1\ G\ N_0\ N_2$ | 1 each |
| $B_{1}$ | $W_{1:k}\ F\ H\ P_2\ N_1\ G\ N_0\ N_2\ N_3\ P_1\ U_{1:k}$ | k |
| $B_{2}$ | $W_{1:k}\ H\ N_1\ N_0\ N_2\ N_3\ F\ P_1\ P_2\ G\ U_{1:k}$ | k |
| $B_{3}$ | $W_{1:k}\ N_3\ F\ H\ G\ N_0\ P_2\ N_1\ N_2\ P_1\ U_{1:k}$ | 1 |
| $B_{4}$ | $W_{1:k}\ N_3\ H\ N_1\ G\ N_2\ F\ P_1\ N_0\ P_2\ U_{1:k}$ | 1 |
| $B_{5}$ | $W_{1:k}\ N_3\ H\ N_2\ P_2\ F\ N_1\ P_1\ G\ N_0\ U_{1:k}$ | 1 |
| $B_{6}$ | $W_{1:k}\ N_3\ H\ G\ N_2\ P_2\ F\ N_1\ P_1\ N_0\ U_{1:k}$ | 1 |
| $B_{7}$ | $W_{1:k}\ F\ H\ P_2\ N_1\ G\ N_0\ N_2\ N_3\ P_1\ U_{1:k}$ | 2 |
| $B_{8}$ | $W_{1:k}\ H\ N_1\ N_2\ N_3\ F\ P_1\ N_0\ P_2\ G\ U_{1:k}$ | 1 |
| $B_{9}$ | $W_{1:k}\ H\ N_2\ F\ N_1\ P_1\ N_0\ N_3\ P_2\ G\ U_{1:k}$ | 1 |
| $B_{10}$ | $N_3\ P_1\ P_2\ E\ F\ H\ G\ N_1\ N_0\ N_2$ | 1 |
| $B_{11}$ | $N_1\ N_3\ P_1\ G\ E\ H\ N_2\ F\ N_0\ P_2$ | 1 |
| $B_{12}$ | $F\ P_1\ P_2\ G\ E\ H\ N_1\ N_0\ N_2\ N_3$ | 2 |
| $B_{13}$ | $N_1\ G\ N_2\ P_1\ N_0\ E\ N_3\ F\ H\ P_2$ | 1 |
| $B_{14}$ | $N_2\ N_3\ P_1\ P_2\ G\ E\ F\ H\ N_1\ N_0$ | 1 |
| $B_{15}$ | $U_k\ H\ D\ P_1\ W_1\ N_0\ N_2\ P_2\ F\ N_1\ N_3\ G$ | 1 |
| $B_{16}$ | $F\ U_k\ H\ D\ P_1\ W_1\ N_0\ P_2\ N_1\ N_3\ G\ N_2$ | 1 |
| $B_{17}$ | $N_0\ N_2\ N_3\ F\ U_k\ H\ D\ P_1\ W_1\ P_2\ N_1\ G$ | 1 |
| $B_{18}$ | $N_1\ N_0\ N_2\ N_3\ U_k\ H\ D\ P_1\ W_1\ F\ P_2\ G$ | 1 |
| $B_{19}$ | $N_1\ N_0\ N_2\ N_3\ F\ U_k\ H\ D\ P_1\ W_1\ P_2\ G$ | 1 |
| $B_{20}$ | $G\ N_0\ N_2\ N_3\ P_2\ F\ N_1\ U_k\ H\ D\ P_1\ W_1$ | 1 |
| $B_{21}$ | $G\ N_0\ N_2\ P_2\ N_1\ N_3\ F\ U_k\ H\ D\ P_1\ W_1$ | 1 |
| $B^{E1}_j$, $0 \le j \le k$ | $N_1\ P_1\ G\ N_0\ E_{\le j}\ N_2\ E_{>j}\ N_3\ F\ H\ P_2$ | 1 each |
| $B^{E2}_j$, $0 \le j \le k$ | $F\ P_1\ N_0\ P_2\ E_{\le j}\ N_1\ E_{>j}\ N_3\ H\ G\ N_2$ | 1 each |
| $B^{D1}_j$, $0 \le j \le k-1$ | $N_3\ G\ U_k\ H\ D_{\le j}\ N_2\ D_{>j}\ P_1\ W_1\ F\ N_0\ P_2\ N_1$ | 1 each |
| $B^{D2}_j$, $0 \le j \le k-1$ | $N_2\ N_3\ P_2\ F\ U_k\ H\ D_{\le j}\ N_1\ D_{>j}\ P_1\ W_1\ G\ N_0$ | 1 each |
| $C_{1}$ | $W_{1:k}\ F\ H\ P_2\ N_1\ G\ N_0\ N_2\ N_3\ P_1\ U_{1:k}$ | k |
| $C_{2}$ | $W_{1:k}\ H\ N_1\ N_0\ N_2\ N_3\ F\ P_1\ P_2\ G\ U_{1:k}$ | k |
| $C_{3}$ | $W_{1:k}\ N_0\ N_2\ N_3\ F\ P_2\ N_1\ P_1\ G\ U_{1:k}\ H$ | 1 |
| $C_{4}$ | $W_{1:k}\ N_3\ H\ N_2\ F\ P_2\ N_1\ P_1\ G\ N_0\ U_{1:k}$ | 1 |
| $C_{5}$ | $W_{1:k}\ F\ N_0\ N_3\ H\ P_2\ N_1\ G\ N_2\ P_1\ U_{1:k}$ | 1 |
| $C_{6}$ | $W_{1:k}\ F\ H\ N_1\ G\ N_0\ N_2\ N_3\ P_1\ P_2\ U_{1:k}$ | 3 |
| $C_{7}$ | $W_{1:k}\ H\ N_1\ N_2\ N_3\ F\ P_1\ G\ N_0\ P_2\ U_{1:k}$ | 1 |
| $C_{8}$ | $W_{1:k}\ H\ N_2\ F\ N_0\ P_2\ N_1\ N_3\ P_1\ G\ U_{1:k}$ | 1 |
| $C_{9}$ | $N_1\ P_1\ N_0\ E\ N_3\ H\ G\ N_2\ P_2\ F$ | 1 |
| $C_{10}$ | $P_1\ P_2\ G\ E\ F\ H\ N_0\ N_1\ N_2\ N_3$ | 1 |
| $C_{11}$ | $N_1\ N_2\ P_1\ N_0\ E\ N_3\ F\ H\ P_2\ G$ | 1 |
| $C_{12}$ | $N_1\ P_1\ N_0\ P_2\ E\ N_3\ H\ G\ N_2\ F$ | 1 |
| $C_{13}$ | $N_3\ F\ P_1\ P_2\ G\ E\ H\ N_1\ N_0\ N_2$ | 1 |
| $C_{14}$ | $F\ H\ N_0\ P_2\ N_1\ G\ N_2\ U_k\ D\ P_1\ W_1\ N_3$ | 1 |
| $C_{15}$ | $U_k\ H\ D\ P_1\ W_1\ G\ N_0\ N_2\ P_2\ N_1\ N_3\ F$ | 1 |
| $C_{16}$ | $N_1\ N_3\ G\ U_k\ H\ D\ P_1\ W_1\ N_0\ N_2\ F\ P_2$ | 1 |
| $C_{17}$ | $N_2\ N_3\ P_2\ U_k\ H\ D\ P_1\ W_1\ F\ N_1\ G\ N_0$ | 1 |
| $C_{18}$ | $N_2\ N_3\ F\ U_k\ H\ D\ P_1\ W_1\ P_2\ N_1\ G\ N_0$ | 2 |
| $C_{19}$ | $P_2\ N_1\ N_3\ G\ N_2\ F\ U_k\ H\ D\ P_1\ W_1\ N_0$ | 1 |
| $C_{20}$ | $P_2\ N_1\ G\ N_0\ N_2\ N_3\ F\ U_k\ H\ D\ P_1\ W_1$ | 1 |
| $C^{E1}_j$, $0 \le j \le k$ | $P_1\ G\ N_0\ E_{\le j}\ N_2\ E_{>j}\ N_3\ F\ H\ P_2\ N_1$ | 1 each |
| $C^{E2}_j$, $0 \le j \le k$ | $F\ P_1\ N_0\ P_2\ E_{\le j}\ N_1\ E_{>j}\ N_3\ H\ G\ N_2$ | 1 each |
| $C^{D1}_j$, $0 \le j \le k-1$ | $N_1\ N_3\ G\ U_k\ H\ D_{\le j}\ N_2\ D_{>j}\ P_1\ W_1\ F\ N_0\ P_2$ | 1 each |
| $C^{D2}_j$, $0 \le j \le k-1$ | $N_2\ N_3\ F\ P_2\ U_k\ H\ D_{\le j}\ N_1\ D_{>j}\ P_1\ W_1\ G\ N_0$ | 1 each |
| $D_{1}$ | $W_{1:k}\ F\ H\ P_2\ N_1\ G\ N_0\ N_2\ N_3\ P_1\ U_{1:k}$ | k |
| $D_{2}$ | $W_{1:k}\ H\ N_1\ N_0\ N_2\ N_3\ F\ P_1\ P_2\ G\ U_{1:k}$ | k |
| $D_{3}$ | $W_{1:k}\ N_2\ F\ N_0\ P_2\ N_1\ N_3\ P_1\ G\ U_{1:k}\ H$ | 1 |
| $D_{4}$ | $W_{1:k}\ N_3\ F\ H\ P_2\ N_1\ G\ N_2\ P_1\ N_0\ U_{1:k}$ | 1 |
| $D_{5}$ | $W_{1:k}\ N_3\ H\ N_2\ F\ P_2\ N_1\ P_1\ G\ N_0\ U_{1:k}$ | 1 |
| $D_{6}$ | $W_{1:k}\ N_3\ H\ P_2\ G\ N_2\ F\ N_1\ P_1\ N_0\ U_{1:k}$ | 1 |
| $D_{7}$ | $W_{1:k}\ F\ H\ N_0\ P_2\ N_1\ N_3\ G\ N_2\ P_1\ U_{1:k}$ | 1 |
| $D_{8}$ | $W_{1:k}\ H\ N_1\ N_0\ N_2\ N_3\ F\ P_1\ P_2\ G\ U_{1:k}$ | 2 |
| $D_{9}$ | $W_{1:k}\ H\ N_1\ N_2\ F\ P_1\ N_0\ N_3\ P_2\ G\ U_{1:k}$ | 1 |
| $D_{10}$ | $P_1\ P_2\ E\ F\ H\ N_1\ G\ N_0\ N_2\ N_3$ | 3 |
| $D_{11}$ | $N_2\ N_3\ P_1\ P_2\ G\ E\ F\ H\ N_1\ N_0$ | 1 |
| $D_{12}$ | $G\ N_2\ P_2\ F\ N_1\ P_1\ N_0\ E\ N_3\ H$ | 1 |
| $D_{13}$ | $N_3\ F\ H\ G\ N_1\ N_0\ N_2\ P_1\ U_k\ D\ W_1\ P_2$ | 1 |
| $D_{14}$ | $N_1\ U_k\ H\ D\ P_1\ W_1\ N_0\ N_2\ N_3\ F\ P_2\ G$ | 1 |
| $D_{15}$ | $N_1\ N_3\ U_k\ H\ D\ P_1\ W_1\ G\ N_0\ N_2\ F\ P_2$ | 1 |
| $D_{16}$ | $N_3\ F\ U_k\ H\ D\ P_1\ W_1\ G\ N_0\ P_2\ N_1\ N_2$ | 1 |
| $D_{17}$ | $G\ N_0\ N_2\ N_3\ U_k\ F\ H\ D\ P_1\ W_1\ P_2\ N_1$ | 1 |
| $D_{18}$ | $N_1\ G\ N_2\ N_3\ F\ U_k\ H\ D\ P_1\ W_1\ N_0\ P_2$ | 1 |
| $D_{19}$ | $N_1\ N_0\ N_2\ N_3\ F\ U_k\ H\ D\ P_1\ P_2\ G\ W_1$ | 1 |
| $D_{20}$ | $G\ N_0\ N_2\ P_2\ N_1\ N_3\ F\ U_k\ H\ D\ P_1\ W_1$ | 1 |
| $D^{E1}_j$, $0 \le j \le k$ | $P_1\ G\ N_0\ E_{\le j}\ N_2\ E_{>j}\ N_3\ F\ H\ P_2\ N_1$ | 1 each |
| $D^{E2}_j$, $0 \le j \le k$ | $F\ P_1\ N_0\ P_2\ E_{\le j}\ N_1\ E_{>j}\ N_3\ H\ G\ N_2$ | 1 each |
| $D^{D1}_j$, $0 \le j \le k-1$ | $N_1\ N_3\ G\ U_k\ H\ D_{\le j}\ N_2\ D_{>j}\ P_1\ W_1\ F\ N_0\ P_2$ | 1 each |
| $D^{D2}_j$, $0 \le j \le k-1$ | $N_2\ N_3\ P_2\ F\ U_k\ H\ D_{\le j}\ N_1\ D_{>j}\ P_1\ W_1\ G\ N_0$ | 1 each |
| $E_{1}$ | $W_{1:k}\ F\ H\ P_2\ N_1\ G\ N_0\ N_2\ N_3\ P_1\ U_{1:k}$ | k |
| $E_{2}$ | $W_{1:k}\ H\ N_1\ N_0\ N_2\ N_3\ F\ P_1\ P_2\ G\ U_{1:k}$ | k |
| $E_{3}$ | $W_{1:k}\ N_3\ F\ H\ P_2\ N_1\ G\ N_0\ N_2\ P_1\ U_{1:k}$ | 1 |
| $E_{4}$ | $W_{1:k}\ F\ H\ N_1\ G\ N_0\ N_2\ N_3\ P_1\ P_2\ U_{1:k}$ | 1 |
| $E_{5}$ | $W_{1:k}\ F\ H\ P_2\ N_1\ G\ N_0\ N_2\ N_3\ P_1\ U_{1:k}$ | 2 |
| $E_{6}$ | $W_{1:k}\ H\ N_0\ N_2\ F\ P_2\ N_1\ N_3\ P_1\ G\ U_{1:k}$ | 1 |
| $E_{7}$ | $W_{1:k}\ H\ N_1\ N_2\ N_3\ F\ P_1\ N_0\ P_2\ G\ U_{1:k}$ | 1 |
| $E_{8}$ | $W_{1:k}\ H\ N_2\ F\ N_1\ P_1\ N_0\ N_3\ P_2\ G\ U_{1:k}$ | 1 |
| $E_{9}$ | $P_1\ W_{1:k}\ F\ N_0\ N_3\ H\ P_2\ G\ N_1\ N_2\ U_{1:k}$ | 1 |
| $E_{10}$ | $N_0\ E\ N_3\ H\ G\ N_2\ F\ P_2\ N_1\ P_1$ | 1 |
| $E_{11}$ | $N_1\ P_1\ G\ N_0\ E\ N_3\ H\ N_2\ F\ P_2$ | 1 |
| $E_{12}$ | $N_1\ N_3\ F\ P_1\ G\ E\ H\ N_0\ N_2\ P_2$ | 1 |
| $E_{13}$ | $N_3\ F\ P_1\ P_2\ G\ E\ H\ N_1\ N_0\ N_2$ | 1 |
| $E_{14}$ | $N_1\ G\ N_2\ P_1\ N_0\ P_2\ E\ N_3\ F\ H$ | 1 |
| $E_{15}$ | $N_1\ N_3\ G\ N_2\ U_k\ D\ F\ H\ P_1\ W_1\ N_0\ P_2$ | 1 |
| $E_{16}$ | $N_2\ N_3\ F\ P_1\ P_2\ G\ U_k\ H\ D\ W_1\ N_0\ N_1$ | 1 |
| $E_{17}$ | $U_k\ H\ D\ P_1\ W_1\ P_2\ G\ N_1\ N_0\ N_2\ N_3\ F$ | 1 |
| $E_{18}$ | $F\ U_k\ H\ D\ P_1\ W_1\ G\ N_0\ P_2\ N_1\ N_2\ N_3$ | 1 |
| $E_{19}$ | $N_2\ N_3\ P_2\ U_k\ H\ D\ P_1\ W_1\ F\ N_1\ G\ N_0$ | 1 |
| $E_{20}$ | $P_2\ N_1\ N_3\ U_k\ H\ D\ P_1\ W_1\ G\ N_2\ F\ N_0$ | 1 |
| $E_{21}$ | $N_1\ N_0\ N_2\ N_3\ F\ U_k\ H\ D\ P_1\ W_1\ P_2\ G$ | 1 |
| $E_{22}$ | $N_0\ N_2\ N_3\ P_2\ F\ N_1\ U_k\ H\ D\ P_1\ W_1\ G$ | 1 |
| $E^{E1}_j$, $0 \le j \le k$ | $P_1\ G\ N_0\ E_{\le j}\ N_2\ E_{>j}\ N_3\ F\ H\ P_2\ N_1$ | 1 each |
| $E^{E2}_j$, $0 \le j \le k$ | $N_2\ F\ P_1\ N_0\ P_2\ E_{\le j}\ N_1\ E_{>j}\ N_3\ H\ G$ | 1 each |
| $E^{D1}_j$, $0 \le j \le k-1$ | $N_1\ N_3\ G\ U_k\ H\ D_{\le j}\ N_2\ D_{>j}\ P_1\ W_1\ F\ N_0\ P_2$ | 1 each |
| $E^{D2}_j$, $0 \le j \le k-1$ | $N_3\ F\ P_2\ U_k\ H\ D_{\le j}\ N_1\ D_{>j}\ P_1\ W_1\ G\ N_0\ N_2$ | 1 each |
| $F_{1}$ | $W_{1:k}\ F\ H\ P_2\ N_1\ G\ N_0\ N_2\ N_3\ P_1\ U_{1:k}$ | k |
| $F_{2}$ | $W_{1:k}\ H\ N_1\ N_0\ N_2\ N_3\ F\ P_1\ P_2\ G\ U_{1:k}$ | k |
| $F_{3}$ | $W_{1:k}\ N_0\ P_2\ N_1\ N_3\ G\ N_2\ F\ U_{1:k}\ H\ P_1$ | 1 |
| $F_{4}$ | $W_{1:k}\ N_3\ H\ N_2\ F\ P_2\ N_1\ P_1\ G\ N_0\ U_{1:k}$ | 1 |
| $F_{5}$ | $W_{1:k}\ N_3\ H\ P_2\ G\ N_2\ F\ N_1\ P_1\ N_0\ U_{1:k}$ | 1 |
| $F_{6}$ | $W_{1:k}\ F\ H\ N_1\ N_0\ N_2\ N_3\ P_1\ P_2\ G\ U_{1:k}$ | 1 |
| $F_{7}$ | $W_{1:k}\ F\ H\ P_2\ N_1\ G\ N_0\ N_2\ N_3\ P_1\ U_{1:k}$ | 2 |
| $F_{8}$ | $W_{1:k}\ H\ N_1\ N_0\ N_2\ N_3\ F\ P_1\ P_2\ G\ U_{1:k}$ | 2 |
| $F_{9}$ | $N_2\ P_1\ N_0\ E\ N_3\ F\ H\ P_2\ N_1\ G$ | 1 |
| $F_{10}$ | $N_3\ P_1\ P_2\ E\ F\ H\ N_1\ G\ N_0\ N_2$ | 1 |
| $F_{11}$ | $F\ P_1\ P_2\ G\ E\ H\ N_1\ N_0\ N_2\ N_3$ | 1 |
| $F_{12}$ | $G\ N_2\ F\ P_2\ N_1\ P_1\ N_0\ E\ N_3\ H$ | 1 |
| $F_{13}$ | $N_1\ N_2\ N_3\ F\ P_1\ G\ N_0\ P_2\ E\ H$ | 1 |
| $F_{14}$ | $F\ N_0\ P_2\ N_3\ H\ N_1\ G\ N_2\ P_1\ U_k\ D\ W_1$ | 1 |
| $F_{15}$ | $U_k\ H\ D\ P_1\ W_1\ G\ N_0\ N_2\ P_2\ N_1\ N_3\ F$ | 1 |
| $F_{16}$ | $U_k\ H\ D\ P_1\ G\ N_0\ W_1\ N_2\ N_3\ P_2\ F\ N_1$ | 1 |
| $F_{17}$ | $N_1\ N_3\ G\ U_k\ H\ D\ P_1\ W_1\ N_2\ F\ N_0\ P_2$ | 1 |
| $F_{18}$ | $N_2\ N_3\ P_2\ U_k\ H\ D\ P_1\ W_1\ F\ N_1\ G\ N_0$ | 1 |
| $F_{19}$ | $F\ N_1\ N_3\ U_k\ H\ D\ P_1\ W_1\ G\ N_0\ N_2\ P_2$ | 1 |
| $F_{20}$ | $N_0\ N_2\ N_3\ F\ U_k\ H\ D\ P_1\ W_1\ P_2\ N_1\ G$ | 1 |
| $F_{21}$ | $N_1\ G\ N_2\ N_3\ F\ U_k\ H\ D\ P_1\ W_1\ N_0\ P_2$ | 1 |
| $F^{E1}_j$, $0 \le j \le k$ | $N_1\ P_1\ G\ N_0\ E_{\le j}\ N_2\ E_{>j}\ N_3\ F\ H\ P_2$ | 1 each |
| $F^{E2}_j$, $0 \le j \le k$ | $F\ P_1\ N_0\ P_2\ E_{\le j}\ N_1\ E_{>j}\ N_3\ H\ G\ N_2$ | 1 each |
| $F^{D1}_j$, $0 \le j \le k-1$ | $N_3\ G\ U_k\ H\ D_{\le j}\ N_2\ D_{>j}\ P_1\ W_1\ F\ N_0\ P_2\ N_1$ | 1 each |
| $F^{D2}_j$, $0 \le j \le k-1$ | $N_2\ N_3\ F\ P_2\ U_k\ H\ D_{\le j}\ N_1\ D_{>j}\ P_1\ W_1\ G\ N_0$ | 1 each |

Table: Six sets $A$ to $F$ of weighted orders for $\widehat H_n$, $n = 2k + 9$, $k \ge 1$; a group weight is per member. {#tbl:odd-orders .natural}

| order | vertices from first to last | weight |
|---|---|--:|
| $h$ | $T_3\ W_1\ P_1\ P_2\ T_0\ W_{2:k}\ T_2\ T_1\ U_{2:k}\ U_1$ | $2k$ |
| $Q_1$ | $W_1\ P_1\ P_2\ T_0\ W_{2:k}\ T_2\ T_1\ U_{2:k}\ U_1\ T_3$ | 1 |
| $Q_2$ | $T_0\ W_{2:k}\ T_2\ T_1\ U_{2:k}\ U_1\ T_3\ W_1\ P_1\ P_2$ | 2 |
| $Q_3$ | $U_1\ T_3\ W_1\ P_1\ P_2\ T_0\ W_{2:k}\ T_1\ T_2\ U_{2:k}$ | 1 |
| $Q_4$ | $T_2\ P_1\ S_2\ U_1\ W_1\ T_0\ T_1\ T_3\ P_2$ | 1 |
| $Q_5$ | $T_1\ T_3\ P_1\ S_2\ U_1\ P_2\ W_1\ T_0\ T_2$ | 1 |
| $Q_6$ | $U_1\ P_2\ W_1\ T_2\ P_1\ T_0\ T_1\ T_3\ S_2$ | 1 |
| $Q_7$ | $W_1\ T_0\ T_2\ T_1\ T_3\ P_1\ S_2\ U_1\ P_2$ | 1 |
| $Q_8$ | $P_1\ T_1\ U_1\ M\ T_3\ W_k\ P_2\ T_0\ T_2$ | 1 |
| $Q_9$ | $T_2\ T_3\ P_1\ U_1\ T_0\ M\ W_k\ T_1\ P_2$ | 1 |
| $Q_{10}$ | $P_2\ T_2\ P_1\ U_1\ T_0\ M\ T_3\ W_k\ T_1$ | 1 |
| $Q_{11}$ | $P_1\ T_1\ P_2\ T_2\ U_1\ T_0\ M\ T_3\ W_k$ | 1 |
| $Q_{12}$ | $M\ T_3\ W_k\ T_2\ P_1\ T_1\ P_2\ U_1\ T_0$ | 1 |
| $Q_{13}$ | $T_0\ M\ T_3\ W_k\ P_2\ T_2\ P_1\ T_1\ U_1$ | 1 |
| $K_j$, $0 \le j \le k$ | $S_{\le j}\ T_1\ S_{>j}\ P_2\ T_0\ T_2\ T_3\ P_1$ | 1 each |
| $\tilde K_s$, $1 \le s \le k$ | $\tilde S_s\ P_2\ T_0\ T_2\ T_3\ P_1$ | 1 each |
| $L_s$, $1 \le s \le k$ | $T_2\ P_1\ U_1\ T_0\ M_{\le s-1}\ T_1\ M_{>s-1}\ T_3\ W_k\ P_2$ | 1 each |
| $\tilde L_j$, $1 \le j \le k - 1$ | $T_2\ P_1\ U_1\ T_0\ \tilde M_j\ T_3\ W_k\ P_2$ | 1 each |

Table: An optimal Bob strategy for $G_n$, $n = 2k + 6$, $k \ge 2$, of total $3n - 4$; $\tilde S_s$ and $\tilde M_j$ are $S$ and $M$ with the pair rewritten as stated in the text. {#tbl:even-dual-orders .natural}

| | order: stretch | move | relation |
|---|---|---|---|
| H1 | $K_{k-i}$: $\dots U_{i+1}W_{i+1}\ T_1\ U_iW_i \dots$ | $W_i$ before $T_1$ | $y(W_iT_1) \le y(U_iW_i)$ |
| H2 | $K_{k-i+1}$: $\dots U_iW_i\ T_1\ U_{i-1}W_{i-1} \dots$ | $T_1$ before $U_i$ | $y(T_1U_i) \le y(W_iT_1)$ |
| H3 | $\tilde K_i$: $\dots W_i\ T_1\ U_i \dots$ | $U_i$ before $W_i$ | $y(U_iW_i) \le y(T_1U_i)$ |
| H4 | $L_i$: $\dots U_iW_{i-1}\ T_1\ U_{i+1}W_i \dots$ | $W_i$ before $T_1$ | $y(W_iT_1) \le y(U_{i+1}W_i)$ |
| H5 | $L_{i+1}$: $\dots U_{i+1}W_i\ T_1\ U_{i+2}W_{i+1} \dots$ | $T_1$ before $U_{i+1}$ | $y(T_1U_{i+1}) \le y(W_iT_1)$ |
| H6 | $\tilde L_i$: $\dots W_i\ T_1\ U_{i+1} \dots$ | $U_{i+1}$ before $W_i$ | $y(U_{i+1}W_i) \le y(T_1U_{i+1})$ |
| E1 | $L_k$: $\dots U_kW_{k-1}\ T_1\ T_3\ W_k\ P_2$ | $W_k$ before $T_1$ | $y(W_kT_1) \le y(T_3W_k)$ |
| E2 | $Q_{10}$: $\dots T_3\ W_k\ T_1$ | $T_1$ before $T_3$ | $y(T_1T_3) \le y(W_kT_1)$ |
| E3 | $Q_4$: $T_2\ P_1\ U_kW_k \dots T_1\ T_3\ P_2$ | $W_k$ before $P_2$ | $y(T_3W_k) \le y(W_kT_1)$ |
| Fa | $\varphi Q_8$: $\dots U_1\ M\ T_3\ W_k\ P_1\ T_0\ T_1$ | $T_0$ before $U_2$ | $y(T_0T_3) \le y(P_1T_0)$ |
| Fb | $Q_{10}$: $\dots P_1\ U_1\ T_0\ M\ T_3 \dots$ | $T_3$ before $P_1$ | $y(T_3P_1) \le y(T_0T_3)$ |
| Fc | $\varphi Q_{13}$: $T_0\ M\ T_3\ W_k\ P_1 \dots$ | $P_1$ before $T_0$ | $y(P_1T_0) \le y(T_3P_1)$ |
| Fd | $Q_6$: $\dots W_1\ T_2\ P_1\ T_0 \dots$ | $T_0$ before $T_2$ | $y(T_0T_2) \le y(P_1T_0)$ |
| Fe | $Q_6$: $\dots T_2\ P_1\ T_0\ T_1 \dots$ | $T_2$ before $T_1$ | $y(T_0T_2) \le y(T_2P_1)$ |
| Ff | $h$: $T_3\ W_1\ P_1\ P_2\ T_0\ W_{2:k}\ T_2\ T_1 \dots$ | $P_1$ before $T_1$ | $y(T_2P_1) \le y(P_1T_0)$ |
| Fg | $\varphi Q_9$: $\dots T_0\ M\ W_k\ T_2\ P_1$ | $P_1$ before $P_2$ | $y(P_1T_0) \le y(T_2P_1)$ |
| Fh | $Q_8$: $P_1\ T_1\ U_1\ M\ T_3\ W_k\ P_2 \dots$ | $P_1$ before $P_2$ | $y(T_3P_1) \le y(P_1T_1)$ |
| Fi | $Q_2$: $\dots T_1\ U_{2:k}\ U_1\ T_3\ W_1\ P_1\ P_2$ | $P_1$ before $T_1$ | $y(P_1T_1) \le y(T_3P_1)$ |
| Fj | $Q_5$: $T_1\ T_3\ P_1\ S_2 \dots$ | $T_1$ before $U_k$ | $y(P_1T_1) \le y(T_1T_3)$ |
| Fk | $L_1$: $T_2\ P_1\ U_1\ T_0\ T_1\ U_2 \dots$ | $T_1$ before $U_1$ | $y(T_1U_1) \le y(T_0T_1)$ |

Table: The moves for $G_n$, $k \ge 2$. A vertex moved "before" $x$ lands just before $x$, passing the vertices in between; $y(uv)$ is the weight of the arc $u \to v$. {#tbl:even-moves .natural}

| relation | order | move |
|---|---|---|
| $y(F\to N_0) \ge y(N_0\to N_2)$ | $B_{11}$ | $N_0$ before $H$ |
| $y(F\to N_0) \ge y(N_3\to F)$ | $A_{4}$ | $F$ after $N_3$ |
| $y(F\to N_1) \ge y(N_1\to N_2)$ | $A_{8}$ | $N_1$ before $G$ |
| $y(F\to N_1) \ge y(N_2\to F)$ | $A_{3}$ | $F$ after $N_2$ |
| $y(F\to N_1) \ge y(N_3\to F)$ | $B_{15}$ | $F$ after $N_3$ |
| $y(G\to N_0) \ge y(N_0\to P_2)$ | $A_{9}$ | $N_0$ before $H$ |
| $y(G\to N_0) \ge y(P_2\to G)$ | $B_{3}$ | $G$ after $P_2$ |
| $y(G\to N_2) \ge y(N_2\to N_3)$ | $A_{7}$ | $N_2$ before $N_3$ |
| $y(G\to N_2) \ge y(N_2\to P_2)$ | $A_{8}$ | $N_2$ before $P_2$ |
| $y(G\to N_2) \ge y(N_3\to G)$ | $A_{21}$ | $G$ after $N_3$ |
| $y(G\to N_2) \ge y(P_2\to G)$ | $A_{14}$ | $G$ after $P_2$ |
| $y(H\to N_1) \ge y(N_1\to N_3)$ | $B_{4}$ | $N_1$ before $N_3$ |
| $y(H\to N_1) \ge y(N_3\to H)$ | $A_{7}$ | $H$ after $N_3$ |
| $y(H\to N_2) \ge y(N_2\to N_3)$ | $B_{5}$ | $N_2$ before $N_3$ |
| $y(N_0\to N_2) \ge y(F\to N_0)$ | $C_{16}$ | $N_0$ after $F$ |
| $y(N_0\to N_2) \ge y(P_1\to N_0)$ | $D_{13}$ | $N_0$ after $P_1$ |
| $y(N_0\to N_3) \ge y(N_3\to F)$ | $A_{4}$ | $N_3$ before $F$ |
| $y(N_0\to P_2) \ge y(G\to N_0)$ | $B_{8}$ | $N_0$ after $G$ |
| $y(N_0\to P_2) \ge y(P_2\to G)$ | $B_{3}$ | $P_2$ before $N_3$ |
| $y(N_0\to P_2) \ge y(P_2\to N_1)$ | $B_{9}$ | $P_2$ before $F$ |
| $y(N_1\to N_2) \ge y(F\to N_1)$ | $B_{4}$ | $N_1$ after $F$ |
| $y(N_1\to N_2) \ge y(N_2\to P_2)$ | $B_{3}$ | $N_2$ before $P_2$ |
| $y(N_1\to N_3) \ge y(F\to N_1)$ | $A_{5}$ | $N_1$ after $F$ |
| $y(N_1\to N_3) \ge y(H\to N_1)$ | $A^{E2}_{k}$ | $N_1$ after $H$ |
| $y(N_1\to N_3) \ge y(N_3\to F)$ | $B_{15}$ | $N_3$ before $P_2$ |
| $y(N_1\to N_3) \ge y(N_3\to H)$ | $A_{7}$ | $N_3$ before $H$ |
| $y(N_1\to P_1) \ge y(P_1\to N_0)$ | $C_{8}$ | $P_1$ before $F$ |
| $y(N_1\to P_1) \ge y(P_2\to N_1)$ | $C_{12}$ | $N_1$ after $P_2$ |
| $y(N_2\to F) \ge y(F\to N_0)$ | $A_{17}$ | $F$ before $G$ |
| $y(N_2\to F) \ge y(F\to N_1)$ | $B_{4}$ | $F$ before $H$ |
| $y(N_2\to F) \ge y(N_0\to N_2)$ | $B_{11}$ | $N_2$ after $N_0$ |
| $y(N_2\to F) \ge y(N_1\to N_2)$ | $A_{8}$ | $N_2$ after $N_1$ |
| $y(N_2\to N_3) \ge y(N_3\to G)$ | $A_{21}$ | $N_3$ before $G$ |
| $y(N_2\to P_1) \ge y(N_0\to N_2)$ | $A_{3}$ | $N_2$ after $N_0$ |
| $y(N_2\to P_1) \ge y(P_1\to N_0)$ | $A_{6}$ | $P_1$ before $N_0$ |
| $y(N_2\to P_2) \ge y(N_1\to N_2)$ | $A_{5}$ | $N_2$ after $N_1$ |
| $y(N_2\to P_2) \ge y(P_2\to G)$ | $A_{14}$ | $P_2$ before $G$ |
| $y(N_3\to F) \ge y(F\to N_1)$ | $A_{5}$ | $F$ before $P_2$ |
| $y(N_3\to F) \ge y(N_0\to N_3)$ | $B_{8}$ | $N_3$ after $N_0$ |
| $y(N_3\to F) \ge y(N_1\to N_3)$ | $B_{20}$ | $N_3$ after $N_1$ |
| $y(N_3\to G) \ge y(G\to N_2)$ | $A_{22}$ | $G$ before $N_1$ |
| $y(N_3\to G) \ge y(N_2\to N_3)$ | $A_{7}$ | $N_3$ after $N_2$ |
| $y(N_3\to H) \ge y(H\to N_1)$ | $A^{E2}_{k}$ | $H$ before $N_1$ |
| $y(N_3\to H) \ge y(H\to N_2)$ | $A^{E1}_{k}$ | $H$ before $N_2$ |
| $y(N_3\to H) \ge y(N_1\to N_3)$ | $B_{4}$ | $N_3$ after $N_1$ |
| $y(N_3\to H) \ge y(N_2\to N_3)$ | $B_{5}$ | $N_3$ after $N_2$ |
| $y(P_1\to N_0) \ge y(N_0\to N_2)$ | $A_{3}$ | $N_0$ before $N_2$ |
| $y(P_1\to N_0) \ge y(N_0\to P_2)$ | $A_{14}$ | $N_0$ before $P_2$ |
| $y(P_1\to N_0) \ge y(N_1\to P_1)$ | $A^{E2}_{0}$ | $P_1$ after $N_1$ |
| $y(P_1\to N_0) \ge y(N_2\to P_1)$ | $A^{E1}_{0}$ | $P_1$ after $N_2$ |
| $y(P_2\to G) \ge y(G\to N_0)$ | $B_{8}$ | $G$ before $F$ |
| $y(P_2\to G) \ge y(G\to N_2)$ | $A_{13}$ | $G$ before $N_2$ |
| $y(P_2\to G) \ge y(N_2\to P_2)$ | $A_{8}$ | $P_2$ after $N_2$ |
| $y(P_2\to N_1) \ge y(N_0\to P_2)$ | $A_{14}$ | $P_2$ after $N_0$ |
| $y(P_2\to N_1) \ge y(N_1\to N_2)$ | $A_{5}$ | $N_1$ before $N_0$ |
| $y(P_2\to N_1) \ge y(N_1\to P_1)$ | $A^{E2}_{0}$ | $N_1$ before $P_1$ |
| $y(P_2\to N_1) \ge y(N_2\to P_2)$ | $B_{3}$ | $P_2$ after $N_2$ |

Table: Relations between the arcs of $H_n$ joining fixed vertices, $k \ge 1$: the order of Table @tbl:odd-orders (a group member with its index $j$) and the move of Lemma @lem:family-moves. {#tbl:odd-relations .natural}

| weight | $X_8$, for $\widehat G_8$ | weight | $Y_8$, for $G_8$ |
|--:|---|--:|---|
| 5 | $U_1\,T_3\,W_1\,P_1\,P_2\,T_0\,T_2\,T_1$ | 5 | $T_2\,T_1\,U_1\,T_3\,W_1\,P_1\,P_2\,T_0$ |
| 3 | $W_1\,T_0\,T_2\,T_1\,U_1\,T_3\,P_1\,P_2$ | 3 | $P_1\,U_1\,W_1\,P_2\,T_0\,T_2\,T_1\,T_3$ |
| 1 | $P_1\,T_1\,P_2\,T_0\,T_2\,T_3\,U_1\,W_1$ | 1 | $T_3\,P_1\,T_1\,U_1\,P_2\,T_0\,W_1\,T_2$ |
| 1 | $P_1\,W_1\,T_1\,U_1\,P_2\,T_0\,T_2\,T_3$ | 1 | $W_1\,T_1\,P_2\,T_0\,T_2\,T_3\,P_1\,U_1$ |
| 1 | $P_2\,T_2\,P_1\,T_1\,U_1\,T_0\,T_3\,W_1$ | 1 | $T_3\,P_2\,T_2\,P_1\,U_1\,W_1\,T_0\,T_1$ |
| 1 | $T_0\,T_2\,P_1\,T_1\,T_3\,U_1\,P_2\,W_1$ | 1 | $W_1\,T_2\,P_1\,T_0\,T_1\,U_1\,T_3\,P_2$ |
| 1 | $T_0\,T_2\,T_3\,P_1\,T_1\,U_1\,P_2\,W_1$ | 1 | $U_1\,P_2\,T_0\,T_2\,T_3\,W_1\,P_1\,T_1$ |
| 1 | $T_1\,P_2\,T_2\,T_3\,U_1\,W_1\,P_1\,T_0$ | 1 | $P_2\,T_0\,T_3\,W_1\,T_2\,P_1\,T_1\,U_1$ |
| 1 | $T_1\,U_1\,P_2\,T_0\,T_3\,W_1\,T_2\,P_1$ | 1 | $T_0\,T_3\,P_2\,W_1\,T_2\,P_1\,T_1\,U_1$ |
| 1 | $T_2\,P_1\,T_0\,T_1\,T_3\,U_1\,W_1\,P_2$ | 1 | $U_1\,T_0\,T_3\,W_1\,T_1\,P_2\,T_2\,P_1$ |
| 1 | $T_2\,U_1\,W_1\,P_1\,T_0\,T_1\,T_3\,P_2$ | 1 | $T_0\,T_3\,P_1\,W_1\,T_1\,P_2\,T_2\,U_1$ |
| 1 | $T_3\,W_1\,T_1\,P_2\,T_2\,U_1\,P_1\,T_0$ | 1 | $P_1\,U_1\,T_0\,T_1\,T_3\,W_1\,P_2\,T_2$ |
| 1 | $W_1\,P_2\,T_2\,U_1\,P_1\,T_0\,T_1\,T_3$ | 1 | $W_1\,P_1\,T_0\,T_1\,P_2\,T_2\,U_1\,T_3$ |
| 1 | $W_1\,T_1\,P_2\,T_2\,U_1\,T_0\,T_3\,P_1$ | 1 | $W_1\,T_0\,T_2\,P_1\,T_1\,U_1\,T_3\,P_2$ |

Table: Weighted orders for $n = 8$: a strict certificate $X_8$ for $\widehat G_8$, and an optimal Bob strategy $Y_8$ for $G_8$. {#tbl:small-orders-8 .natural}

| weight | $X_9$, for $\widehat H_9$ | weight | $Y_9$, for $H_9$ |
|--:|---|--:|---|
| 3 | $P_1\,H\,P_2\,G\,N_1\,N_0\,N_2\,N_3\,F$ | 7 | $F\,H\,G\,N_0\,N_1\,N_2\,N_3\,P_1\,P_2$ |
| 1 | $N_0\,N_3\,H\,G\,N_2\,F\,P_2\,N_1\,P_1$ | 1 | $H\,P_2\,G\,N_0\,N_1\,N_2\,N_3\,F\,P_1$ |
| 1 | $N_2\,N_3\,F\,P_2\,N_1\,P_1\,H\,G\,N_0$ | 1 | $N_2\,N_3\,F\,P_2\,G\,P_1\,H\,N_0\,N_1$ |
| 1 | $N_2\,F\,P_1\,H\,N_0\,P_2\,N_1\,N_3\,G$ | 1 | $P_2\,N_1\,N_3\,G\,P_1\,H\,N_2\,F\,N_0$ |
| 1 | $N_0\,P_2\,N_1\,N_3\,H\,G\,N_2\,F\,P_1$ | 1 | $P_1\,N_0\,N_3\,H\,P_2\,G\,N_2\,F\,N_1$ |
| 1 | $F\,P_1\,N_0\,N_3\,H\,P_2\,N_1\,G\,N_2$ | 1 | $N_3\,G\,P_1\,H\,N_0\,N_2\,F\,P_2\,N_1$ |
| 1 | $G\,N_2\,N_3\,F\,P_1\,H\,N_0\,P_2\,N_1$ | 1 | $F\,P_1\,N_0\,N_3\,H\,P_2\,G\,N_1\,N_2$ |
| 1 | $N_2\,F\,N_1\,P_1\,N_0\,N_3\,P_2\,G\,H$ | 1 | $P_2\,N_1\,P_1\,N_0\,N_3\,H\,G\,N_2\,F$ |
| 1 | $N_3\,F\,H\,P_2\,N_1\,P_1\,G\,N_0\,N_2$ | 1 | $P_1\,N_0\,P_2\,N_1\,N_3\,H\,G\,N_2\,F$ |
| 4 | $F\,H\,N_1\,G\,N_0\,N_2\,N_3\,P_1\,P_2$ | 1 | $N_2\,N_3\,F\,P_1\,H\,N_0\,P_2\,N_1\,G$ |
| 2 | $N_2\,N_3\,F\,P_1\,H\,P_2\,N_1\,G\,N_0$ | 1 | $N_2\,P_1\,N_0\,N_3\,F\,H\,P_2\,G\,N_1$ |
| 1 | $P_2\,N_1\,N_3\,F\,P_1\,H\,G\,N_0\,N_2$ | 1 | $P_1\,N_0\,N_2\,N_3\,H\,F\,P_2\,G\,N_1$ |
| 1 | $N_1\,N_2\,N_3\,F\,P_1\,G\,H\,N_0\,P_2$ | 1 | $N_1\,P_1\,N_0\,N_3\,H\,N_2\,F\,P_2\,G$ |
| 1 | $N_0\,N_3\,H\,N_2\,F\,P_2\,N_1\,P_1\,G$ | 1 | $P_2\,N_1\,N_3\,G\,N_2\,F\,P_1\,N_0\,H$ |
| 1 | $F\,N_0\,P_2\,N_1\,N_3\,P_1\,G\,H\,N_2$ | 1 | $N_2\,N_3\,F\,P_2\,G\,N_1\,P_1\,H\,N_0$ |
| 1 | $N_1\,N_2\,P_1\,N_0\,N_3\,F\,H\,P_2\,G$ | 1 | $N_2\,P_2\,N_1\,N_3\,F\,G\,P_1\,H\,N_0$ |
| 1 | $N_1\,N_3\,P_1\,H\,G\,N_0\,N_2\,F\,P_2$ | 1 | $P_2\,N_1\,N_2\,N_3\,G\,F\,P_1\,H\,N_0$ |

Table: Weighted orders for $n = 9$: a strict certificate $X_9$ for $\widehat H_9$, and an optimal Bob strategy $Y_9$ for $H_9$. {#tbl:small-orders-9 .natural}
