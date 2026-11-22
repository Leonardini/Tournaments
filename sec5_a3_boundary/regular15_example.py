#!/usr/bin/env python3
"""A regular tournament on 15 vertices with alpha* = 2/3 that is not 3-inducible (no circulant on 15
vertices is one, by circulant15.py).

The tournament T on {0, ..., 14} is given by three cyclic orders C1, C2, C3 of its vertices:
u -> v exactly when the clockwise distances from u to v in C1, C2 and C3 add up to 15 (they add up to
15 or 30, which the script checks, so this defines a tournament). For the circulants of the paper the
three cyclic orders are the progressions, and the rule is the connection-set rule.

The script checks, each step succeeding or stopping with an error naming the failed statement:
  1. T is a regular tournament;
  2. sigma(x) = 5 - x on {0..5}, 20 - x on {6..14} maps T onto its converse;
  3. T has no module other than single vertices and the whole vertex set (it is not a substitution);
  4. alpha*(T) >= 2/3: the 45 linear orders obtained by cutting C1, C2, C3 at each vertex make every
     arc backward exactly 15 times, so the uniform distribution on them backs every arc with 2/3 of the
     weight (alpha* <= 2/3 holds for every non-transitive tournament);
  5. every arc lies on a cyclic triangle, so every voter of a 3-voter profile is ADMISSIBLE (exactly one
     backward arc on every cyclic triangle) and the three backward sets are pairwise disjoint;
  6. the admissible orders beginning with 0 are exactly the three cuts of C1, C2, C3 at 0 (a
     depth-first search as in circulant_bases.py); a rotation of an admissible order is admissible
     (moving the first vertex to the end changes, on each cyclic triangle through it, which one of
     its two arcs there is backward), so the admissible orders are exactly the 45 cuts;
  7. no three of the 45 cuts (repetition allowed) have pairwise disjoint backward sets.
Standard library only, a few seconds.
"""
import sys
from itertools import combinations, combinations_with_replacement

N = 15
CYCLIC_ORDERS = [
    tuple(range(N)),
    (0, 12, 4, 2, 6, 13, 10, 7, 14, 3, 1, 8, 5, 11, 9),
    (0, 7, 12, 3, 1, 6, 11, 9, 14, 4, 2, 8, 13, 5, 10),
]


def sigma(x):
    return 5 - x if x <= 5 else 20 - x


def fail(msg):
    sys.exit(f"FAIL: {msg}")


def tournament():
    for c in CYCLIC_ORDERS:
        if sorted(c) != list(range(N)):
            fail(f"{c} is not a cyclic order of the vertices")
    pos = [{v: i for i, v in enumerate(c)} for c in CYCLIC_ORDERS]
    arc = [[False] * N for _ in range(N)]
    for u in range(N):
        for v in range(N):
            if u != v:
                s = sum((p[v] - p[u]) % N for p in pos)
                if s not in (N, 2 * N):
                    fail(f"distances from {u} to {v} add up to {s}, not 15 or 30")
                arc[u][v] = s == N
    return arc


def is_prime(arc):
    for a, b in combinations(range(N), 2):
        M = {a, b}
        grown = True
        while grown:
            grown = False
            for x in range(N):
                if x not in M and any(arc[x][m] for m in M) and any(arc[m][x] for m in M):
                    M.add(x)
                    grown = True
        if len(M) < N:
            return False
    return True


def cyclic_triangle(arc, x, y, z):
    return (arc[x][y] and arc[y][z] and arc[z][x]) or (arc[y][x] and arc[z][y] and arc[x][z])


def admissible_orders_from_zero(arc):
    cyc = [[[z for z in range(N) if z not in (x, y) and cyclic_triangle(arc, x, y, z)]
            if x != y else [] for y in range(N)] for x in range(N)]
    out, pos, order = [], [-1] * N, []

    def p(v):                                          # an unplaced vertex comes after all placed
        return pos[v] if pos[v] >= 0 else N

    def backward(u, v):
        return p(v) < p(u)

    def ok(y):
        # every cyclic triangle {x, y, z} with x placed before y is now decided
        for x in order[:-1]:
            for z in cyc[x][y]:
                if arc[x][y]:
                    b = backward(x, y) + backward(y, z) + backward(z, x)
                else:
                    b = backward(y, x) + backward(x, z) + backward(z, y)
                if b != 1:
                    return False
        return True

    def dfs():
        if len(order) == N:
            out.append(tuple(order))
            return
        for y in range(N):
            if pos[y] < 0:
                pos[y] = len(order)
                order.append(y)
                if ok(y):
                    dfs()
                order.pop()
                pos[y] = -1

    pos[0] = 0
    order.append(0)
    dfs()
    return out


def backward_set(arc, order):
    pos = {v: i for i, v in enumerate(order)}
    return frozenset((u, v) for u in range(N) for v in range(N) if arc[u][v] and pos[v] < pos[u])


def main():
    arc = tournament()
    arcs = [(u, v) for u in range(N) for v in range(N) if arc[u][v]]
    # 1. regular
    if any(sum(arc[u]) != (N - 1) // 2 for u in range(N)):
        fail("T is not regular")
    # 2. self-converse
    if any(arc[u][v] != arc[sigma(v)][sigma(u)] for u in range(N) for v in range(N) if u != v):
        fail("sigma does not map T onto its converse")
    # 3. prime
    if not is_prime(arc):
        fail("T has a nontrivial module")
    # 4. the 45 cuts back every arc exactly 30 times out of 45
    cuts = [c[r:] + c[:r] for c in CYCLIC_ORDERS for r in range(N)]
    B = [backward_set(arc, c) for c in cuts]
    for a in arcs:
        if sum(a in b for b in B) != len(cuts) // 3:
            fail(f"arc {a} is backward in {sum(a in b for b in B)} of the {len(cuts)} cuts, not 15")
    # 5. every arc on a cyclic triangle
    for u, v in arcs:
        if not any(arc[v][w] and arc[w][u] for w in range(N)):
            fail(f"arc {u}->{v} lies on no cyclic triangle")
    # 6. admissible orders = the 45 cuts
    found = set(admissible_orders_from_zero(arc))
    expected = {c[c.index(0):] + c[:c.index(0)] for c in CYCLIC_ORDERS}
    if found != expected:
        fail(f"admissible orders from 0 are {sorted(found)}, not the three cuts at 0")
    # 7. no three cuts with pairwise disjoint backward sets
    for i, j, k in combinations_with_replacement(range(len(B)), 3):
        if not (B[i] & B[j] or B[i] & B[k] or B[j] & B[k]):
            fail(f"cuts {cuts[i]}, {cuts[j]}, {cuts[k]} induce T")
    print(f"n={N}: regular, self-converse, prime; the 45 cuts of the three cyclic orders back every arc "
          f"with exactly 2/3 of the weight (alpha* = 2/3); the admissible orders are exactly these 45 cuts "
          f"and no three of them induce T -> not 3-inducible")
    print("PASS")


if __name__ == "__main__":
    main()
