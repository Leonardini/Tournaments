#!/usr/bin/env python3
"""Theorem thm:circulant-family, the three orders settled by computation: n = 21, 27, 45.

For each n we take three distinct units e = (e1, e2, e3) of Z_n with e1 + e2 + e3 = 0 (mod n), the
connection set S = {s : sum_i (s * e_i mod n) = n}, and the circulant tournament T on Z_n with arcs
u -> u + s, s in S.  The paper proves alpha*(T) = 2/3 for every such T.  This script proves, by
exhaustive search, that T is not 3-inducible:

  1. every arc of T lies on a cyclic triangle, so by (P4a) every voter of a 3-voter profile is
     ADMISSIBLE (exactly one backward arc on every cyclic triangle), and the three voters' backward
     sets are pairwise disjoint (an arc backward in two of three voters loses its majority);
  2. the admissible orders are exactly the 3n progressions P(a, d_i) = (a, a + d_i, a + 2 d_i, ...),
     d_i = e_i^{-1}: a depth-first search over orders beginning with 0 (translation is an
     automorphism), which rejects a vertex as soon as some cyclic triangle through it and an earlier
     vertex is decided with a backward count other than 1;
  3. no three progressions (repetition allowed) have pairwise disjoint backward sets.

Every step either succeeds or the script stops with an error saying which statement failed.
Runtime: about a minute on one core (the search at n = 45 dominates).
"""
import sys
from itertools import combinations_with_replacement

CASES = {21: (1, 4, 16), 27: (1, 7, 19), 45: (1, 13, 31)}


def connection_set(n, e):
    assert sum(e) % n == 0 and len(set(e)) == 3, (n, e)
    for x in e:
        pow(x, -1, n)                                  # raises ValueError unless x is a unit
    S = {s for s in range(1, n) if sum(s * x % n for x in e) == n}
    assert all((s in S) != ((n - s) in S) for s in range(1, n)), "not a tournament"
    return S


def admissible_orders_from_zero(n, S):
    """All admissible orders of the circulant (n, S) that begin with 0."""
    arc = [[(v - u) % n in S for v in range(n)] for u in range(n)]
    cyc = [[[] for _ in range(n)] for _ in range(n)]   # cyc[x][y]: z with {x, y, z} cyclic
    for x in range(n):
        for y in range(n):
            if x != y:
                cyc[x][y] = [z for z in range(n) if z not in (x, y)
                             and ((arc[x][y] and arc[y][z] and arc[z][x]) or
                                  (arc[y][x] and arc[z][y] and arc[x][z]))]
    out, pos, order = [], [-1] * n, []

    def p(v):                                          # an unplaced vertex comes after all placed
        return pos[v] if pos[v] >= 0 else n

    def backward(u, v):                                # the arc u -> v is backward
        return p(v) < p(u)

    def ok(y):
        # y was just placed; every cyclic triangle {x, y, z} with x placed earlier is now decided,
        # since z is either placed or the only unplaced vertex of the three (so it comes last)
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
        if len(order) == n:
            out.append(tuple(order)); return
        for y in range(n):
            if pos[y] < 0:
                pos[y] = len(order); order.append(y)
                if ok(y):
                    dfs()
                order.pop(); pos[y] = -1

    pos[0] = 0; order.append(0)
    dfs()
    return out


def backward_mask(n, S, order):
    pos = {v: i for i, v in enumerate(order)}
    m = 0
    for u in range(n):
        for s in S:
            v = (u + s) % n
            if pos[v] < pos[u]:
                m |= 1 << (u * n + v)
    return m


def main():
    for n, e in CASES.items():
        S = connection_set(n, e)
        D = sorted(pow(x, -1, n) for x in e)
        arcs = [(u, (u + s) % n) for u in range(n) for s in S]
        # 1. every arc on a cyclic triangle
        for u, v in arcs:
            if not any((w - v) % n in S and (u - w) % n in S for w in range(n)):
                sys.exit(f"n={n}: arc {u}->{v} lies on no cyclic triangle")
        # 2. admissible orders = progressions
        found = set(admissible_orders_from_zero(n, S))
        progs = {tuple((i * d) % n for i in range(n)) for d in D}
        if found != progs:
            sys.exit(f"n={n}: admissible orders from 0 are not exactly the progressions of steps {D}")
        # 3. no three progressions with pairwise disjoint backward sets
        allp = [tuple((a + i * d) % n for i in range(n)) for d in D for a in range(n)]
        masks = [backward_mask(n, S, p) for p in allp]
        for i, j, k in combinations_with_replacement(range(len(masks)), 3):
            if not (masks[i] & masks[j] or masks[i] & masks[k] or masks[j] & masks[k]):
                sys.exit(f"n={n}: progressions {allp[i]}, {allp[j]}, {allp[k]} induce T")
        print(f"n={n}: e={e}, steps {D}, |S|={len(S)}; admissible orders from 0 = the 3 progressions; "
              f"no three of the {len(allp)} progressions induce T -> not 3-inducible")
    print("PASS")


if __name__ == "__main__":
    main()
