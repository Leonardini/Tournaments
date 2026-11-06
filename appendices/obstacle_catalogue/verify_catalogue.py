#!/usr/bin/env python3
"""Exact check, with the Python standard library only, that every class of the two catalogues is an
obstacle with the value it is listed with.

For a class with integer multiplicities m on its arcs (dual weights m_e / sum m), the best order of its
vertices collects max_pi sum_{e forward in pi} m_e, computed exactly by the Held-Karp recurrence over vertex
subsets.  The script asserts that this share equals the listed value (alpha* for n9_minimal_obstacles.tsv,
alpha^= for n9_signed_obstacles_254.tsv) and that the value is below 2/3.  A tournament containing the
class's arcs therefore has alpha* (resp. alpha^=) at most that value: these weights, put on its arcs and 0
elsewhere, leave every order at most that share.  The script also checks that every class is Eulerian.

Usage: python3 verify_catalogue.py      (from this folder; about a second)
"""
from fractions import Fraction
from collections import Counter


def best_order(arcs, m):
    """max over orders of the vertices of the total multiplicity of forward arcs (exact integers)."""
    verts = sorted({u for u, _ in arcs} | {v for _, v in arcs}); k = len(verts)
    pos = {v: i for i, v in enumerate(verts)}
    inw = [[0] * k for _ in range(k)]                        # inw[v][u] = multiplicity of u -> v
    for (u, v), x in zip(arcs, m):
        inw[pos[v]][pos[u]] += x
    f = [None] * (1 << k); f[0] = 0
    for S in range(1, 1 << k):                               # f[S] = best order of S; v is S's last vertex
        f[S] = max(f[S & ~(1 << v)] + sum(inw[v][u] for u in range(k) if S >> u & 1 and u != v)
                   for v in range(k) if S >> v & 1)
    return f[(1 << k) - 1]


def check(path, signed):
    lines = [l.rstrip("\n").split("\t") for l in open(path)]
    head, rows = lines[0], [dict(zip(lines[0], r)) for r in lines[1:]]
    for r in rows:
        arcs, m = [], []
        for a in r["arclist"].split(";"):
            uv, x = a.split(":"); u, v = uv.split(">"); arcs.append((int(u), int(v))); m.append(int(x))
        assert signed or all(x > 0 for x in m), f"{r['id']}: a non-positive multiplicity in the y >= 0 catalogue"
        tot = sum(m); assert tot > 0
        val = Fraction(best_order(arcs, m), tot)
        assert val == Fraction(r["alpha"]), f"{r['id']}: best order collects {val}, listed {r['alpha']}"
        assert val < Fraction(2, 3), f"{r['id']}: value {val} is not below 2/3"
        bal = Counter()
        for (u, v), x in zip(arcs, m):
            bal[u] += x; bal[v] -= x
        assert all(b == 0 for b in bal.values()), f"{r['id']}: not Eulerian"
    print(f"{path}: {len(rows)}/{len(rows)} classes certified exactly (best order = listed value < 2/3; Eulerian)")


if __name__ == "__main__":
    check("n9_minimal_obstacles.tsv", False)
    check("n9_signed_obstacles_254.tsv", True)
