#!/usr/bin/env python3
"""The example of Section sec:family: G_10 completed along T0, T1, T2, T3, P1, P2, U1, U2, W1, W2
contains a copy of G_8 (through the arc T3 -> W1), and its predictability is exactly 13/20.

  upper bound: the copy of G_8 on T0..T3, P1, P2, U1, W1 has 20 arcs, and no order of its
               vertices keeps more than 13 of them forward (exact DP over vertex subsets), so
               Alice's uniform strategy on the copy caps alpha* at 13/20;
  lower bound: a cutting-plane LP (HiGHS master, exact DP oracle over the 2^10 vertex subsets)
               gives Bob strategies; their weights are rounded to fractions and the rounded
               strategy is checked in exact rational arithmetic to put every arc forward with
               probability at least 13/20.
Usage: python3 g10_completion_example.py      (a few seconds)
"""
from fractions import Fraction
from itertools import combinations

import numpy as np
from scipy.optimize import linprog

TARGET = Fraction(13, 20)
LP_TOL = 1e-9            # the cutting plane stops when no order beats the LP value by more than this
DENOM_CAP = 1000         # rounding of the LP's order weights; the result is then checked exactly

ORDER = ["T0", "T1", "T2", "T3", "P1", "P2", "U1", "U2", "W1", "W2"]
U, W = ["U1", "U2"], ["W1", "W2"]
G10 = ([("T0", x) for x in ("T1", "T2", "T3")] + [("T1", "T3"), ("T2", "T3")]
       + [("T3", "P1"), ("P1", "T0"), ("T3", "P2"), ("P2", "T0")]
       + [("T1", "P2"), ("P2", "T2"), ("T2", "P1"), ("P1", "T1")]
       + [(h, u) for h in ("T1", "T2") for u in U] + [(w, h) for h in ("T1", "T2") for w in W]
       + [("U1", "W1"), ("U2", "W1"), ("U2", "W2"), ("U1", "T0"), ("T3", "W2")])
assert len(G10) == 3 * len(ORDER) - 4
joined = {frozenset(a) for a in G10}
ARCS = G10 + [(a, b) for a, b in combinations(ORDER, 2) if frozenset((a, b)) not in joined]
assert len(ARCS) == len(ORDER) * (len(ORDER) - 1) // 2, "the completion is a tournament"
COPY = ["T0", "T1", "T2", "T3", "P1", "P2", "U1", "W1"]
assert ("T3", "W1") in ARCS


def max_forward(vertices, arcs, weight):
    """Largest total weight of forward arcs over the linear orders of `vertices`, and one such order."""
    n = len(vertices); ix = {v: i for i, v in enumerate(vertices)}
    w_in = [[0] * n for _ in range(n)]
    for (a, b), x in zip(arcs, weight):
        w_in[ix[b]][ix[a]] = x            # b placed after a: a -> b forward
    best = [None] * (1 << n); best[0] = 0; last = [0] * (1 << n)
    for S in range(1, 1 << n):
        for v in range(n):
            if S >> v & 1:
                P = S ^ (1 << v)
                val = best[P] + sum(w_in[v][u] for u in range(n) if P >> u & 1)
                if best[S] is None or val > best[S]:
                    best[S], last[S] = val, v
    order, S = [], (1 << n) - 1
    while S:
        order.append(vertices[last[S]]); S ^= 1 << last[S]
    return best[-1], order[::-1]


def forward(order, arcs):
    p = {v: i for i, v in enumerate(order)}
    return [1 if p[a] < p[b] else 0 for a, b in arcs]


# G_8 in the labels of Section sec:family is G_10's arcs on these eight vertices plus T3 -> W1
# (its terminal arc; in G_10 the terminal arc is T3 -> W2)
copy_arcs = [(a, b) for a, b in G10 if a in COPY and b in COPY] + [("T3", "W1")]
assert len(copy_arcs) == 3 * len(COPY) - 4
top, _ = max_forward(COPY, copy_arcs, [1] * len(copy_arcs))
assert Fraction(top, len(copy_arcs)) == TARGET, f"copy of G_8: {top}/{len(copy_arcs)}"
print(f"upper bound: the copy of G_8 has {len(copy_arcs)} arcs, at most {top} forward => alpha* <= {TARGET}")

orders = [ORDER[:]]
while True:
    m, K = len(ARCS), len(orders)
    c = np.zeros(m + 1); c[-1] = 1
    res = linprog(c, A_ub=np.array([forward(o, ARCS) + [-1] for o in orders]), b_ub=np.zeros(K),
                  A_eq=np.array([[1] * m + [0]]), b_eq=[1],
                  bounds=[(0, None)] * m + [(None, None)], method="highs")
    assert res.status == 0, "the Alice LP is feasible and bounded by construction"
    val, o = max_forward(ORDER, ARCS, list(res.x[:m]))
    if val <= res.x[-1] + LP_TOL:
        break
    orders.append(o)
w = [Fraction(float(d)).limit_denominator(DENOM_CAP) for d in -res.ineqlin.marginals]
w = [x / sum(w) for x in w]
low = min(sum(x for x, o in zip(w, orders) if forward(o, [arc])[0]) for arc in ARCS)
assert low >= TARGET, f"rounded Bob strategy only guarantees {low}"
print(f"lower bound: a Bob strategy on {sum(x > 0 for x in w)} orders puts every arc forward with "
      f"probability >= {low}, checked exactly")
print(f"alpha* = {TARGET} exactly")
print("PASS")
