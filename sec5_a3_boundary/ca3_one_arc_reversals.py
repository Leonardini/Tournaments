#!/usr/bin/env python3
"""cA3 minus a vertex, and cA3 with one arc reversed (Appendix: the minimum certificate of cA3).

cA3 is the circulant tournament on Z_11 with connection set S = {1, 2, 3, 4, 6}. Rotation maps any
arc of step s onto 0 -> s, so reversing one arc of step s gives, up to isomorphism, the tournament
T_s = cA3 with 0 -> s reversed. This script checks the paper's statements:

  (a) deleting 0 from the progressions of steps 1, 2, 3 starting at 2, 8, 6 gives three voters
      rho, sigma, tau that induce cA3 - 0 with every margin 1;
  (b) for s = 1 and s = 3, putting 0 back at its place in the progressions of the other two steps
      and first in the progression of step s gives three voters that induce T_s;
  (c) T_2 has alpha* = 2/3 exactly and is not 3-inducible:
        alpha* <= 2/3 by (P3); alpha* >= 2/3 by a Bob strategy (orders from a cutting-plane LP,
        weights rounded to fractions) checked in exact rational arithmetic; not 3-inducible by
        OR-Tools CP-SAT (three linear orders, every arc forward in at least two: INFEASIBLE);
  (d) T_4 and T_6 have alpha* < 2/3, hence are not 3-inducible by (P1): an Alice strategy (the
        LP's arc weights rounded to fractions) under which no linear order, by an exact dynamic
        program over vertex subsets, has forward weight 2/3 or more.
Every guaranteed step asserts. Usage: python3 ca3_one_arc_reversals.py      (about a minute)
"""
from fractions import Fraction

import numpy as np
from ortools.sat.python import cp_model
from scipy.optimize import linprog

N = 11
S = {1, 2, 3, 4, 6}
TWO_THIRDS = Fraction(2, 3)
LP_TOL = 1e-9          # cutting plane: stop when no order beats the LP value by more than this
DENOM_CAP = 10_000     # rounding of LP weights to fractions; the result is then checked exactly


def cA3():
    return {(u, (u + s) % N) for u in range(N) for s in S}


def reversed_at_zero(s):
    A = cA3(); A.remove((0, s)); A.add((s, 0)); return A


def prog(a, d):
    return [(a + i * d) % N for i in range(N)]


def induces(profile, arcs, margin_one=False):
    pos = [{v: i for i, v in enumerate(o)} for o in profile]
    k = len(profile)
    counts = [sum(p[a] < p[b] for p in pos) for a, b in arcs]
    return all(c == (k + 1) // 2 for c in counts) if margin_one else all(2 * c > k for c in counts)


def max_forward(arcs, weight, exact=False):
    """Largest total weight of forward arcs over all linear orders of Z_11 (DP over subsets)."""
    zero = Fraction(0) if exact else 0.0
    w_in = [[zero] * N for _ in range(N)]
    for (a, b), x in zip(arcs, weight):
        w_in[b][a] = x                       # b placed after a: a -> b forward
    best = [zero] + [None] * ((1 << N) - 1); last = [0] * (1 << N)
    for X in range(1, 1 << N):
        for v in range(N):
            if X >> v & 1:
                P = X ^ (1 << v)
                val = best[P] + sum((w_in[v][u] for u in range(N) if P >> u & 1), zero)
                if best[X] is None or val > best[X]:
                    best[X], last[X] = val, v
    order, X = [], (1 << N) - 1
    while X:
        order.append(last[X]); X ^= 1 << last[X]
    return best[-1], order[::-1]


def forward(order, arcs):
    p = {v: i for i, v in enumerate(order)}
    return [1 if p[a] < p[b] else 0 for a, b in arcs]


def alpha_lp(arcs):
    """Cutting-plane LP for alpha*: returns (value, Alice weights y, Bob orders and weights)."""
    arcs = list(arcs); m = len(arcs); orders = [list(range(N))]
    while True:
        c = np.zeros(m + 1); c[-1] = 1
        res = linprog(c, A_ub=np.array([forward(o, arcs) + [-1] for o in orders]),
                      b_ub=np.zeros(len(orders)), A_eq=np.array([[1] * m + [0]]), b_eq=[1],
                      bounds=[(0, None)] * m + [(None, None)], method="highs")
        assert res.status == 0, "the Alice LP is feasible and bounded by construction"
        val, o = max_forward(arcs, list(res.x[:m]))
        if val <= res.x[-1] + LP_TOL:
            return res.x[-1], list(res.x[:m]), orders, list(-res.ineqlin.marginals)
        orders.append(o)


def three_inducible(arcs):
    m = cp_model.CpModel()
    pos = [[m.NewIntVar(0, N - 1, "") for _ in range(N)] for _ in range(3)]
    for p in pos:
        m.AddAllDifferent(p)
    for a, b in arcs:
        f = [m.NewBoolVar("") for _ in range(3)]
        for k in range(3):
            m.Add(pos[k][a] < pos[k][b]).OnlyEnforceIf(f[k])
            m.Add(pos[k][a] > pos[k][b]).OnlyEnforceIf(f[k].Not())
        m.Add(sum(f) >= 2)
    s = cp_model.CpSolver(); s.parameters.num_workers = 1
    st = s.Solve(m)
    assert st in (cp_model.OPTIMAL, cp_model.FEASIBLE, cp_model.INFEASIBLE), "CP-SAT must decide"
    return st != cp_model.INFEASIBLE


def frac(xs):
    f = [Fraction(float(x)).limit_denominator(DENOM_CAP) if x > 0 else Fraction(0) for x in xs]
    return [x / sum(f) for x in f]


# (a) the profile of cA3 - 0
starts = {1: 2, 2: 8, 3: 6}
full = {d: prog(a, d) for d, a in starts.items()}
minus0 = [[v for v in full[d] if v != 0] for d in (1, 2, 3)]
arcs_minus0 = {(a, b) for a, b in cA3() if 0 not in (a, b)}
assert induces(minus0, arcs_minus0, margin_one=True)
print("(a) rho, sigma, tau =", [tuple(o) for o in minus0], "induce cA3 - 0, every margin 1")

# (b) reversals of steps 1 and 3
for s in (1, 3):
    prof = [[0] + o if d == s else full[d] for d, o in zip((1, 2, 3), minus0)]
    assert induces(prof, reversed_at_zero(s)), f"completion for step {s}"
    print(f"(b) step {s}: 0 first in the step-{s} voter, at its progression place in the others,"
          f" induces cA3 with 0 -> {s} reversed")

# (c) step 2: alpha* = 2/3 exactly, not 3-inducible
A2 = sorted(reversed_at_zero(2))
val, _, orders, xs = alpha_lp(A2)
x = frac(xs)
low = min(sum(w for w, o in zip(x, orders) if forward(o, [arc])[0]) for arc in A2)
assert low >= TWO_THIRDS, f"Bob strategy guarantees only {low}"
assert not three_inducible(A2), "T_2 must not be 3-inducible"
print(f"(c) step 2: alpha* = 2/3 (Bob strategy on {sum(w > 0 for w in x)} orders, checked exactly;"
      " <= 2/3 by (P3)); not 3-inducible (CP-SAT: infeasible)")

# (d) steps 4 and 6: alpha* < 2/3
for s in (4, 6):
    A = sorted(reversed_at_zero(s))
    val, y, _, _ = alpha_lp(A)
    yq = frac(y)
    top, _ = max_forward(A, yq, exact=True)
    assert top < TWO_THIRDS, f"step {s}: Alice strategy only shows alpha* <= {top}"
    print(f"(d) step {s}: alpha* <= {top} = {float(top):.4f} < 2/3 (Alice strategy, checked exactly);"
          f" LP value {val:.4f}")
print("PASS")
