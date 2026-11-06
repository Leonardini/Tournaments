#!/usr/bin/env python3
"""Shared exact tools for the n = 9 obstacle catalogue: tournaments, the Held-Karp maximum-weight order,
exact (cddlib, rationals) and floating-point (GLOP) LPs, and the exact predictability alpha*(T) or
exact-coverage value alpha^=(T).

Notation: an order pi of the vertices sends arc u -> v forward if it ranks u before v; for weights y on the
arcs, fwd_pi(y) is the total weight of the arcs sent forward.
  alpha*(T)  = min over y >= 0 with sum y = 1 of max over orders pi of fwd_pi(y)   (predictability LP dual)
  alpha^=(T) = the same minimum with y of any sign                                (exact-coverage LP dual)
Floating point only ever proposes which orders to collect; every value used is decided in exact arithmetic.
"""
import numpy as np
from fractions import Fraction
from math import lcm
import cdd, cdd.gmp
from ortools.linear_solver import pywraplp


def read_tournaments(path):
    ts = []
    for line in open(path):
        rows = line.split()
        if rows:
            ts.append([[int(c) for c in r] for r in rows])
    return ts


def arcs_of(A):
    n = len(A)
    return [(u, v) for u in range(n) for v in range(n) if A[u][v]]


class HK:
    """Held-Karp: the maximum total weight of forward arcs over all orders, and an order attaining it."""
    def __init__(self, n):
        self.n, self.size = n, 1 << n
        masks = np.arange(self.size)
        pc = np.array([bin(m).count("1") for m in range(self.size)])
        self.layers = [masks[pc == k] for k in range(n + 1)]
        self.bits = [((masks >> u) & 1).astype(bool) for u in range(n)]

    def run(self, W, dtype):
        n, size = self.n, self.size
        inW = np.zeros((n, size), dtype=dtype)
        for v in range(n):
            for u in range(n):
                if W[u][v] != 0:
                    inW[v] += np.where(self.bits[u], W[u][v], 0).astype(dtype)
        neg = np.iinfo(np.int64).min // 4 if dtype == np.int64 else -np.inf
        f = np.full(size, neg, dtype=dtype); f[0] = 0
        par = np.full(size, -1, dtype=np.int64)
        for k in range(1, n + 1):
            M = self.layers[k]
            best = np.full(len(M), neg, dtype=dtype); arg = np.full(len(M), -1, dtype=np.int64)
            for v in range(n):
                has = ((M >> v) & 1).astype(bool)
                P = M & ~(1 << v)
                cand = np.where(has, f[P] + inW[v][P], neg)
                upd = cand > best
                best = np.where(upd, cand, best); arg = np.where(upd, v, arg)
            f[M] = best; par[M] = arg
        order, S = [], size - 1
        while S:
            v = int(par[S]); order.append(v); S &= ~(1 << v)
        order.reverse()
        return f[size - 1], order


def fwd_set(order, arcs):
    pos = {v: i for i, v in enumerate(order)}
    return tuple(i for i, (u, v) in enumerate(arcs) if pos[u] < pos[v])


class Tour:
    def __init__(self, A, hk):
        self.A, self.n, self.hk = A, len(A), hk
        self.arcs = arcs_of(A); self.m = len(self.arcs)

    def best_float(self, y):
        W = [[0.0] * self.n for _ in range(self.n)]
        for i, (u, v) in enumerate(self.arcs):
            W[u][v] = y[i]
        val, order = self.hk.run(W, np.float64)
        return float(val), order

    def best_exact(self, yq):
        """exact max_pi fwd_pi(y) for rational y (integer Held-Karp after a common scaling)."""
        L = 1
        for q in yq:
            L = lcm(L, q.denominator)
        W = [[0] * self.n for _ in range(self.n)]
        for i, (u, v) in enumerate(self.arcs):
            W[u][v] = int(yq[i] * L)
        assert sum(abs(w) for r in W for w in r) < 2 ** 50, "integer Held-Karp overflow risk"
        val, order = self.hk.run(W, np.int64)
        return Fraction(int(val), L), order


# ---------------------------------------------------------------- exact LP (cddlib, rationals)
def exact_lp(nvar, obj, le, eq):
    """maximise obj.x  s.t.  a.x <= b for (a, b) in le,  a.x = b for (a, b) in eq.  Rationals throughout.
    Returns (status, value, x, duals) with duals[j] the multiplier of row j (le rows first, then eq)."""
    rows = [[Fraction(b)] + [-Fraction(c) for c in a] for a, b in le]
    rows += [[Fraction(b)] + [-Fraction(c) for c in a] for a, b in eq]
    mat = cdd.gmp.matrix_from_array(rows, lin_set=set(range(len(le), len(rows))),
                                    rep_type=cdd.RepType.INEQUALITY, obj_type=cdd.LPObjType.MAX,
                                    obj_func=[Fraction(0)] + [Fraction(c) for c in obj])
    lp = cdd.gmp.linprog_from_matrix(mat)
    cdd.gmp.linprog_solve(lp)
    if lp.status == cdd.LPStatusType.OPTIMAL:
        return "optimal", Fraction(lp.obj_value), [Fraction(v) for v in lp.primal_solution], \
               {j: Fraction(v) for j, v in lp.dual_solution}
    if lp.status == cdd.LPStatusType.INCONSISTENT:
        return "infeasible", None, None, None
    raise RuntimeError(f"cdd LP status {lp.status}: the LPs here are bounded by construction")


def float_lp(nvar, obj, le, eq, lb, ub):
    s = pywraplp.Solver.CreateSolver("GLOP")
    x = [s.NumVar(lb[i], ub[i], "") for i in range(nvar)]
    for a, b in le:
        s.Add(sum(c * x[i] for i, c in enumerate(a) if c) <= b)
    for a, b in eq:
        s.Add(sum(c * x[i] for i, c in enumerate(a) if c) == b)
    s.Maximize(sum(c * x[i] for i, c in enumerate(obj) if c))
    st = s.Solve()
    if st == pywraplp.Solver.INFEASIBLE:
        return None
    assert st == pywraplp.Solver.OPTIMAL, f"GLOP status {st}"
    return [xi.solution_value() for xi in x]


# ---------------------------------------------------------------- alpha
def compute_alpha(T, signed, rows):
    """alpha*(T) ('std') or alpha^=(T) ('signed'), exactly.  Variables (y_0..y_{m-1}, t); min t."""
    m = T.m; nv = m + 1
    obj = [0] * m + [-1]
    eq = [([1] * m + [0], 1)]
    # box for the float proposal only (|y_e| <= 10 is loose: optimal duals here have |y_e| < 1); a box of
    # 1e3 made GLOP report ABNORMAL on a signed instance. The exact LP below has no box.
    lb = [(-10.0 if signed else 0.0)] * m + [-10.0]; ub = [10.0] * nv

    def le_rows():
        out = [([1 if i in set(F) else 0 for i in range(m)] + [-1], 0) for F in rows]
        if not signed:
            out += [([-1 if i == j else 0 for i in range(m)] + [0], 0) for j in range(m)]
        return out
    if signed:
        # an order and its reverse: fwd_pi(y) + fwd_rev(y) = sum y = 1 bounds t below by 1/2, so the exact
        # LP over the collected rows is bounded even with y free
        for order in (list(range(T.n)), list(range(T.n))[::-1]):
            F = fwd_set(order, T.arcs)
            if F not in rows:
                rows.append(F)
    # floating-point cutting plane: collect order rows (a proposal; the exact step below decides)
    for _ in range(10000):
        sol = float_lp(nv, obj, le_rows() if rows else [], eq, lb, ub)
        assert sol is not None, "alpha LP infeasible: it is feasible by construction"
        val, order = T.best_float(sol[:m])
        if val <= sol[m] + 1e-9:
            break
        F = fwd_set(order, T.arcs)
        if F in rows:
            break
        rows.append(F)
    else:
        raise RuntimeError("alpha cutting plane did not converge in 10000 rounds")
    # exact: LP over the collected rows (relaxation, lower bound) + exact Held-Karp on its y (upper bound)
    while True:
        st, val, x, _ = exact_lp(nv, obj, le_rows(), eq)
        assert st == "optimal", "exact alpha LP must be optimal (feasible and bounded)"
        yq, t = x[:m], x[m]
        best, order = T.best_exact(yq)
        if best <= t:
            assert best == t
            return t
        rows.append(fwd_set(order, T.arcs))


