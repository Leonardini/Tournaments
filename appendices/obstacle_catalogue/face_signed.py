#!/usr/bin/env python3
r"""
All minimal SIGNED obstacle supports of a tournament for the exact-coverage LP (y of any sign), by exact
vertex enumeration of a sign-split polytope.

T is a tournament with arc set A, alpha = alpha^=(T) (exact). The optimal-dual set
    F = { y in R^A : sum y = 1,  fwd_pi(y) <= alpha  for every order pi }
is a polytope (its recession cone {d : sum d = 0, fwd_pi(d) <= 0 for all pi} is {0}, since
fwd_pi(d) + fwd_rev(pi)(d) = sum d). With y free, {y_e = 0} is not a face of F, so minimal supports are not
read off F's vertices. Instead split y = u - w with u, w >= 0 and bound u_e + w_e <= B_e + 1, where
B_e = max |y_e| over F (exact):
    P = { (u, w) >= 0 : sum (u - w) = 1,  fwd_pi(u - w) <= alpha (all pi),  u_e + w_e <= B_e + 1 }.
(Only arcs whose weight changes sign over F need both u_e and w_e; see face().)
For a support S with signs sigma, the optimal duals with sign-consistent support inside (S, sigma) form
    P cap { u_e = 0 if sigma_e < 0 or e not in S,  w_e = 0 if sigma_e > 0 or e not in S },
a face of P on which the bounds are slack. If S is a minimal support, every point of that face has support
exactly S with signs sigma, so its vertices are vertices of P with u_e w_e = 0 for all e. Hence the minimal
supports are the inclusion-minimal (unsigned) supports among the vertices of P with u_e w_e = 0, and the
dual on a minimal (S, sigma) is unique iff exactly one such vertex has support S and signs sigma.

Steps (each exact; a failure of a promised step raises):
  1. alpha exactly (obstacle_lp.compute_alpha, signed mode).
  2. B_e = max(max y_e, max -y_e) over F for every arc, by exact LPs (float cutting plane, exact LP over the
     collected orders inside the box |y_i| <= K, exact Held-Karp check). An exact optimum strictly inside the
     box is optimal without the box (a local optimum of an LP is global).
  3. Vertex enumeration of P on the arcs with B_e > 0 (cddlib, after recognising implicit equalities), with
     the collected orders as rows; every vertex's y = u - w is checked exactly against all 9! orders by
     integer Held-Karp; violated orders are added and the enumeration rerun until all vertices pass.

Usage: python3 face_signed.py <tournaments.txt> <out.jsonl> <k> <K> [indices.txt]
"""
import sys, json, time
from fractions import Fraction
import cdd, cdd.gmp
import obstacle_lp as MS

BOX = Fraction(10 ** 6)


def face_lp(T, alpha, obj, rows):
    """max obj.y over F, exactly.  Variables y (free)."""
    m = T.m
    eq = [([1] * m, 1)]
    af = float(alpha)

    def le_rows(exact):
        out = [([1 if e in set(F) else 0 for e in range(m)], (alpha if exact else af)) for F in rows]
        if exact:
            for e in range(m):                               # the box |y_e| <= K (exact LP only)
                r = [0] * m; r[e] = 1; out.append((r, BOX))
                r = [0] * m; r[e] = -1; out.append((r, BOX))
        return out
    lb = [-10.0] * m; ub = [10.0] * m          # float proposal box only; the exact LP uses BOX
    for _ in range(10000):                                   # float proposal of the relevant orders
        sol = MS.float_lp(m, obj, le_rows(False), eq, lb, ub)
        assert sol is not None, "F is nonempty"
        val, order = T.best_float(sol)
        if val <= af + 1e-9:
            break
        F = MS.fwd_set(order, T.arcs)
        if F in rows:
            break
        rows.append(F)
    while True:
        st, val, y, _ = MS.exact_lp(m, obj, le_rows(True), eq)
        assert st == "optimal", "box-bounded LP over a nonempty set must be optimal"
        best, order = T.best_exact(y)
        if best <= alpha:
            assert all(abs(v) < BOX for v in y), "optimum on the box boundary: enlarge BOX"
            return val
        F = MS.fwd_set(order, T.arcs)
        assert F not in rows
        rows.append(F)


def split_vertices(U, W, Bb, rowsE, alpha, k):
    """vertices of P in coordinates (u_i for i in U, w_i for i in W), exact; i indexes the kept arcs (0..k-1).
    Bb maps each i in U & W to its bound B_i + 1 on u_i + w_i.  rowsE: order rows restricted to kept arcs."""
    p, q = alpha.numerator, alpha.denominator
    cols = [("u", i) for i in U] + [("w", i) for i in W]
    nv = len(cols); col = {c: j for j, c in enumerate(cols)}
    H = []
    for j in range(nv):                                      # u, w >= 0
        H.append([Fraction(0)] + [Fraction(1 if t == j else 0) for t in range(nv)])
    for i in sorted(set(U) & set(W)):                        # u_i + w_i <= B_i + 1 (slack on optimal duals)
        r = [Fraction(0)] * nv; r[col[("u", i)]] = Fraction(-1); r[col[("w", i)]] = Fraction(-1)
        H.append([Fraction(Bb[i])] + r)
    def yrow(R, scale):                                      # coefficients of scale * sum_{i in R} y_i
        r = [Fraction(0)] * nv
        for i in R:
            if ("u", i) in col: r[col[("u", i)]] = Fraction(scale)
            if ("w", i) in col: r[col[("w", i)]] = Fraction(-scale)
        return r
    for R in rowsE:                                          # q fwd(y) <= p
        H.append([Fraction(p)] + [-c for c in yrow(R, q)])
    H.append([Fraction(-1)] + yrow(range(k), 1))             # sum y = 1
    M = cdd.gmp.matrix_from_array(H, lin_set={len(H) - 1}, rep_type=cdd.RepType.INEQUALITY)
    cdd.gmp.matrix_canonicalize_linearity(M)
    V = cdd.gmp.copy_generators(cdd.gmp.polyhedron_from_matrix(M))
    assert not V.lin_set, "P is a polytope: no lines"
    verts = []
    for r in V.array:
        assert r[0] == 1, "P is a polytope: no rays"
        u = [Fraction(0)] * k; w = [Fraction(0)] * k
        for j, (t, i) in enumerate(cols):
            (u if t == "u" else w)[i] = Fraction(r[1 + j])
        verts.append((u, w))
    assert verts
    return verts


def face(T):
    rows = []
    alpha = MS.compute_alpha(T, True, rows)
    m = T.m
    hi = [face_lp(T, alpha, [1 if i == e else 0 for i in range(m)], rows) for e in range(m)]
    lo = [-face_lp(T, alpha, [-1 if i == e else 0 for i in range(m)], rows) for e in range(m)]
    # every optimal dual has lo_e <= y_e <= hi_e.  Arcs with hi_e <= 0 never carry a positive weight and arcs
    # with lo_e >= 0 never a negative one, so fixing those split variables to 0 keeps a face of P that still
    # contains every face of a minimal support; arcs with lo_e = hi_e = 0 are dropped.
    Eb = [e for e in range(m) if not (lo[e] == 0 and hi[e] == 0)]
    k = len(Eb); pos = {e: i for i, e in enumerate(Eb)}
    U = [i for i, e in enumerate(Eb) if hi[e] > 0]
    W = [i for i, e in enumerate(Eb) if lo[e] < 0]
    Bb = {i: max(hi[Eb[i]], -lo[Eb[i]]) + 1 for i in set(U) & set(W)}
    restrict = lambda F: tuple(sorted(pos[e] for e in F if e in pos))
    rowsE = sorted({restrict(F) for F in rows})
    rounds = 0
    while True:
        rounds += 1
        verts = split_vertices(U, W, Bb, rowsE, alpha, k)
        bad = set()
        for u, w in verts:
            y = [Fraction(0)] * m
            for i, e in enumerate(Eb):
                y[e] = u[i] - w[i]
            best, order = T.best_exact(y)
            if best > alpha:
                bad.add(restrict(MS.fwd_set(order, T.arcs)))
            else:
                assert best == alpha
        if not bad:
            break
        assert not (bad & set(rowsE)), "a vertex violates a row the enumeration was given"
        rowsE = sorted(set(rowsE) | bad)
    split = []                                               # vertices with u_e w_e = 0 everywhere
    for u, w in verts:
        if all(u[i] == 0 or w[i] == 0 for i in range(k)):
            split.append({Eb[i]: u[i] - w[i] for i in range(k) if u[i] != w[i]})
    sups = [frozenset(y) for y in split]
    minimal = sorted({S for S in sups if not any(S2 < S for S2 in sups)}, key=lambda S: (len(S), sorted(S)))
    out = []
    for S in minimal:
        pats = {}
        for y, S2 in zip(split, sups):
            if S2 == S:
                pats.setdefault(tuple(1 if y[e] > 0 else -1 for e in sorted(S)), []).append(y)
        for sg, ys in sorted(pats.items()):
            out.append({"arcs": [list(T.arcs[e]) for e in sorted(S)], "sign": list(sg),
                        "y": [str(ys[0][e]) for e in sorted(S)], "n_vertices": len(ys)})
    return alpha, out, {"rows": len(rowsE), "rounds": rounds, "n_vertices": len(verts),
                        "n_split_vertices": len(split), "kept_arcs": k, "both_signs": len(Bb)}


def main():
    src, outp, k, K = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4])
    ts = MS.read_tournaments(src)
    hk = MS.HK(len(ts[0]))
    if len(sys.argv) > 5:
        idxs = [int(x) for x in open(sys.argv[5]).read().split()]
        mine = [i for j, i in enumerate(idxs) if j % K == k]
    else:
        mine = [i for i in range(len(ts)) if i % K == k]
    t0 = time.time()
    with open(outp, "w") as fh:
        for done, idx in enumerate(mine, 1):
            t1 = time.time()
            alpha, sups, stats = face(MS.Tour(ts[idx], hk))
            fh.write(json.dumps({"idx": idx, "alpha": str(alpha), "supports": sups, **stats,
                                 "seconds": round(time.time() - t1, 2)}) + "\n"); fh.flush()
            el = time.time() - t0
            sys.stderr.write(f"{time.strftime('%H:%M:%S')} [{el:7.0f}s] worker {k}/{K} {done}/{len(mine)} "
                             f"(idx {idx}: {stats['n_vertices']} vertices, {time.time() - t1:.1f}s), "
                             f"ETA {el / done * (len(mine) - done):.0f}s\n"); sys.stderr.flush()


if __name__ == "__main__":
    main()
