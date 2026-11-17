"""HS3(RT_n) = C(k,2) for n = 2k-1 (RT_n: i -> i+1..i+k-1 mod n), by strong induction on k, with an EXACT rational
LP certificate per k.  (FAS(RT_n) <= C(k,2) from the natural order, so only HS3 >= C(k,2) needs proof.)

For m = 2..k-1 let B_m be the balanced copy of RT_{2m-1} in RT_n: vertices v_j = floor(j n / p), p = 2m-1.  It is a
genuine RT_{2m-1}: a window of m-1 gaps spans <= ceil((m-1)n/p) <= k-1 and a window of m gaps >= floor(mn/p) >= k.
Its arcs v_j -> v_{j+t} (t = 1..m-1) have span floor(tn/p) or floor(tn/p)+1, the latter exactly (tn mod p) times.
By induction every hitting set H uses >= C(m,2) arcs of each rotation of B_m; summing over the n rotations gives
      sum_d c_{m,d} y_d >= n C(m,2)      (y_d = # arcs of H of span d, c_{m,d} = # arcs of B_m of span d).
A dual certificate pi_m, sigma_d >= 0 with  sum_m pi_m c_{m,d} - sigma_d <= 1 (all d)  and value
sum_m pi_m n C(m,2) - n sum_d sigma_d > C(k,2) - 1  then gives |H| > C(k,2) - 1, so |H| >= C(k,2).
The certificate comes from Gurobi (one thread) and is verified in exact rational arithmetic.
Usage: python3 rt_hs3_certificate.py kmax [kmin] [--show]"""
import sys, os, collections
from fractions import Fraction as Fr
from math import comb
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gurobipy as gp
from hs3 import _env

def balanced_spans(n, m):
    p = 2 * m - 1; v = [j * n // p for j in range(p)]
    return [(v[(i + t) % p] - v[i]) % n for i in range(p) for t in range(1, m)]

def certificate(k):
    n = 2 * k - 1
    rows = {m: collections.Counter(balanced_spans(n, m)) for m in range(2, k)}
    for m, c in rows.items():                          # B_m is RT_{2m-1}, and the span counts match the formula
        p = 2 * m - 1
        f = collections.Counter()
        for t in range(1, m): f[t * n // p] += p - t * n % p; f[t * n // p + 1] += t * n % p
        assert +c == +f and max(c) <= k - 1
    M = gp.Model(env=_env()); M.Params.Threads = 1
    y = {d: M.addVar(lb=0, ub=n) for d in range(1, k)}
    cons = {m: M.addConstr(gp.quicksum(a * y[d] for d, a in r.items()) >= n * comb(m, 2)) for m, r in rows.items()}
    M.setObjective(gp.quicksum(y.values())); M.optimize()
    pi = {m: Fr(max(c.Pi, 0)).limit_denominator(10 ** 6) for m, c in cons.items()}
    sig = {d: Fr(max(-v.RC, 0)).limit_denominator(10 ** 6) for d, v in y.items()}
    worst = max(sum(pi[m] * rows[m][d] for m in rows) - sig[d] for d in y)
    if worst > 1: pi = {m: p / worst for m, p in pi.items()}; sig = {d: s / worst for d, s in sig.items()}
    assert all(sum(pi[m] * rows[m][d] for m in rows) - sig[d] <= 1 for d in y)          # exact dual feasibility
    val = sum(pi[m] * n * comb(m, 2) for m in rows) - n * sum(sig.values())
    return val, pi, sig

if __name__ == "__main__":
    show = "--show" in sys.argv; a = [x for x in sys.argv[1:] if not x.startswith("--")]
    kmax = int(a[0]); kmin = int(a[1]) if len(a) > 1 else 3; fails = []
    for k in range(kmin, kmax + 1):
        n = 2 * k - 1; val, pi, sig = certificate(k); ok = val > comb(k, 2) - 1
        if not ok: fails.append(k)
        if show or not ok or k % 25 == 0:
            print(f"k={k} n={n}: certificate value {val} = {float(val):.4f} > C(k,2)-1 = {comb(k, 2) - 1}: {ok}"
                  + (f"\n   n*pi_m (m=2..k-1): {[str(pi[m] * n) for m in sorted(pi)]}"
                     + (f"; sigma {dict((d, str(s)) for d, s in sig.items() if s)}" if any(sig.values()) else "") if show else ""),
                  flush=True)
    print(f"k = {kmin}..{kmax} (n = {2*kmin-1}..{2*kmax-1}): HS3(RT_n) >= C(k,2) certified exactly; failures: {fails or 'none'}")
