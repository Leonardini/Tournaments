"""Closed-form certificate candidate for HS3(RT_n) >= C(k,2), n = 2k-1: weight the balanced copy B_m (p = 2m-1) by
phi(g)/g, g = gcd(p, n).  Load at span d:  L(d) = sum_m phi(g_m)/g_m * c_{m,d},   c_{m,d} = sum_{t=1}^{m-1} (p - |pd - tn|)_+
(the exact span count of B_m).  With w = 1 / max_d L(d) the dual is feasible, and its value is
    V(k) = n * sum_m phi(g_m)/g_m * C(m,2) / max_d L(d),
which must exceed C(k,2) - 1.  Exact rational arithmetic; also prints the load profile shape.
Usage: python3 rt_totient_weights.py kmax [kmin] [--profile]"""
import sys
from fractions import Fraction as Fr
from math import gcd, comb
def phi(g):
    r, x, q = g, g, 2
    while q * q <= x:
        if x % q == 0:
            while x % q == 0: x //= q
            r -= r // q
        q += 1
    if x > 1: r -= r // x
    return r
def c(n, m, d):
    p = 2 * m - 1
    return sum(max(0, p - abs(p * d - t * n)) for t in range(1, m))
def run(k):
    n = 2 * k - 1
    wt = {m: Fr(phi(gcd(2 * m - 1, n)), gcd(2 * m - 1, n)) for m in range(2, k)}
    L = {d: sum(wt[m] * c(n, m, d) for m in wt) for d in range(1, k)}
    V = n * sum(wt[m] * comb(m, 2) for m in wt) / max(L.values())
    return V, L, wt
if __name__ == "__main__":
    a = [x for x in sys.argv[1:] if not x.startswith("--")]; kmax = int(a[0]); kmin = int(a[1]) if len(a) > 1 else 3
    fails = []; minslack = None
    for k in range(kmin, kmax + 1):
        V, L, wt = run(k); C = comb(k, 2); s = V - (C - 1)
        if s <= 0: fails.append(k)
        if minslack is None or s < minslack[0]: minslack = (s, k)
        if "--profile" in sys.argv or k % 50 == 0 or s <= 0:
            Lmax = max(L.values()); arg = [d for d in L if L[d] == Lmax]
            print(f"k={k} n={2*k-1}: V = {float(V):.4f}, C(k,2)-1 = {C-1}, slack {float(s):+.4f}; max load {float(Lmax):.4f} at d={arg[:6]}"
                  + (f"\n   load/max by d: {[round(float(L[d]/Lmax), 3) for d in L]}" if "--profile" in sys.argv else ""), flush=True)
    print(f"k = {kmin}..{kmax}: failures {fails or 'none'}; min slack {float(minslack[0]):.4f} at k={minslack[1]}")
