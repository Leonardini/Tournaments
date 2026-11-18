#!/usr/bin/env python3
"""Theorem thm:circulant-family, the 15-vertex half: no circulant tournament on Z_15 has
alpha* = 2/3 and fails to be 3-inducible.

A circulant tournament on Z_15 is given by a connection set S containing exactly one of s, -s for
s = 1..7 (128 sets).  Multiplying S by a unit u of Z_15 gives an isomorphic tournament (x -> u x),
so it suffices to treat one set per orbit of the unit group; this script finds the 16 orbits.
For each representative it computes alpha* with alpha_fast (cutting planes: GLPK master LP, exact
maximum-acyclic-subgraph DP oracle; built from alpha_fast.c in this folder), and checks that
exactly three orbits reach alpha* = 2/3, namely those of
    {1, ..., 7}                    RT_15, locally transitive -> 3-inducible (paper's theorem),
    {1, 2, 5, 6, 7, 11, 12}        RT_5[C_3]   (blocks = cosets of {0, 5, 10})
    {1, 3, 4, 6, 7, 10, 13}        C_3[RT_5]   (blocks = cosets of {0, 3, 6, 9, 12}),
the last two being substitutions of 3-inducible tournaments, hence 3-inducible (paper's lemma).
The substitution structure is checked here directly: S minus the block subgroup H is a union of
cosets of H, and the quotient and block tournaments are the ones named.
Every other orbit has alpha* <= 0.6596, far below 2/3 = 0.6667 relative to the LP's precision.
Usage: python3 circulant15.py PATH/TO/alpha_fast      (about 40 seconds)
"""
import subprocess, sys, tempfile
from itertools import product
from math import gcd

N = 15
TWO_THIRDS_TOL = 1e-6        # alpha_fast is a float LP; the values to separate differ by > 0.007


def main(alpha_fast):
    units = [u for u in range(1, N) if gcd(u, N) == 1]
    orbit_of, reps = {}, []
    for bits in product((0, 1), repeat=7):
        S = frozenset(s if b else N - s for s, b in zip(range(1, 8), bits))
        key = min(tuple(sorted(u * s % N for s in S)) for u in units)
        if key not in orbit_of:
            orbit_of[key] = len(reps); reps.append(key)
    if len(reps) != 16:
        sys.exit(f"expected 16 unit orbits of connection sets, found {len(reps)}")
    with tempfile.NamedTemporaryFile("w", suffix=".inm", delete=False) as f:
        for S in reps:
            f.write(" ".join(str(sum(1 << u for u in range(N) if (v - u) % N in S)) for v in range(N)) + "\n")
        path = f.name
    out = subprocess.run([alpha_fast, path], capture_output=True, text=True, check=True).stdout.split("\n")
    alpha = {}
    for line in out:
        if line.strip():
            i, mas, a = line.split()
            alpha[int(i)] = float(a)
    if len(alpha) != 16:
        sys.exit("alpha_fast did not return 16 values")
    hits = sorted(reps[i] for i, a in alpha.items() if a > 2 / 3 - TWO_THIRDS_TOL)
    canon = lambda S: min(tuple(sorted(u * s % N for s in S)) for u in units)
    want = {"RT_15": {1, 2, 3, 4, 5, 6, 7}, "RT_5[C_3]": {1, 2, 5, 6, 7, 11, 12},
            "C_3[RT_5]": {1, 3, 4, 6, 7, 10, 13}}
    if sorted(canon(S) for S in want.values()) != hits:
        sys.exit(f"orbits with alpha* = 2/3 are {hits}, not the three expected")
    # substitution structure of the two non-rotational ones
    for name, S, H, q in (("RT_5[C_3]", want["RT_5[C_3]"], {0, 5, 10}, 5),
                          ("C_3[RT_5]", want["C_3[RT_5]"], {0, 3, 6, 9, 12}, 3)):
        outside = [s for s in S if s not in H]
        if not all((s + h) % N in S for s in outside for h in H):
            sys.exit(f"{name}: S minus H is not a union of cosets of H")
        quotient = sorted({s % q for s in outside})
        block = sorted(s for s in S if s in H)
        print(f"{name}: S = {sorted(S)}, blocks = cosets of {sorted(H)} with steps {block}, "
              f"quotient Z_{q} with steps {quotient}")
    others = max(a for i, a in alpha.items() if reps[i] not in hits)
    print(f"16 orbits; alpha* = 2/3 exactly for RT_15, RT_5[C_3], C_3[RT_5]; all others <= {others:.4f}")
    print("PASS")


if __name__ == "__main__":
    main(sys.argv[1])
