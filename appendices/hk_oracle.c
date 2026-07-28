/* hk_oracle.c — weighted-MAS Held-Karp oracle for n <= 16, double weights.
 * best_order(W, n, order_out) returns max over linear orders of sum of W[a][b]
 * over pairs a before b; reconstructs an argmax order.  For alpha* screens:
 * W[a][b] = y_arc for arcs (a,b), 0 otherwise. */
#include <string.h>

double hk_best(const double *W, int n, int *order_out) {
    static double f[1 << 16];
    static unsigned char par[1 << 16];
    int FULL = (1 << n) - 1;
    for (int S = 1; S <= FULL; S++) f[S] = -1e300;
    f[0] = 0.0;
    double rowsum[16];
    for (int x = 0; x < n; x++) {
        rowsum[x] = 0.0;
        for (int b = 0; b < n; b++) rowsum[x] += W[x * n + b];
    }
    for (int S = 0; S < FULL; S++) {
        if (f[S] < -1e299) continue;
        double fS = f[S];
        for (int x = 0; x < n; x++) {
            if (S & (1 << x)) continue;
            /* gain of appending x after set S: arcs x->b for b not in S+x */
            double g = rowsum[x];
            int z = S | (1 << x);
            for (int b = 0; b < n; b++)
                if ((z >> b) & 1) g -= W[x * n + b];
            int S2 = S | (1 << x);
            double val = fS + g;
            if (val > f[S2] + 1e-15) { f[S2] = val; par[S2] = (unsigned char)x; }
        }
    }
    int S = FULL;
    for (int p = n - 1; p >= 0; p--) { order_out[p] = par[S]; S ^= 1 << par[S]; }
    return f[FULL];
}
