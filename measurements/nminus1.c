/* Item 3 prototype: B-smooth part F of n-1 for the primes n of [10^f, 10^f + count).
 * n - 1 values are sieved by the primes p <= B (prime powers divided out repeatedly); the
 * primes n are found with BPSW (statistics only). Prints: floor count B primes
 * frac(F >= n^1/2) frac(F >= n^1/3) median(log F / log n) seconds
 * Build: gcc -O3 -march=native -I"$PRIMEATLAS_DIR/prime_sieve" nminus1.c -o nminus1 -lprimesieve -lpthread -lm
 */
#include <stdio.h>
#include <time.h>
#include "prime_sieve_engine_pt1.c"   /* from PrimeAtlas prime_sieve/, see README */

static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + t.tv_nsec * 1e-9; }
static int cmpd(const void *a, const void *b) { double x = *(const double *)a, y = *(const double *)b; return x < y ? -1 : x > y; }
static double lg(u128 x) { return log((double)(x >> 64) * 18446744073709551616.0 + (double)(u64)x); }

int main(int argc, char **argv) {
    int floor = atoi(argv[1]);
    u64 count = (u64)strtod(argv[2], NULL), b = (u64)strtod(argv[3], NULL);
    double t0 = now();
    u128 lo = 1; for (int i = 0; i < floor; i++) lo *= 10;
    u128 *r = malloc(sizeof *r * count);           /* r[i] = cofactor of (lo + i) - 1 */
    for (u64 i = 0; i < count; i++) r[i] = lo + i - 1;
    size_t np = 0;
    u32 *p = (u32 *)primesieve_generate_primes(2, b, &np, UINT32_PRIMES);
    for (size_t k = 0; k < np; k++) {
        u64 q = p[k];
        u64 off = (u64)((q - (lo - 1) % q) % q);   /* first i with q | lo - 1 + i */
        for (u64 i = off; i < count; i += q)
            do r[i] /= q; while (r[i] % q == 0);
    }
    u64 primes = 0, half = 0, third = 0;
    double *ratio = malloc(sizeof(double) * count);
    for (u64 i = 1; i < count; i += 2) {
        u128 n = lo + i;
        if (!is_prime_bpsw(n)) continue;
        u128 f = (n - 1) / r[i];
        double ln = lg(n), lf = lg(f);
        ratio[primes++] = lf / ln;
        half += lf >= ln / 2; third += lf >= ln / 3;
    }
    qsort(ratio, primes, sizeof(double), cmpd);
    printf("%d %.0e %llu %llu %.5f %.5f %.4f %.1f\n", floor, (double)count, (unsigned long long)b,
           (unsigned long long)primes, (double)half / primes, (double)third / primes,
           ratio[primes / 2], now() - t0);
    return 0;
}
