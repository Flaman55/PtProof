/* pt1 deterministic research bench. pt1's partial sieve to B, survivors decided by
 *   pss   pss_decide (pseudosquares proof + square/cube rejection)
 *   pssnc pss_prove only
 *   bpsw  BPSW (pt1.1 P)
 *   none  sieve only: every survivor counted as "prime" -> survivors
 * Usage: ./pt1det_bench floor size B mode threads   (B = 0: isqrt(isqrt(top)))
 * Prints: floor size B mode n_bases seconds primes maxrss_MB sqcube_ns
 * Build: gcc -O3 -march=native -I"$PRIMEATLAS_DIR/prime_sieve" pt1det_bench.c -o pt1det_bench -lprimesieve -lpthread -lm
 */
#include <stdio.h>
#include <time.h>
#include <sys/resource.h>
#include "prime_sieve_engine_pt1.c"   /* from PrimeAtlas prime_sieve/, see README */

static double now(void) { struct timespec t; clock_gettime(CLOCK_MONOTONIC, &t); return t.tv_sec + t.tv_nsec * 1e-9; }
static int t_pss(u128 n, const void *a) { return pss_decide(n, *(const int *)a); }
static int t_pssnc(u128 n, const void *a) { return pss_prove(n, *(const int *)a); }
static int t_bpsw(u128 n, const void *a) { (void)a; return is_prime_bpsw(n); }
static int t_none(u128 n, const void *a) { (void)n; (void)a; return 1; }

static u128 isqrt128(u128 n) {
    u128 r = (u128)sqrtl((long double)n);
    while (r * r > n) r--;
    while ((r + 1) * (r + 1) <= n) r++;
    return r;
}

int main(int argc, char **argv) {
    if (argc < 6) return 1;
    int floor = atoi(argv[1]);
    u128 size = (u128)strtod(argv[2], NULL);
    u64 b = (u64)strtod(argv[3], NULL);
    const char *mode = argv[4];
    u64 threads = strtoull(argv[5], NULL, 10);
    u128 lo = 1; for (int i = 0; i < floor; i++) lo *= 10;
    u128 hi = lo + size, top = hi - 1;
    if (!b) b = (u64)isqrt128(isqrt128(top));
    u64 lim = (u64)isqrt128(lo); if (b > lim) b = lim;
    if (b > 0xffffffffull) b = 0xffffffffull;
    pt_test_fn fn = !strcmp(mode, "pss") ? t_pss : !strcmp(mode, "pssnc") ? t_pssnc :
                    !strcmp(mode, "bpsw") ? t_bpsw : t_none;
    int n_bases = pss_bases(top, b);
    if ((fn == t_pss || fn == t_pssnc) && !n_bases) {
        printf("%d %.0e %llu %s 0 nobases\n", floor, (double)size, (unsigned long long)b, mode);
        return 0;
    }
    double t0 = now();
    void *ctx = pt_ctx_new(b);
    u64 chunk = 4096 * 1024, slab = 2 * chunk * threads * 4;   /* pt1 defaults */
    unsigned char *bits = malloc(slab / 2 / 8 + 16);
    volatile u64 done = 0;
    u64 primes = 0;
    for (u128 s = lo | 1; s < hi; s += slab) {
        u128 e = s + slab < hi ? s + slab : hi;
        u64 n_odd = (u64)((e - s + 1) / 2);
        if (pt_sieve_odd(ctx, (u64)(s >> 64), (u64)s, n_odd, fn, &n_bases, threads, chunk,
                         bits, &done)) { printf("error\n"); return 1; }
        u64 comp = 0;
        for (u64 i = 0; i < n_odd / 8; i++) comp += __builtin_popcount(bits[i]);
        for (u64 i = n_odd / 8 * 8; i < n_odd; i++) comp += (bits[i / 8] >> (i % 8)) & 1;
        primes += n_odd - comp;
    }
    double secs = now() - t0;
    /* single-thread cost of is_square + is_cube near the floor */
    double t1 = now(); volatile int acc = 0;
    for (u64 i = 0; i < 2000000; i++) { u128 n = lo + 2 * (u128)i * 7919 + 1; acc += is_square(n) | is_cube(n); }
    double sq_ns = (now() - t1) / 2e6 * 1e9;
    struct rusage ru; getrusage(RUSAGE_SELF, &ru);
    printf("%d %.0e %llu %s %d %.3f %llu %.0f %.1f\n", floor, (double)size, (unsigned long long)b,
           mode, n_bases, secs, (unsigned long long)primes, ru.ru_maxrss / 1024.0, sq_ns);
    return 0;
}
