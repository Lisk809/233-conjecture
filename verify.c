/* ============================================================
 * 验证“质因数尾数迭代”猜想（带进度显示 + 修复死循环）
 *
 * 用法:
 *   ./verify [LIMIT] [threads]
 *     LIMIT   验证范围 2..LIMIT，默认 1000000
 *     threads 线程数，默认 1
 *
 *   例: ./verify 100000000 4
 *
 * 输出 result.txt:
 *   第一行: <min> <max> <total> <hit> <miss>
 *   之后每行: 一个未到达的起始值
 *   若失败数为 0，则只有第一行
 * ============================================================ */

#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <pthread.h>
#include <stdatomic.h>
#include <unistd.h>

typedef uint64_t u64;
typedef unsigned __int128 u128;

/* ==================== 计时 ==================== */

static double now_sec(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}

/* ==================== 算术 ==================== */

static inline u64 mulmod(u64 a, u64 b, u64 m) {
    return (u128)a * b % m;
}

static u64 powmod(u64 a, u64 b, u64 m) {
    u64 r = 1; a %= m;
    while (b) {
        if (b & 1) r = mulmod(r, a, m);
        a = mulmod(a, a, m);
        b >>= 1;
    }
    return r;
}

static inline u64 gcd_u64(u64 a, u64 b) {
    while (b) { u64 t = a % b; a = b; b = t; }
    return a;
}

/* ==================== Miller-Rabin 7 基 ==================== */

static const u64 MR_BASES[7] = {
    2ULL, 325ULL, 9375ULL, 28178ULL,
    450775ULL, 9780504ULL, 1795265022ULL
};

static int is_prime(u64 n) {
    if (n < 2) return 0;
    static const u64 small[] = {2,3,5,7,11,13,17,19,23,29,31,37};
    for (int i = 0; i < 12; i++) {
        if (n == small[i]) return 1;
        if (n % small[i] == 0) return 0;
    }
    u64 d = n - 1; int r = 0;
    while ((d & 1) == 0) { d >>= 1; r++; }
    for (int i = 0; i < 7; i++) {
        u64 a = MR_BASES[i] % n;
        if (a == 0) continue;
        u64 x = powmod(a, d, n);
        if (x == 1 || x == n - 1) continue;
        int cont = 0;
        for (int j = 1; j < r; j++) {
            x = mulmod(x, x, n);
            if (x == n - 1) { cont = 1; break; }
        }
        if (cont) continue;
        return 0;
    }
    return 1;
}

/* ==================== Brent-Pollard（带 c 参数） ==================== */

static u64 pollard_brent(u64 n, u64 c) {
    if ((n & 1) == 0) return 2;
    if (n % 3 == 0) return 3;

    u64 y = 2, g = 1, r = 1, q = 1, x = 0, ys = 0;
    const u64 batch = 128;
    const u64 MAX_R = 1ULL << 20;

    while (g == 1) {
        x = y;
        for (u64 i = 0; i < r; i++)
            y = (mulmod(y, y, n) + c) % n;

        u64 k = 0;
        while (k < r && g == 1) {
            ys = y;
            u64 lim = (r - k < batch) ? r - k : batch;
            for (u64 i = 0; i < lim; i++) {
                y = (mulmod(y, y, n) + c) % n;
                u64 diff = x > y ? x - y : y - x;
                q = mulmod(q, diff, n);
            }
            g = gcd_u64(q, n);
            k += lim;
        }

        r <<= 1;
        if (r > MAX_R) return n;   /* 放弃 */

        if (g == n) {
            do {
                ys = (mulmod(ys, ys, n) + c) % n;
                u64 diff = x > ys ? x - ys : ys - x;
                g = gcd_u64(diff, n);
            } while (g == 1);
            break;
        }
    }
    return g;
}

/* ==================== 预筛素数（<5000） ==================== */

#define N_PRE 669
static u64 pre_primes[N_PRE];
static int pre_count = 0;

static void init_pre_primes(void) {
    pre_count = 0;
    for (u64 i = 2; i < 5000 && pre_count < N_PRE; i++) {
        int p = 1;
        for (u64 j = 2; j * j <= i; j++)
            if (i % j == 0) { p = 0; break; }
        if (p) pre_primes[pre_count++] = i;
    }
}

/* ==================== 最大质因数 ==================== */

static u64 max_prime_factor(u64 n) {
    if (n <= 1) return 0;
    u64 best = 1;

    for (int i = 0; i < pre_count; i++) {
        u64 p = pre_primes[i];
        if (p * p > n) break;
        while (n % p == 0) { best = p; n /= p; }
    }
    if (n == 1) return best;
    if (is_prime(n)) return n > best ? n : best;

    u64 stack[128]; int top = 0;
    stack[top++] = n;
    while (top > 0) {
        u64 m = stack[--top];
        if (m <= 1) continue;
        if (is_prime(m)) {
            if (m > best) best = m;
            continue;
        }

        u64 c = 1;
        u64 d = pollard_brent(m, c);
        int retries = 0;
        while ((d == 1 || d == m) && retries < 100) {
            c++;
            retries++;
            d = pollard_brent(m, c);
        }
        if (d == 1 || d == m) {
            /* 极端兜底：当作质数处理，避免卡死 */
            if (m > best) best = m;
            continue;
        }
        stack[top++] = d;
        stack[top++] = m / d;
    }
    return best;
}

/* ==================== 有限缓存 ==================== */

#define CACHE_BITS 22
#define CACHE_SIZE (1u << CACHE_BITS)
#define CACHE_MASK (CACHE_SIZE - 1)
#define CACHE_MAX  (CACHE_SIZE * 3 / 4)

static u64     *cache_keys;
static uint8_t *cache_used;
static size_t   cache_count = 0;
static pthread_mutex_t cache_mtx = PTHREAD_MUTEX_INITIALIZER;

static inline size_t hash_key(u64 k) {
    k ^= k >> 33; k *= 0xff51afd7ed558ccdULL;
    k ^= k >> 33; k *= 0xc4ceb9fe1a85ec53ULL;
    k ^= k >> 33;
    return (size_t)(k & CACHE_MASK);
}

static int cache_has(u64 k) {
    size_t h = hash_key(k);
    for (size_t i = 0; i < 24; i++) {
        size_t idx = (h + i) & CACHE_MASK;
        if (!cache_used[idx]) return 0;
        if (cache_keys[idx] == k) return 1;
    }
    return 0;
}

static void cache_add(u64 k) {
    if (cache_count >= CACHE_MAX) return;
    size_t h = hash_key(k);
    for (size_t i = 0; i < 48; i++) {
        size_t idx = (h + i) & CACHE_MASK;
        if (!cache_used[idx]) {
            cache_used[idx] = 1;
            cache_keys[idx] = k;
            cache_count++;
            return;
        }
        if (cache_keys[idx] == k) return;
    }
}

/* ==================== 迭代 ==================== */

#define MAX_STEPS 1024

typedef struct { u64 n, maxP, next; } Step;

static int iterate(u64 start, Step *steps, int *out_steps, int *from_cache) {
    u64 n = start;
    int skip_first_233 = (start == 233);
    *from_cache = 0;

    for (int i = 0; i < MAX_STEPS; i++) {
        pthread_mutex_lock(&cache_mtx);
        int hit = cache_has(n);
        pthread_mutex_unlock(&cache_mtx);
        if (hit) {
            *out_steps = i;
            *from_cache = 1;
            return 1;
        }

        u64 p = max_prime_factor(n);
        if (p == 0) { *out_steps = i; return 0; }
        if (p > (UINT64_MAX - 9) / 10) { *out_steps = i; return 0; }

        u64 next = 10 * p + (p % 10);
        steps[i].n = n;
        steps[i].maxP = p;
        steps[i].next = next;

        if (p == 233) {
            if (skip_first_233) skip_first_233 = 0;
            else { *out_steps = i + 1; return 1; }
        }
        n = next;
    }
    *out_steps = MAX_STEPS;
    return 0;
}

/* ==================== 线程 ==================== */

typedef struct {
    u64 start, end;
    _Atomic u64 local_done;
    _Atomic u64 local_reached;
    _Atomic u64 local_iters;
    _Atomic u64 local_cache_hits;
    u64 *fails;
    size_t fail_count;
    size_t fail_cap;
} ThreadArg;

static void add_fail(ThreadArg *ta, u64 v) {
    if (ta->fail_count >= ta->fail_cap) {
        ta->fail_cap = ta->fail_cap ? ta->fail_cap * 2 : 64;
        ta->fails = (u64*)realloc(ta->fails, sizeof(u64) * ta->fail_cap);
        if (!ta->fails) { fprintf(stderr, "realloc fail\n"); exit(1); }
    }
    ta->fails[ta->fail_count++] = v;
}

static void *worker(void *arg) {
    ThreadArg *ta = (ThreadArg*)arg;
    Step *steps = (Step*)malloc(sizeof(Step) * MAX_STEPS);
    if (!steps) { fprintf(stderr, "steps alloc fail\n"); exit(1); }

    for (u64 i = ta->start; i < ta->end; i++) {
        int num_steps, from_cache;
        int ok = iterate(i, steps, &num_steps, &from_cache);

        if (ok) {
            atomic_fetch_add_explicit(&ta->local_reached, 1, memory_order_relaxed);
            if (from_cache)
                atomic_fetch_add_explicit(&ta->local_cache_hits, 1,
                                          memory_order_relaxed);
            pthread_mutex_lock(&cache_mtx);
            for (int j = 0; j < num_steps; j++) cache_add(steps[j].n);
            cache_add(i);
            pthread_mutex_unlock(&cache_mtx);
        } else {
            add_fail(ta, i);
        }

        atomic_fetch_add_explicit(&ta->local_iters, (u64)num_steps,
                                  memory_order_relaxed);
        atomic_fetch_add_explicit(&ta->local_done, 1, memory_order_relaxed);
    }
    free(steps);
    return NULL;
}

/* ==================== 进度显示 ==================== */

static void fmt_time(double sec, char *buf, size_t n) {
    int h = (int)(sec / 3600);
    int m = (int)((sec - h * 3600) / 60);
    double s = sec - h * 3600 - m * 60;
    if (h > 0)      snprintf(buf, n, "%dh%02dm%02.0fs", h, m, s);
    else if (m > 0) snprintf(buf, n, "%dm%02.0fs", m, s);
    else            snprintf(buf, n, "%.1fs", s);
}

static void print_progress(u64 done, u64 total, u64 reached,
                          u64 iters, u64 cache_hits,
                          double elapsed) {
    double pct = total ? 100.0 * (double)done / (double)total : 100.0;
    double speed = (elapsed > 0.05) ? (double)done / elapsed : 0.0;
    double remain = (speed > 0.0) ? (double)(total - done) / speed : 0.0;
    double cache_pct = (iters > 0) ? 100.0 * (double)cache_hits / (double)iters : 0.0;

    char eta[32];
    fmt_time(remain, eta, sizeof(eta));

    const int BAR_W = 30;
    int filled = (int)(BAR_W * pct / 100.0);
    if (filled > BAR_W) filled = BAR_W;
    char bar[64];
    for (int i = 0; i < BAR_W; i++)
        bar[i] = (i < filled) ? '=' : ((i == filled) ? '>' : ' ');
    bar[BAR_W] = '\0';

    printf("\r[%s] %6.2f%%  %llu/%llu  %.0f/s  ETA %s  cache %.1f%%   ",
           bar, pct,
           (unsigned long long)done,
           (unsigned long long)total,
           speed, eta, cache_pct);
    fflush(stdout);
    (void)reached;
}

/* ==================== main ==================== */

int main(int argc, char **argv) {
    u64 LIMIT = 1000000ULL;
    int threads = 1;

    if (argc >= 2) LIMIT = strtoull(argv[1], NULL, 10);
    if (argc >= 3) threads = atoi(argv[2]);
    if (threads < 1) threads = 1;
    if (LIMIT < 2) { fprintf(stderr, "LIMIT must >= 2\n"); return 1; }

    init_pre_primes();

    cache_keys = (u64*)calloc(CACHE_SIZE, sizeof(u64));
    cache_used = (uint8_t*)calloc(CACHE_SIZE, 1);
    if (!cache_keys || !cache_used) {
        fprintf(stderr, "cache alloc fail\n"); return 1;
    }

    pthread_t *tids = (pthread_t*)malloc(sizeof(pthread_t) * threads);
    ThreadArg *args = (ThreadArg*)calloc(threads, sizeof(ThreadArg));
    if (!tids || !args) { fprintf(stderr, "alloc fail\n"); return 1; }

    u64 total = LIMIT - 1;
    u64 per = total / (u64)threads;
    u64 rem = total % (u64)threads;
    u64 cur = 2;

    for (int t = 0; t < threads; t++) {
        u64 chunk = per + ((u64)t < rem ? 1 : 0);
        args[t].start = cur;
        args[t].end = cur + chunk;
        args[t].fails = NULL;
        args[t].fail_count = 0;
        args[t].fail_cap = 0;
        cur += chunk;
    }

    printf("===============================================================\n");
    printf("  验证“质因数尾数迭代”猜想\n");
    printf("  范围:  2 .. %-20llu  (共 %llu 个)\n",
           (unsigned long long)LIMIT, (unsigned long long)total);
    printf("  线程:  %d\n", threads);
    printf("  缓存:  %u 槽 (约 %.0f MB)\n",
           CACHE_SIZE, CACHE_SIZE * 9.0 / 1024.0 / 1024.0);
    printf("===============================================================\n\n");

    double t_start = now_sec();

    for (int t = 0; t < threads; t++)
        pthread_create(&tids[t], NULL, worker, &args[t]);

    while (1) {
        u64 done = 0, reached = 0, iters = 0, chits = 0;
        for (int t = 0; t < threads; t++) {
            done    += atomic_load_explicit(&args[t].local_done,    memory_order_relaxed);
            reached += atomic_load_explicit(&args[t].local_reached, memory_order_relaxed);
            iters   += atomic_load_explicit(&args[t].local_iters,   memory_order_relaxed);
            chits   += atomic_load_explicit(&args[t].local_cache_hits, memory_order_relaxed);
        }
        double elapsed = now_sec() - t_start;
        print_progress(done, total, reached, iters, chits, elapsed);
        if (done >= total) break;
        usleep(200000);
    }

    for (int t = 0; t < threads; t++)
        pthread_join(tids[t], NULL);

    double elapsed = now_sec() - t_start;
    printf("\n\n");

    u64 reached = 0;
    size_t total_fail = 0;
    u64 total_iters = 0, total_cache_hits = 0;
    for (int t = 0; t < threads; t++) {
        reached += atomic_load_explicit(&args[t].local_reached, memory_order_relaxed);
        total_fail += args[t].fail_count;
        total_iters += atomic_load_explicit(&args[t].local_iters, memory_order_relaxed);
        total_cache_hits += atomic_load_explicit(&args[t].local_cache_hits, memory_order_relaxed);
    }

    FILE *out = fopen("result.txt", "w");
    if (!out) { perror("fopen"); return 1; }

    fprintf(out, "2 %llu %llu %llu %zu\n",
        (unsigned long long)LIMIT,
        (unsigned long long)total,
        (unsigned long long)reached,
        total_fail);

    for (int t = 0; t < threads; t++)
        for (size_t i = 0; i < args[t].fail_count; i++)
            fprintf(out, "%llu\n", (unsigned long long)args[t].fails[i]);
    fclose(out);

    char tb[32];
    fmt_time(elapsed, tb, sizeof(tb));

    printf("==================== 结果 ====================\n");
    printf("  用时:       %s (%.3f 秒)\n", tb, elapsed);
    printf("  总数:       %llu\n", (unsigned long long)total);
    printf("  到达 233:   %llu  (%.4f%%)\n",
           (unsigned long long)reached,
           total ? 100.0 * (double)reached / (double)total : 0.0);
    printf("  未到达:     %zu\n", total_fail);
    printf("  平均速度:   %.0f 个/秒\n",
           elapsed > 0.05 ? (double)total / elapsed : 0.0);
    printf("  总迭代步数: %llu\n", (unsigned long long)total_iters);
    if (total_iters > 0)
        printf("  缓存命中步: %llu  (%.2f%%)\n",
               (unsigned long long)total_cache_hits,
               100.0 * (double)total_cache_hits / (double)total_iters);
    printf("  缓存条目:   %zu / %d\n", cache_count, CACHE_MAX);
    printf("==============================================\n");

    if (total_fail > 0) {
        printf("\n失败值（前 30 个）: ");
        int shown = 0;
        for (int t = 0; t < threads && shown < 30; t++) {
            for (size_t i = 0; i < args[t].fail_count && shown < 30; i++, shown++)
                printf("%llu%s", (unsigned long long)args[t].fails[i],
                       (shown + 1 < 30) ? ", " : "");
        }
        if (total_fail > 30) printf(" ...");
        printf("\n");
    }

    printf("\n结果已写入 result.txt\n");

    for (int t = 0; t < threads; t++) free(args[t].fails);
    free(tids); free(args);
    free(cache_keys); free(cache_used);
    return 0;
}